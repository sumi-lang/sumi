//! The single-file Sumi command-line driver.

use std::ffi::OsString;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::ExitCode;

use sumi_eval::{Program, Value};
use sumi_frontend::{FileId, Severity, parse_source};
use sumi_hir::Analysis;
use sumi_text::{LineIndex, TextSize};

const USAGE: &str = "usage: sumi check <file>
       sumi run <file>
       sumi fmt [--check] <file>...
       sumi fmt -

  check <file>      report syntax and scalar semantic diagnostics
  run <file>        check, then run `fn main()` and print its value
  fmt <file>...     rewrite each file in canonical layout
  fmt --check       write nothing; list the files that would change
  fmt -             format standard input to standard output
  -h, --help        show this help

Diagnostics go to stderr; clean input produces no output. Running prints
main's value to stdout, or nothing for unit; a trap, such as a division by
zero, is reported like a diagnostic. Formatting keeps every token and
comment, leaves what the parser could not parse as written, and never
changes the parse.
Locations use one-based lines and UTF-8 byte columns.
Exit status: 0 = no errors, 1 = source errors, a trap, or files that would
change, 2 = usage or input errors.";

fn main() -> ExitCode {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let result = match args.as_slice() {
        [help] if help == "--help" || help == "-h" => {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        [command, help]
            if (command == "check" || command == "run") && (help == "--help" || help == "-h") =>
        {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        [command, file] if command == "check" => check(Path::new(file)),
        [command, file] if command == "run" => run(Path::new(file)),
        [command, rest @ ..] if command == "fmt" && !rest.is_empty() => fmt(rest),
        _ => Err(USAGE.to_owned()),
    };
    match result {
        Ok(code) => code,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(2)
        }
    }
}

/// Read `path` as a source file, refusing one past the coordinate space.
fn read_source(path: &Path) -> Result<String, String> {
    let input_error = |error| format!("{}: error[cli/input]: {error}", path.display());
    let mut file = fs::File::open(path).map_err(input_error)?;
    let source_len = file.metadata().map_err(input_error)?.len();
    if source_len > u64::from(u32::MAX) {
        return Err(format!(
            "{}: error[cli/source-too-large]: source is {source_len} bytes but the maximum is {} bytes",
            path.display(),
            u32::MAX,
        ));
    }
    let mut source = String::new();
    file.read_to_string(&mut source).map_err(input_error)?;
    Ok(source)
}

/// `path:line:col: ` for a byte offset of `source`.
fn locate(path: &Path, lines: &LineIndex, offset: TextSize) -> String {
    let position = lines.line_col(offset);
    format!(
        "{}:{}:{}: ",
        path.display(),
        position.line + 1,
        u64::from(position.col) + 1
    )
}

/// Parse and check `path`, reporting every diagnostic; the analysis comes
/// back with whether any was an error.
fn analyze(path: &Path) -> Result<(Analysis, bool), String> {
    let source = read_source(path)?;
    let parsed = parse_source(FileId::new(0), source.into_boxed_str())
        .map_err(|error| format!("{}: error[cli/source-too-large]: {error}", path.display()))?;
    let analysis = sumi_hir::analyze(parsed);
    let lines = LineIndex::new(analysis.parsed().source());
    let mut diagnostics = analysis.parsed().diagnostics().to_vec();
    diagnostics.extend_from_slice(analysis.diagnostics());
    // Stable ordering: syntax first at an equal position, then emission order.
    diagnostics.sort_by_key(|d| d.primary.location.start());
    let mut has_errors = false;
    for diagnostic in &diagnostics {
        has_errors |= diagnostic.severity == Severity::Error;
        eprintln!(
            "{}{}[{}]: {}",
            locate(path, &lines, diagnostic.primary.location.start()),
            diagnostic.severity.as_str(),
            diagnostic.code,
            diagnostic.message,
        );
    }
    Ok((analysis, has_errors))
}

fn check(path: &Path) -> Result<ExitCode, String> {
    let (_, has_errors) = analyze(path)?;
    Ok(if has_errors {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}

/// Check, then run `fn main()`: its value goes to stdout unless unit, and a
/// trap is reported at the operation that trapped. A file without a
/// parameterless `main` cannot be run and is an input error.
fn run(path: &Path) -> Result<ExitCode, String> {
    let (analysis, has_errors) = analyze(path)?;
    if has_errors {
        return Ok(ExitCode::FAILURE);
    }
    let program = Program::new(&analysis).expect("a file without errors is valid");
    let Some(main) = program.function_named("main") else {
        return Err(format!(
            "{}: error[cli/no-main]: nothing to run; the file declares no `fn main()`",
            path.display()
        ));
    };
    let lines = LineIndex::new(analysis.parsed().source());
    if !program.signature(main).params.is_empty() {
        return Err(format!(
            "{}error[cli/main-parameters]: `main` takes arguments; `sumi run` passes none",
            locate(
                path,
                &lines,
                program.function(main).origin().range().start()
            ),
        ));
    }
    match program.evaluate(main, &[]) {
        Ok(Value::Unit) => Ok(ExitCode::SUCCESS),
        Ok(value) => {
            println!("{value}");
            Ok(ExitCode::SUCCESS)
        }
        Err(trap) => {
            eprintln!(
                "{}error[{}]: {}",
                locate(path, &lines, trap.origin.range().start()),
                trap.kind.code(),
                trap
            );
            Ok(ExitCode::FAILURE)
        }
    }
}

/// Format each file in place, or list the files `--check` would change, or
/// filter standard input. A file the parser recovered in is still
/// formatted where it is sound; a defect leaves the file untouched and is
/// an input error, since it is a formatter bug.
fn fmt(args: &[OsString]) -> Result<ExitCode, String> {
    let check_only = args[0] == "--check";
    let paths = if check_only { &args[1..] } else { args };
    if paths.is_empty() {
        return Err(USAGE.to_owned());
    }
    if paths == ["-"] {
        let mut source = String::new();
        std::io::stdin()
            .read_to_string(&mut source)
            .map_err(|error| format!("<stdin>: error[cli/input]: {error}"))?;
        let formatted = format_source(Path::new("<stdin>"), &source)?;
        print!("{formatted}");
        return Ok(ExitCode::SUCCESS);
    }
    let mut would_change = false;
    for path in paths {
        let path = Path::new(path);
        let source = read_source(path)?;
        let formatted = format_source(path, &source)?;
        if formatted == source {
            continue;
        }
        would_change = true;
        if check_only {
            println!("{}", path.display());
        } else {
            fs::write(path, formatted)
                .map_err(|error| format!("{}: error[cli/input]: {error}", path.display()))?;
        }
    }
    Ok(if check_only && would_change {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}

fn format_source(path: &Path, source: &str) -> Result<String, String> {
    let parsed = parse_source(FileId::new(0), source.into())
        .map_err(|error| format!("{}: error[cli/source-too-large]: {error}", path.display()))?;
    let formatted = sumi_format::format(source, parsed.lexed(), parsed.parse())
        .map_err(|defect| format!("{}: error[cli/format-defect]: {defect}", path.display()))?;
    Ok(formatted.text)
}
