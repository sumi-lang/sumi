//! The single-file Sumi command-line driver.

use std::ffi::OsString;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::ExitCode;

use sumi_frontend::{FileId, Severity, parse_source};
use sumi_text::LineIndex;

const USAGE: &str = "usage: sumi check <file>
       sumi fmt [--check] <file>...
       sumi fmt -

  check <file>      report syntax and scalar semantic diagnostics
  fmt <file>...     rewrite each file in canonical layout
  fmt --check       write nothing; list the files that would change
  fmt -             format standard input to standard output
  -h, --help        show this help

Diagnostics go to stderr; clean input produces no output. Formatting keeps
every token and comment, leaves what the parser could not parse as written,
and never changes the parse.
Locations use one-based lines and UTF-8 byte columns.
Exit status: 0 = no errors, 1 = source errors or files that would change,
2 = usage or input errors.";

fn main() -> ExitCode {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let result = match args.as_slice() {
        [help] if help == "--help" || help == "-h" => {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        [command, help] if command == "check" && (help == "--help" || help == "-h") => {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        [command, file] if command == "check" => check(Path::new(file)),
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

fn check(path: &Path) -> Result<ExitCode, String> {
    let source = read_source(path)?;
    let parsed = parse_source(FileId::new(0), source.into_boxed_str())
        .map_err(|error| format!("{}: error[cli/source-too-large]: {error}", path.display()))?;
    let lines = LineIndex::new(parsed.source());
    let mut diagnostics = parsed.diagnostics().to_vec();
    diagnostics.extend_from_slice(sumi_hir::analyze(parsed).diagnostics());
    // Stable ordering: syntax first at an equal position, then emission order.
    diagnostics.sort_by_key(|d| d.primary.location.start());
    let mut has_errors = false;
    for diagnostic in &diagnostics {
        let position = lines.line_col(diagnostic.primary.location.start());
        has_errors |= diagnostic.severity == Severity::Error;
        eprintln!(
            "{}:{}:{}: {}[{}]: {}",
            path.display(),
            position.line + 1,
            u64::from(position.col) + 1,
            diagnostic.severity.as_str(),
            diagnostic.code,
            diagnostic.message,
        );
    }
    Ok(if has_errors {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
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
