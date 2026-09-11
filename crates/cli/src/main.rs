//! The single-file Sumi command-line driver.

use std::ffi::OsString;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::ExitCode;

use sumi_frontend::{FileId, Severity, parse_source};
use sumi_text::LineIndex;

const USAGE: &str = "usage: sumi check <file>

  check <file>      report syntax and scalar semantic diagnostics
  -h, --help        show this help

Diagnostics go to stderr; clean input produces no output.
Locations use one-based lines and UTF-8 byte columns.
Exit status: 0 = no errors, 1 = source errors, 2 = usage or input errors.";

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

fn check(path: &Path) -> Result<ExitCode, String> {
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
