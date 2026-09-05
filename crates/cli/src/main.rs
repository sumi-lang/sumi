//! The single-file Sumi command-line driver.

use std::ffi::OsString;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::ExitCode;

use sumi_frontend::{FileId, Severity, parse_source};
use sumi_text::LineIndex;

const USAGE: &str = "usage: sumi diagnose <file>

  diagnose <file>   report syntax diagnostics for one UTF-8 source file
  -h, --help        show this help

This command does not perform name resolution or type checking.
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
        [command, help] if command == "diagnose" && (help == "--help" || help == "-h") => {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        [command, file] if command == "diagnose" => diagnose(Path::new(file)),
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

fn diagnose(path: &Path) -> Result<ExitCode, String> {
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
    let mut has_errors = false;
    for diagnostic in parsed.diagnostics() {
        let position = lines.line_col(diagnostic.primary.location.start());
        let severity = match diagnostic.severity {
            Severity::Error => {
                has_errors = true;
                "error"
            }
            Severity::Warning => "warning",
            Severity::Info => "info",
            Severity::Hint => "hint",
        };
        eprintln!(
            "{}:{}:{}: {}[{}/{}]: {}",
            path.display(),
            position.line + 1,
            u64::from(position.col) + 1,
            severity,
            diagnostic.code.group().as_str(),
            diagnostic.code.name(),
            diagnostic.message,
        );
    }
    Ok(if has_errors {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    })
}
