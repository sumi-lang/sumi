use std::fs;
use std::process::{Command, Output};

fn sumi() -> Command {
    Command::new(env!("CARGO_BIN_EXE_sumi"))
}

fn check(source: &[u8]) -> (tempfile::TempDir, Output) {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("case.sumi"), source).unwrap();
    let output = sumi()
        .current_dir(dir.path())
        .args(["check", "case.sumi"])
        .output()
        .unwrap();
    assert_eq!(fs::read(dir.path().join("case.sumi")).unwrap(), source);
    (dir, output)
}

#[test]
fn check_is_silent_on_success_and_never_modifies_source() {
    for source in [
        "",
        "fn answer() -> int = twice(21)\nfn twice(x: int) -> int = x * 2\n",
    ] {
        let (_dir, output) = check(source.as_bytes());
        assert_eq!(output.status.code(), Some(0));
        assert!(output.stdout.is_empty());
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn source_errors_have_locations_codes_and_failure_status() {
    for (source, expected) in [
        (
            "fn f() {\r\n    €\r\n}\r\n",
            "case.sumi:2:5: error[syntax/unknown-character]:",
        ),
        (
            "fn f() { \"é\" € }",
            "case.sumi:1:15: error[syntax/unknown-character]:",
        ),
        (
            "fn f(",
            "case.sumi:1:6: error[syntax/expected-token]: expected `)`",
        ),
    ] {
        let (_dir, output) = check(source.as_bytes());
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains(expected), "{stderr}");
    }
}

#[test]
fn diagnostic_output_is_one_plain_line() {
    let (_dir, output) = check(b"fn f() -> int = true");
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        "case.sumi:1:17: error[semantic/type-mismatch]: expected int, found bool\n"
    );
}

#[test]
#[cfg(target_os = "linux")]
fn oversized_file_is_rejected_before_reading() {
    let dir = tempfile::tempdir().unwrap();
    let file = fs::File::create(dir.path().join("large.sumi")).unwrap();
    file.set_len(u64::from(u32::MAX) + 1).unwrap();
    let output = sumi()
        .current_dir(dir.path())
        .args(["check", "large.sumi"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        "large.sumi: error[cli/source-too-large]: source is 4294967296 bytes but the maximum is 4294967295 bytes\n"
    );
}

#[test]
fn help_and_invalid_invocations() {
    for args in [
        vec!["--help"],
        vec!["-h"],
        vec!["check", "--help"],
        vec!["check", "-h"],
    ] {
        let output = sumi().args(args).output().unwrap();
        assert_eq!(output.status.code(), Some(0));
        assert!(String::from_utf8(output.stdout).unwrap().contains("usage:"));
        assert!(output.stderr.is_empty());
    }
    for args in [
        vec![],
        vec!["unknown"],
        vec!["unknown", "case.sumi"],
        vec!["check"],
        vec!["check", "a", "b"],
    ] {
        let output = sumi().args(args).output().unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.starts_with("usage: sumi check <file>\n"));
    }
}

#[test]
fn input_errors_are_distinct_from_source_errors() {
    let (dir, output) = check(&[0xff]);
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .starts_with("case.sumi: error[cli/input]: ")
    );
    let output = sumi()
        .current_dir(dir.path())
        .args(["check", "missing.sumi"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .starts_with("missing.sumi: error[cli/input]: ")
    );
}

#[test]
fn check_reports_semantics_and_syntax_in_source_order() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("case.sumi");
    let source = "fn cafe() -> int = absent\nfn bad() -> int = 01\nfn later() -> int = true\n";
    fs::write(&path, source).unwrap();
    let run = || {
        sumi()
            .current_dir(dir.path())
            .args(["check", "case.sumi"])
            .output()
            .unwrap()
    };
    let output = run();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert_eq!(output.stderr, run().stderr);
    let stderr = String::from_utf8(output.stderr).unwrap();
    let lines: Vec<_> = stderr.lines().collect();
    assert_eq!(lines.len(), 3, "{stderr}");
    assert_eq!(
        lines[0],
        "case.sumi:1:20: error[semantic/unknown-name]: unknown name `absent`"
    );
    assert!(lines[1].contains("error[syntax/"), "{stderr}");
    assert!(
        lines[2].contains("error[semantic/type-mismatch]"),
        "{stderr}"
    );
    assert_eq!(fs::read_to_string(path).unwrap(), source);
}
