use std::fs;
use std::process::{Command, Output};

fn sumi() -> Command {
    Command::new(env!("CARGO_BIN_EXE_sumi"))
}

fn diagnose(source: &[u8]) -> (tempfile::TempDir, Output) {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("case.sumi"), source).unwrap();
    let output = sumi()
        .current_dir(dir.path())
        .args(["diagnose", "case.sumi"])
        .output()
        .unwrap();
    assert_eq!(fs::read(dir.path().join("case.sumi")).unwrap(), source);
    (dir, output)
}

#[test]
fn clean_syntax_is_silent_and_does_not_check_names() {
    for source in [b"".as_slice(), b"fn f() = unknown\n"] {
        let (_dir, output) = diagnose(source);
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
        let (_dir, output) = diagnose(source.as_bytes());
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains(expected), "{stderr}");
    }
}

#[test]
fn diagnostic_output_is_one_plain_line() {
    let (_dir, output) = diagnose(b"fn f() { '' }");
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        "case.sumi:1:11: error[syntax/empty-char-literal]: character literal is empty\n"
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
        .args(["diagnose", "large.sumi"])
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
    for args in [vec!["--help"], vec!["-h"], vec!["diagnose", "--help"]] {
        let output = sumi().args(args).output().unwrap();
        assert_eq!(output.status.code(), Some(0));
        assert!(String::from_utf8(output.stdout).unwrap().contains("usage:"));
        assert!(output.stderr.is_empty());
    }
    for args in [
        vec![],
        vec!["unknown"],
        vec!["diagnose"],
        vec!["diagnose", "a", "b"],
    ] {
        let output = sumi().args(args).output().unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.starts_with("usage: sumi diagnose <file>\n"));
    }
}

#[test]
fn input_errors_are_distinct_from_source_errors() {
    let (dir, output) = diagnose(&[0xff]);
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .starts_with("case.sumi: error[cli/input]: ")
    );
    let output = sumi()
        .current_dir(dir.path())
        .args(["diagnose", "missing.sumi"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .starts_with("missing.sumi: error[cli/input]: ")
    );
}
