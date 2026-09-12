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

fn fmt(args: &[&str], files: &[(&str, &str)]) -> (tempfile::TempDir, Output) {
    let dir = tempfile::tempdir().unwrap();
    for (name, source) in files {
        fs::write(dir.path().join(name), source).unwrap();
    }
    let output = sumi()
        .current_dir(dir.path())
        .arg("fmt")
        .args(args)
        .output()
        .unwrap();
    (dir, output)
}

#[test]
fn fmt_rewrites_files_in_place_and_is_silent() {
    let (dir, output) = fmt(
        &["a.sumi", "b.sumi"],
        &[
            ("a.sumi", "fn f(x:int)->int{x*2}"),
            ("b.sumi", "fn g() {}\n"),
        ],
    );
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    assert_eq!(
        fs::read_to_string(dir.path().join("a.sumi")).unwrap(),
        "fn f(x: int) -> int {\n    x * 2\n}\n"
    );
    assert_eq!(
        fs::read_to_string(dir.path().join("b.sumi")).unwrap(),
        "fn g() {}\n"
    );
}

#[test]
fn fmt_check_lists_files_that_would_change_and_writes_nothing() {
    let (dir, output) = fmt(
        &["--check", "a.sumi", "b.sumi"],
        &[
            ("a.sumi", "fn f(x:int)->int{x*2}"),
            ("b.sumi", "fn g() {}\n"),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "a.sumi\n");
    assert_eq!(
        fs::read_to_string(dir.path().join("a.sumi")).unwrap(),
        "fn f(x:int)->int{x*2}"
    );

    let (_dir, output) = fmt(&["--check", "b.sumi"], &[("b.sumi", "fn g() {}\n")]);
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stdout.is_empty());
}

#[test]
fn fmt_formats_what_it_can_around_syntax_errors() {
    let (dir, output) = fmt(
        &["a.sumi"],
        &[("a.sumi", "fn f() { let y = (\n}\nfn g() { ok(1) }")],
    );
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        fs::read_to_string(dir.path().join("a.sumi")).unwrap(),
        "fn f() {\n    let y = (\n}\nfn g() {\n    ok(1)\n}\n"
    );
}

#[test]
fn fmt_filters_stdin_to_stdout() {
    use std::io::Write as _;
    use std::process::Stdio;
    let mut child = sumi()
        .args(["fmt", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(b"fn f(){1}").unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "fn f() {\n    1\n}\n"
    );
}

#[test]
fn fmt_reports_missing_files_as_input_errors() {
    let (_dir, output) = fmt(&["missing.sumi"], &[]);
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("missing.sumi: error[cli/input]")
    );
}
