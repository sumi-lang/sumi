use std::io::Write;
use std::process::{Command, Stdio};

use serde_json::{Value, json};

#[test]
fn exit_without_shutdown_returns_failure() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sumi-lsp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    send(
        &mut stdin,
        json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": { "capabilities": {} }
        }),
    );
    send(
        &mut stdin,
        json!({ "jsonrpc": "2.0", "method": "initialized", "params": {} }),
    );
    send(
        &mut stdin,
        json!({ "jsonrpc": "2.0", "method": "exit", "params": null }),
    );
    drop(stdin);

    assert!(!child.wait().unwrap().success());
}

fn send(output: &mut impl Write, message: Value) {
    let body = serde_json::to_vec(&message).unwrap();
    write!(output, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
    output.write_all(&body).unwrap();
    output.flush().unwrap();
}
