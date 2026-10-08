//! Prints a fuzz target's input as text: for `edit`, the edit and the token it lands on above the
//! source, as the recovery check reports them; for the rest, the bytes as the source they are.
use std::fs;

use sumi_test::{edit_input, front};

fn main() {
    let (Some(target), Some(path)) = (std::env::args().nth(1), std::env::args().nth(2)) else {
        eprintln!("usage: fuzz-show <target> <input>");
        std::process::exit(2);
    };
    let data = fs::read(&path).unwrap_or_else(|error| panic!("cannot read {path}: {error}"));
    if target != "edit" {
        print!("{}", String::from_utf8_lossy(&data));
        return;
    }
    let Some((edit, index, source)) = edit_input(&data) else {
        println!("not an edit input: {} bytes", data.len());
        return;
    };
    let original = front(source);
    let count = original.parse.input().len();
    let index = usize::from(index) % count.max(1);
    let spans = original.spans();
    let token = spans
        .get(index)
        .map_or("none", |&(start, end)| &source[start..end]);
    println!("{edit:?} at token {index} ({token:?})");
    println!("--- source ---");
    print!("{source}");
    if !source.ends_with('\n') {
        println!();
    }
}
