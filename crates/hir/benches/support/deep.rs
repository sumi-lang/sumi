pub fn source(shape: &str, depth: usize) -> String {
    let body = match shape {
        "tail" => "fn count(n: int, total: int) -> int = if n <= 0 { total } else { count(n - 1, total + 1) }",
        "mutual-tail" => "fn count(n: int, total: int) -> int = if n <= 0 { total } else { other(total + 1, n - 1, true) }
fn other(total: int, n: int, b: bool) -> int = if b { count(n, total) } else { 0 }",
        "return-tail" => "fn count(n: int, total: int) -> int { if n > 0 { return count(n - 1, total + 1) }\n total }",
        "non-tail" => "fn count(n: int, total: int) -> int = if n <= 0 { total } else { 1 + count(n - 1, total) }",
        _ => unreachable!(),
    };
    format!("{body}\nfn main() -> int = count({depth}, 7)")
}
