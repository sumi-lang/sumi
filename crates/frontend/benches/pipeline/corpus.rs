//! Deterministic Sumi source generation for the frontend benchmarks.
//!
//! The clean generator emits strictly valid Sumi — spaced binary
//! operators, glued prefix operators, blocks on the line of their owner,
//! one statement per line (with occasional operator-led continuation
//! lines) — so a valid corpus must produce zero diagnostics, which the
//! benches assert. The corruptor then injects seeded, byte-level damage
//! to exercise recovery paths.
//!
//! Every benchmark baseline hangs off these exact bytes: the generation
//! logic and the seeds pinned in `main.rs` define the corpora, and
//! changing either resets the performance history CodSpeed tracks.

pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed ^ 0x9E37_79B9_7F4A_7C15)
    }

    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) as u32
    }

    fn below(&mut self, n: u32) -> u32 {
        self.next_u32() % n
    }

    fn chance(&mut self, percent: u32) -> bool {
        self.below(100) < percent
    }

    fn pick<'a>(&mut self, items: &'a [&'a str]) -> &'a str {
        items[self.below(items.len() as u32) as usize]
    }
}

const NOUNS: &[&str] = &[
    "value", "total", "offset", "index", "count", "width", "limit", "delta", "scale", "cursor",
    "weight", "ratio", "phase", "depth", "span",
];
const VERBS: &[&str] = &[
    "compute", "blend", "scan", "merge", "fold", "clamp", "shift", "probe", "route", "trace",
];
const TYPES: &[&str] = &["Int", "Float", "Bool", "Str", "Char"];
const INTS: &[&str] = &["0", "1", "2", "7", "42", "128", "1_000", "9999"];
const FLOATS: &[&str] = &["0.5", "3.25", "1e9", "2.5e-3", "12.75", "1.0"];
const CHARS: &[&str] = &["'a'", "'z'", "'0'", "'\\n'", "'\\\\'", "'\\u{41}'"];
const CMP_OPS: &[&str] = &["==", "!=", "<", "<=", ">", ">="];
const ADD_OPS: &[&str] = &["+", "-"];
const MUL_OPS: &[&str] = &["*", "/", "%"];

struct Gen {
    rng: Rng,
    out: String,
    fresh: u32,
}

/// Generate at least `target_bytes` of valid Sumi source.
pub fn generate(target_bytes: usize, seed: u64) -> String {
    let mut g = Gen {
        rng: Rng::new(seed),
        out: String::with_capacity(target_bytes + 1024),
        fresh: 0,
    };
    g.out.push_str("//! Generated Sumi benchmark corpus.\n\n");
    while g.out.len() < target_bytes {
        g.fn_item();
    }
    g.out
}

impl Gen {
    fn fresh_name(&mut self, pool: &[&str]) -> String {
        self.fresh += 1;
        format!("{}{}", self.rng.pick(pool), self.fresh)
    }

    fn indent(&mut self, level: usize) {
        for _ in 0..level {
            self.out.push_str("    ");
        }
    }

    fn fn_item(&mut self) {
        if self.rng.chance(20) {
            let a = self.rng.pick(NOUNS);
            let b = self.rng.pick(NOUNS);
            self.out
                .push_str(&format!("/// Computes the {a} of the {b}.\n"));
        }
        let verb = self.rng.pick(VERBS);
        self.fresh += 1;
        let name = format!("{verb}_{}", self.fresh);
        let mut scope: Vec<String> = Vec::new();
        let params = self.rng.below(5);
        let mut sig = format!("fn {name}(");
        for i in 0..params {
            if i > 0 {
                sig.push_str(", ");
            }
            let p = self.fresh_name(NOUNS);
            let ty = self.rng.pick(TYPES);
            sig.push_str(&format!("{p}: {ty}"));
            scope.push(p);
        }
        sig.push(')');
        let returns = self.rng.chance(50);
        if returns {
            let ty = self.rng.pick(TYPES);
            sig.push_str(&format!(" -> {ty}"));
        }
        sig.push_str(" {\n");
        self.out.push_str(&sig);
        let stmts = 3 + self.rng.below(7);
        for _ in 0..stmts {
            self.statement(1, 0, &mut scope);
        }
        if returns {
            self.indent(1);
            let e = self.expr(&scope, 0);
            self.out.push_str(&format!("return {e}\n"));
        }
        self.out.push_str("}\n\n");
    }

    fn statement(&mut self, level: usize, depth: u32, scope: &mut Vec<String>) {
        if self.rng.chance(8) {
            self.indent(level);
            let n = self.rng.pick(NOUNS);
            self.out.push_str(&format!("// tune the {n}\n"));
        }
        let roll = self.rng.below(100);
        self.indent(level);
        if roll < 42 {
            self.let_stmt(level, scope);
        } else if roll < 52 {
            let e = self.expr(scope, 0);
            self.out.push_str(&format!("_ = {e}\n"));
        } else if roll < 67 && depth < 2 {
            self.if_stmt(level, depth, scope);
        } else if roll < 82 {
            let callee = self.rng.pick(VERBS);
            let args = self.call_args(scope);
            self.out.push_str(&format!("{callee}{args}\n"));
        } else if roll < 92 {
            let e = self.expr(scope, 0);
            self.out.push_str(&format!("return {e}\n"));
        } else {
            let e = self.expr(scope, 0);
            self.out.push_str(&e);
            self.out.push('\n');
        }
    }

    fn let_stmt(&mut self, level: usize, scope: &mut Vec<String>) {
        let name = self.fresh_name(NOUNS);
        let mutable = if self.rng.chance(15) { "mut " } else { "" };
        let annotation = if self.rng.chance(20) {
            format!(": {}", self.rng.pick(TYPES))
        } else {
            String::new()
        };
        if self.rng.chance(8) {
            // Conditional initializer: blocks stay on the line of the `if`.
            let c = self.condition(scope);
            let a = self.atom(scope, 3);
            let b = self.atom(scope, 3);
            self.out.push_str(&format!(
                "let {mutable}{name}{annotation} = if {c} {{ {a} }} else {{ {b} }}\n"
            ));
        } else if self.rng.chance(6) {
            // Continuation line: the operator leads the next line.
            let a = self.mul_expr(scope, 1);
            let b = self.mul_expr(scope, 1);
            self.out
                .push_str(&format!("let {mutable}{name}{annotation} = {a}\n"));
            self.indent(level + 1);
            self.out.push_str(&format!("+ {b}\n"));
        } else {
            let e = self.expr(scope, 0);
            self.out
                .push_str(&format!("let {mutable}{name}{annotation} = {e}\n"));
        }
        scope.push(name);
    }

    fn if_stmt(&mut self, level: usize, depth: u32, scope: &mut Vec<String>) {
        let c = self.condition(scope);
        self.out.push_str(&format!("if {c} {{\n"));
        let stmts = 1 + self.rng.below(4);
        let mark = scope.len();
        for _ in 0..stmts {
            self.statement(level + 1, depth + 1, scope);
        }
        scope.truncate(mark);
        self.indent(level);
        self.out.push('}');
        if self.rng.chance(50) {
            if self.rng.chance(30) {
                let c2 = self.condition(scope);
                self.out.push_str(&format!(" else if {c2} {{\n"));
            } else {
                self.out.push_str(" else {\n");
            }
            let stmts = 1 + self.rng.below(3);
            let mark = scope.len();
            for _ in 0..stmts {
                self.statement(level + 1, depth + 1, scope);
            }
            scope.truncate(mark);
            self.indent(level);
            self.out.push('}');
        }
        self.out.push('\n');
    }

    fn condition(&mut self, scope: &[String]) -> String {
        let a = self.add_expr(scope, 1);
        let op = self.rng.pick(CMP_OPS);
        let b = self.add_expr(scope, 1);
        let mut s = format!("{a} {op} {b}");
        if self.rng.chance(15) {
            let c = self.atom(scope, 3);
            let logic = if self.rng.chance(50) { "&&" } else { "||" };
            s = format!("{s} {logic} {c}");
        }
        s
    }

    /// Full expression: logical ops over at most one comparison layer, so
    /// comparisons never chain.
    fn expr(&mut self, scope: &[String], depth: u32) -> String {
        let mut s = self.cmp_expr(scope, depth);
        if self.rng.chance(12) {
            let logic = if self.rng.chance(50) { "&&" } else { "||" };
            let rhs = self.cmp_expr(scope, depth);
            s = format!("{s} {logic} {rhs}");
        }
        s
    }

    fn cmp_expr(&mut self, scope: &[String], depth: u32) -> String {
        let mut s = self.add_expr(scope, depth);
        if self.rng.chance(18) {
            let op = self.rng.pick(CMP_OPS);
            let rhs = self.add_expr(scope, depth);
            s = format!("{s} {op} {rhs}");
        }
        s
    }

    fn add_expr(&mut self, scope: &[String], depth: u32) -> String {
        let mut s = self.mul_expr(scope, depth);
        for _ in 0..self.rng.below(3) {
            if !self.rng.chance(40) {
                break;
            }
            let op = self.rng.pick(ADD_OPS);
            let rhs = self.mul_expr(scope, depth);
            s = format!("{s} {op} {rhs}");
        }
        s
    }

    fn mul_expr(&mut self, scope: &[String], depth: u32) -> String {
        let mut s = self.unary_expr(scope, depth);
        if self.rng.chance(25) {
            let op = self.rng.pick(MUL_OPS);
            let rhs = self.unary_expr(scope, depth);
            s = format!("{s} {op} {rhs}");
        }
        s
    }

    fn unary_expr(&mut self, scope: &[String], depth: u32) -> String {
        let inner = self.postfix_expr(scope, depth);
        if self.rng.chance(10) {
            // Prefix operators glue to their operand.
            let op = if self.rng.chance(60) { "-" } else { "!" };
            format!("{op}{inner}")
        } else {
            inner
        }
    }

    fn postfix_expr(&mut self, scope: &[String], depth: u32) -> String {
        if self.rng.chance(18) {
            let callee = self.rng.pick(VERBS);
            let args = self.call_args_at(scope, depth);
            return format!("{callee}{args}");
        }
        self.atom(scope, depth)
    }

    fn call_args(&mut self, scope: &[String]) -> String {
        self.call_args_at(scope, 1)
    }

    fn call_args_at(&mut self, scope: &[String], depth: u32) -> String {
        let n = self.rng.below(4);
        let mut s = String::from("(");
        for i in 0..n {
            if i > 0 {
                s.push_str(", ");
            }
            let a = if depth < 3 {
                self.add_expr(scope, depth + 1)
            } else {
                self.atom(scope, depth)
            };
            s.push_str(&a);
        }
        s.push(')');
        s
    }

    fn atom(&mut self, scope: &[String], depth: u32) -> String {
        if !scope.is_empty() && self.rng.chance(55) {
            return scope[self.rng.below(scope.len() as u32) as usize].clone();
        }
        match self.rng.below(100) {
            0..=39 => self.rng.pick(INTS).to_string(),
            40..=54 => self.rng.pick(FLOATS).to_string(),
            55..=69 => {
                if self.rng.chance(20) {
                    "\"a\\tb\\nc \\\"q\\\" \\\\ \\u{1F600}\"".to_string()
                } else if self.rng.chance(10) {
                    "r\"raw \\no escape\"".to_string()
                } else {
                    self.fresh += 1;
                    format!("\"item {}\"", self.fresh)
                }
            }
            70..=77 => self.rng.pick(CHARS).to_string(),
            78..=87 => if self.rng.chance(50) { "true" } else { "false" }.to_string(),
            _ => {
                if depth < 3 {
                    let inner = self.expr(scope, depth + 1);
                    format!("({inner})")
                } else {
                    self.rng.pick(INTS).to_string()
                }
            }
        }
    }
}

/// Inject one seeded corruption roughly every `stride` bytes. Only ASCII
/// positions are touched, so the result stays valid UTF-8.
pub fn corrupt(source: &str, seed: u64, stride: usize) -> String {
    let mut bytes = source.as_bytes().to_vec();
    let mut rng = Rng::new(seed);
    let mut pos = stride / 2;
    while pos < bytes.len().saturating_sub(4) {
        let ascii = match (pos..bytes.len().min(pos + 8)).find(|&p| bytes[p].is_ascii()) {
            Some(p) => p,
            None => {
                pos += stride;
                continue;
            }
        };
        match rng.below(7) {
            0 => {
                bytes.remove(ascii);
            }
            1 => bytes.insert(ascii, b';'),
            2 => bytes.insert(ascii, b'['),
            3 => remove_next(&mut bytes, ascii, b')'),
            4 => remove_next(&mut bytes, ascii, b'}'),
            5 => remove_next(&mut bytes, ascii, b'"'),
            _ => {
                bytes.insert(ascii, b' ');
                bytes.insert(ascii, b'+');
            }
        }
        pos += stride / 2 + rng.below(stride as u32) as usize;
    }
    String::from_utf8(bytes).expect("corruptions preserve UTF-8")
}

fn remove_next(bytes: &mut Vec<u8>, from: usize, needle: u8) {
    if let Some(at) = (from..bytes.len().min(from + 2000)).find(|&p| bytes[p] == needle) {
        bytes.remove(at);
    }
}
