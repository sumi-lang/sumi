//! `sumi.grammar`: its data model, parser, and validation.
//!
//! The format is documented at the top of the grammar file itself. Parsing
//! is strict: every declaration is checked, every reference resolved, and
//! the first problem is reported with its line number.

use std::fmt;

#[derive(Debug, Default)]
pub struct Grammar {
    pub tokens: Vec<Token>,
    pub pairs: Vec<Pair>,
    /// The texts of compound operators, each glued from single punctuation.
    pub compounds: Vec<String>,
    /// The texts of prefix operators.
    pub prefix: Vec<String>,
    pub binary: Vec<Binary>,
    pub rules: Vec<Rule>,
}

#[derive(Debug)]
pub struct Token {
    pub doc: Vec<String>,
    pub name: String,
    pub shape: Shape,
    /// The fixed text of a keyword or punctuation token.
    pub text: Option<String>,
    /// How the token reads after "expected" in a diagnostic.
    pub description: String,
    pub flags: Flags,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    Trivia,
    Ident,
    Keyword,
    Punct,
    Literal,
    Error,
}

/// The token classes a declaration opts into; every table the generated
/// code derives reads from these and the operator tables.
#[derive(Clone, Copy, Debug, Default)]
pub struct Flags {
    /// Can begin an expression.
    pub expr: bool,
    /// Begins a statement that is not an expression.
    pub stmt: bool,
    /// A statement can end after it.
    pub end: bool,
    /// Begins a top-level item.
    pub item: bool,
    /// Continues the previous line's statement.
    pub continues: bool,
}

#[derive(Debug)]
pub struct Pair {
    pub opener: String,
    pub closer: String,
}

#[derive(Debug)]
pub struct Binary {
    pub name: String,
    pub text: String,
    /// Higher levels bind tighter.
    pub level: u8,
    pub comparison: bool,
}

#[derive(Debug)]
pub struct Rule {
    pub doc: Vec<String>,
    pub name: String,
    pub body: Node,
}

/// One rule body in ungrammar notation.
#[derive(Debug)]
pub enum Node {
    /// A token by its fixed text: a keyword, punctuation, or a compound
    /// operator.
    Text(String),
    /// A rule, a token kind, or an implicit operator rule, by name.
    Name(String),
    Seq(Vec<Node>),
    Alt(Vec<Node>),
    Opt(Box<Node>),
    Rep(Box<Node>),
}

/// The rule names the operator tables define implicitly.
pub const PREFIX_OPERATOR_RULE: &str = "PrefixOperator";
pub const BINARY_OPERATOR_RULE: &str = "BinaryOperator";

/// The node kind every grammar has, for tokens the parser could not parse.
pub const ERROR_NODE: &str = "Error";

impl Grammar {
    pub fn parse(source: &str) -> Result<Self, String> {
        let toks = tokenize(source)?;
        let mut parser = Parser {
            toks: &toks,
            pos: 0,
        };
        let grammar = parser.grammar()?;
        grammar.validate()?;
        Ok(grammar)
    }

    pub fn token(&self, name: &str) -> Option<&Token> {
        self.tokens.iter().find(|token| token.name == name)
    }

    /// The keyword or punctuation token with this fixed text.
    pub fn token_by_text(&self, text: &str) -> Option<&Token> {
        self.tokens
            .iter()
            .find(|token| token.text.as_deref() == Some(text))
    }

    /// The punctuation tokens an operator text is glued from: one for a
    /// single character, and one per character of a compound.
    pub fn operator_tokens(&self, text: &str) -> Result<Vec<&Token>, String> {
        text.chars()
            .map(|c| {
                self.token_by_text(c.encode_utf8(&mut [0; 4]))
                    .filter(|token| token.shape == Shape::Punct)
                    .ok_or_else(|| {
                        format!("{c:?} in operator {text:?} is not punctuation of the language")
                    })
            })
            .collect()
    }

    pub fn rule(&self, name: &str) -> Option<&Rule> {
        self.rules.iter().find(|rule| rule.name == name)
    }

    /// Whether a rule names a category — several node kinds — rather than
    /// a node kind of its own: its body lists other rules and nothing else.
    pub fn is_category(&self, rule: &Rule) -> bool {
        let names: Option<Vec<&str>> = match &rule.body {
            Node::Alt(alternatives) => alternatives
                .iter()
                .map(|node| match node {
                    Node::Name(name) => Some(name.as_str()),
                    _ => None,
                })
                .collect(),
            Node::Name(name) => Some(vec![name.as_str()]),
            _ => None,
        };
        names.is_some_and(|names| names.iter().all(|name| self.rule(name).is_some()))
    }

    /// The rules that are node kinds, in declaration order.
    pub fn nodes(&self) -> impl Iterator<Item = &Rule> {
        self.rules.iter().filter(|rule| !self.is_category(rule))
    }

    pub fn max_level(&self) -> u8 {
        self.binary.iter().map(|op| op.level).max().unwrap_or(0)
    }

    fn validate(&self) -> Result<(), String> {
        // Token kinds and rules share a namespace, since a rule refers to
        // either by name; operator names are the parser's own.
        let mut kinds: Vec<String> = Vec::new();
        let mut operators: Vec<String> = Vec::new();
        fn unique(names: &mut Vec<String>, name: &str, what: &str) -> Result<(), String> {
            if names.iter().any(|known| known == name) {
                return Err(format!("{what} {name} is declared twice"));
            }
            names.push(name.to_owned());
            Ok(())
        }
        for token in &self.tokens {
            if !is_kind_name(&token.name) {
                return Err(format!(
                    "token kind {} must be a capitalized identifier",
                    token.name
                ));
            }
            unique(&mut kinds, &token.name, "token kind")?;
            match (token.shape, token.text.as_deref()) {
                (Shape::Keyword, Some(text)) => {
                    let mut chars = text.chars();
                    let ident = chars
                        .next()
                        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_');
                    if !ident {
                        return Err(format!("keyword {text:?} is not an identifier"));
                    }
                }
                (Shape::Punct, Some(text))
                    if !(text.len() == 1 && text.as_bytes()[0].is_ascii_punctuation()) =>
                {
                    return Err(format!(
                        "punctuation {text:?} must be one ASCII punctuation character"
                    ));
                }
                _ => {}
            }
            if let Some(text) = &token.text
                && self
                    .tokens
                    .iter()
                    .filter(|other| other.text.as_ref() == Some(text))
                    .count()
                    > 1
            {
                return Err(format!("text {text:?} is declared for two token kinds"));
            }
        }
        let mut bracketed: Vec<&str> = Vec::new();
        for pair in &self.pairs {
            for name in [&pair.opener, &pair.closer] {
                if self
                    .token(name)
                    .is_none_or(|token| token.shape != Shape::Punct)
                {
                    return Err(format!("bracket {name} is not a punctuation token kind"));
                }
                if bracketed.contains(&name.as_str()) {
                    return Err(format!("bracket {name} is in two pairs"));
                }
                bracketed.push(name);
            }
        }
        for text in &self.compounds {
            if text.chars().count() < 2 {
                return Err(format!(
                    "compound operator {text:?} needs at least two characters"
                ));
            }
            self.operator_tokens(text)?;
            if self.compounds.iter().filter(|other| *other == text).count() > 1 {
                return Err(format!("compound operator {text:?} is declared twice"));
            }
        }
        for text in &self.prefix {
            let tokens = self.operator_text(text)?;
            if tokens.len() != 1 {
                return Err(format!(
                    "prefix operator {text:?} must be one token, which the parser takes whole"
                ));
            }
            if !tokens[0].flags.expr {
                return Err(format!(
                    "prefix operator {text:?} begins an expression, so {} needs the expr flag",
                    tokens[0].name
                ));
            }
            if self.prefix.iter().filter(|other| *other == text).count() > 1 {
                return Err(format!("prefix operator {text:?} is declared twice"));
            }
        }
        for op in &self.binary {
            if !is_kind_name(&op.name) {
                return Err(format!(
                    "binary operator {} must be a capitalized identifier",
                    op.name
                ));
            }
            unique(&mut operators, &op.name, "binary operator")?;
            let tokens = self.operator_text(&op.text)?;
            if tokens.len() > 2 {
                return Err(format!(
                    "binary operator {:?} is wider than the two tokens the parser glues",
                    op.text
                ));
            }
            if op.level == 0 {
                return Err(format!(
                    "binary operator {:?} needs a level of 1 or more",
                    op.text
                ));
            }
            if self
                .binary
                .iter()
                .filter(|other| other.text == op.text)
                .count()
                > 1
            {
                return Err(format!("binary operator {:?} is declared twice", op.text));
            }
        }
        for token in self.tokens.iter().filter(|token| token.flags.continues) {
            let operator = self
                .prefix
                .iter()
                .chain(self.binary.iter().map(|op| &op.text));
            if operator
                .flat_map(|text| self.operator_tokens(text))
                .any(|tokens| tokens[0].name == token.name)
            {
                return Err(format!(
                    "{} is an operator, which continues a line by the operator tables, not the continue flag",
                    token.name
                ));
            }
        }
        for rule in &self.rules {
            if !is_kind_name(&rule.name) {
                return Err(format!(
                    "rule {} must be a capitalized identifier",
                    rule.name
                ));
            }
            if [PREFIX_OPERATOR_RULE, BINARY_OPERATOR_RULE, ERROR_NODE]
                .contains(&rule.name.as_str())
            {
                return Err(format!(
                    "rule {} is implicit and cannot be declared",
                    rule.name
                ));
            }
            unique(&mut kinds, &rule.name, "rule")?;
            self.resolve(&rule.body)
                .map_err(|error| format!("in rule {}: {error}", rule.name))?;
        }
        if self.rules.is_empty() {
            return Err("no node rules are declared".into());
        }
        Ok(())
    }

    /// The tokens of a prefix or binary operator text: one punctuation
    /// token, or the tokens of a declared compound.
    fn operator_text(&self, text: &str) -> Result<Vec<&Token>, String> {
        let tokens = self.operator_tokens(text)?;
        if tokens.len() > 1 && !self.compounds.contains(&text.to_owned()) {
            return Err(format!("operator {text:?} is not a declared compound"));
        }
        Ok(tokens)
    }

    fn resolve(&self, node: &Node) -> Result<(), String> {
        match node {
            Node::Text(text) => {
                if self.token_by_text(text).is_none() && !self.compounds.contains(text) {
                    return Err(format!(
                        "'{text}' is not the text of any token or compound operator"
                    ));
                }
            }
            Node::Name(name) => {
                let known = self.rule(name).is_some()
                    || self.token(name).is_some()
                    || [PREFIX_OPERATOR_RULE, BINARY_OPERATOR_RULE].contains(&name.as_str());
                if !known {
                    return Err(format!("{name} is not a rule or a token kind"));
                }
            }
            Node::Seq(items) | Node::Alt(items) => {
                for item in items {
                    self.resolve(item)?;
                }
            }
            Node::Opt(inner) | Node::Rep(inner) => self.resolve(inner)?,
        }
        Ok(())
    }
}

fn is_kind_name(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c.is_ascii_uppercase()) && chars.all(|c| c.is_ascii_alphanumeric())
}

impl Node {
    /// Whether the node prints without parentheses inside a sequence.
    fn is_atomic(&self) -> bool {
        !matches!(self, Node::Seq(_) | Node::Alt(_))
    }
}

/// Ungrammar notation, normalized to one line.
impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let grouped = |node: &Node, f: &mut fmt::Formatter<'_>| {
            if node.is_atomic() {
                write!(f, "{node}")
            } else {
                write!(f, "({node})")
            }
        };
        match self {
            Node::Text(text) => write!(f, "'{text}'"),
            Node::Name(name) => f.write_str(name),
            Node::Seq(items) => {
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        f.write_str(" ")?;
                    }
                    grouped(item, f)?;
                }
                Ok(())
            }
            Node::Alt(items) => {
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        f.write_str(" | ")?;
                    }
                    grouped(item, f)?;
                }
                Ok(())
            }
            Node::Opt(inner) => {
                grouped(inner, f)?;
                f.write_str("?")
            }
            Node::Rep(inner) => {
                grouped(inner, f)?;
                f.write_str("*")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Word(String),
    Str(String),
    Punct(char),
    Doc(String),
    Newline,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tok::Word(word) => write!(f, "`{word}`"),
            Tok::Str(text) => write!(f, "\"{text}\""),
            Tok::Punct(c) => write!(f, "`{c}`"),
            Tok::Doc(_) => f.write_str("a `///` comment"),
            Tok::Newline => f.write_str("end of line"),
        }
    }
}

fn tokenize(source: &str) -> Result<Vec<(usize, Tok)>, String> {
    let mut toks = Vec::new();
    for (index, line) in source.lines().enumerate() {
        let number = index + 1;
        let mut rest = line;
        loop {
            rest = rest.trim_start_matches([' ', '\t']);
            if rest.is_empty() {
                break;
            }
            if let Some(doc) = rest.strip_prefix("///") {
                let doc = doc.strip_prefix(' ').unwrap_or(doc);
                toks.push((number, Tok::Doc(doc.trim_end().to_owned())));
                break;
            }
            if rest.starts_with("//") {
                break;
            }
            let c = rest.chars().next().expect("nonempty");
            match c {
                '"' | '\'' => {
                    let Some(end) = rest[1..].find(c) else {
                        return Err(format!("line {number}: unterminated {c}…{c} text"));
                    };
                    toks.push((number, Tok::Str(rest[1..1 + end].to_owned())));
                    rest = &rest[end + 2..];
                }
                '=' | '|' | '(' | ')' | '?' | '*' => {
                    toks.push((number, Tok::Punct(c)));
                    rest = &rest[1..];
                }
                c if c.is_ascii_alphanumeric() || c == '_' => {
                    let end = rest
                        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                        .unwrap_or(rest.len());
                    toks.push((number, Tok::Word(rest[..end].to_owned())));
                    rest = &rest[end..];
                }
                _ => return Err(format!("line {number}: unexpected character {c:?}")),
            }
        }
        toks.push((number, Tok::Newline));
    }
    Ok(toks)
}

struct Parser<'a> {
    toks: &'a [(usize, Tok)],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn grammar(&mut self) -> Result<Grammar, String> {
        let mut grammar = Grammar::default();
        loop {
            self.skip_newlines();
            let doc = self.docs()?;
            let Some(tok) = self.peek() else {
                if !doc.is_empty() {
                    return Err(self.error("documentation with nothing to document"));
                }
                return Ok(grammar);
            };
            match tok {
                Tok::Word(word) if word == "token" => {
                    self.pos += 1;
                    grammar.tokens.push(self.token(doc)?);
                }
                Tok::Word(word) if is_kind_name(word) => grammar.rules.push(self.rule(doc)?),
                Tok::Word(word) if !doc.is_empty() => {
                    return Err(self.error(&format!("`{word}` declarations take no documentation")));
                }
                Tok::Word(word) if word == "pair" => {
                    self.pos += 1;
                    let opener = self.word("an opener kind")?;
                    let closer = self.word("a closer kind")?;
                    self.end_of_line()?;
                    grammar.pairs.push(Pair { opener, closer });
                }
                Tok::Word(word) if word == "compound" => {
                    self.pos += 1;
                    grammar.compounds.push(self.string("the operator's text")?);
                    self.end_of_line()?;
                }
                Tok::Word(word) if word == "prefix" => {
                    self.pos += 1;
                    grammar.prefix.push(self.string("the operator's text")?);
                    self.end_of_line()?;
                }
                Tok::Word(word) if word == "binary" => {
                    self.pos += 1;
                    grammar.binary.push(self.binary()?);
                }
                other => {
                    return Err(self.error(&format!("expected a declaration, found {other}")));
                }
            }
        }
    }

    fn token(&mut self, doc: Vec<String>) -> Result<Token, String> {
        let name = self.word("a token kind name")?;
        let shape = match self.word("a token shape")?.as_str() {
            "trivia" => Shape::Trivia,
            "ident" => Shape::Ident,
            "keyword" => Shape::Keyword,
            "punct" => Shape::Punct,
            "literal" => Shape::Literal,
            "error" => Shape::Error,
            other => return Err(self.error(&format!("`{other}` is not a token shape"))),
        };
        let text = match shape {
            Shape::Keyword | Shape::Punct => Some(self.string("the token's text")?),
            _ => None,
        };
        let description = match self.peek() {
            Some(Tok::Str(_)) => self.string("a description")?,
            _ => match &text {
                Some(text) => format!("`{text}`"),
                None => return Err(self.error("expected a description")),
            },
        };
        let mut flags = Flags::default();
        while let Some(Tok::Word(flag)) = self.peek() {
            let flag = match flag.as_str() {
                "expr" => &mut flags.expr,
                "stmt" => &mut flags.stmt,
                "end" => &mut flags.end,
                "item" => &mut flags.item,
                "continue" => &mut flags.continues,
                other => return Err(self.error(&format!("`{other}` is not a token flag"))),
            };
            if *flag {
                return Err(self.error("flag is repeated"));
            }
            *flag = true;
            self.pos += 1;
        }
        self.end_of_line()?;
        Ok(Token {
            doc,
            name,
            shape,
            text,
            description,
            flags,
        })
    }

    fn binary(&mut self) -> Result<Binary, String> {
        let name = self.word("an operator name")?;
        let text = self.string("the operator's text")?;
        let level = self.word("a precedence level")?;
        let Ok(level) = level.parse::<u8>() else {
            return Err(self.error(&format!("`{level}` is not a precedence level")));
        };
        let comparison = match self.peek() {
            Some(Tok::Word(word)) if word == "comparison" => {
                self.pos += 1;
                true
            }
            _ => false,
        };
        self.end_of_line()?;
        Ok(Binary {
            name,
            text,
            level,
            comparison,
        })
    }

    fn rule(&mut self, doc: Vec<String>) -> Result<Rule, String> {
        let name = self.word("a rule name")?;
        self.punct('=')?;
        let body = self.alternatives()?;
        Ok(Rule { doc, name, body })
    }

    fn alternatives(&mut self) -> Result<Node, String> {
        let mut alternatives = vec![self.sequence()?];
        loop {
            self.skip_newlines();
            if self.peek() != Some(&Tok::Punct('|')) {
                break;
            }
            self.pos += 1;
            alternatives.push(self.sequence()?);
        }
        Ok(if alternatives.len() == 1 {
            alternatives.pop().expect("one alternative")
        } else {
            Node::Alt(alternatives)
        })
    }

    fn sequence(&mut self) -> Result<Node, String> {
        let mut items = Vec::new();
        while let Some(atom) = self.atom()? {
            items.push(atom);
        }
        if items.is_empty() {
            return Err(self.error("expected a rule atom"));
        }
        Ok(if items.len() == 1 {
            items.pop().expect("one item")
        } else {
            Node::Seq(items)
        })
    }

    fn atom(&mut self) -> Result<Option<Node>, String> {
        self.skip_newlines();
        let starts_rule = matches!(self.toks.get(self.pos + 1), Some((_, Tok::Punct('='))));
        let node = match self.peek() {
            Some(Tok::Str(text)) => {
                let text = text.clone();
                self.pos += 1;
                Node::Text(text)
            }
            Some(Tok::Word(name)) if is_kind_name(name) && !starts_rule => {
                let name = name.clone();
                self.pos += 1;
                Node::Name(name)
            }
            Some(Tok::Punct('(')) => {
                self.pos += 1;
                let inner = self.alternatives()?;
                self.skip_newlines();
                self.punct(')')?;
                inner
            }
            _ => return Ok(None),
        };
        let node = match self.peek() {
            Some(Tok::Punct('?')) => {
                self.pos += 1;
                Node::Opt(Box::new(node))
            }
            Some(Tok::Punct('*')) => {
                self.pos += 1;
                Node::Rep(Box::new(node))
            }
            _ => node,
        };
        Ok(Some(node))
    }

    /// The `///` lines before a declaration, which must follow directly.
    fn docs(&mut self) -> Result<Vec<String>, String> {
        let mut doc = Vec::new();
        while let Some(Tok::Doc(line)) = self.peek() {
            doc.push(line.clone());
            self.pos += 1;
            self.end_of_line()?;
        }
        if !doc.is_empty() && matches!(self.peek(), None | Some(Tok::Newline)) {
            return Err(self.error("documentation must directly precede its declaration"));
        }
        Ok(doc)
    }

    fn peek(&self) -> Option<&'a Tok> {
        self.toks.get(self.pos).map(|(_, tok)| tok)
    }

    fn skip_newlines(&mut self) {
        while self.peek() == Some(&Tok::Newline) {
            self.pos += 1;
        }
    }

    fn word(&mut self, expected: &str) -> Result<String, String> {
        match self.peek() {
            Some(Tok::Word(word)) => {
                let word = word.clone();
                self.pos += 1;
                Ok(word)
            }
            _ => Err(self.expected(expected)),
        }
    }

    fn string(&mut self, expected: &str) -> Result<String, String> {
        match self.peek() {
            Some(Tok::Str(text)) => {
                let text = text.clone();
                self.pos += 1;
                Ok(text)
            }
            _ => Err(self.expected(expected)),
        }
    }

    fn punct(&mut self, c: char) -> Result<(), String> {
        if self.peek() == Some(&Tok::Punct(c)) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.expected(&format!("`{c}`")))
        }
    }

    fn end_of_line(&mut self) -> Result<(), String> {
        match self.peek() {
            None => Ok(()),
            Some(Tok::Newline) => {
                self.pos += 1;
                Ok(())
            }
            _ => Err(self.expected("end of line")),
        }
    }

    fn expected(&self, expected: &str) -> String {
        match self.peek() {
            Some(found) => self.error(&format!("expected {expected}, found {found}")),
            None => self.error(&format!("expected {expected}, found end of file")),
        }
    }

    fn error(&self, message: &str) -> String {
        let line = self
            .toks
            .get(self.pos)
            .or(self.toks.last())
            .map_or(1, |(line, _)| *line);
        format!("sumi.grammar:{line}: {message}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const GRAMMAR: &str = "\
/// Words.
token Ident ident \"a name\" expr end
token LParen punct \"(\" expr
token RParen punct \")\" end
token Minus punct \"-\" expr
token Gt punct \">\"
token FnKw keyword \"fn\" item
pair LParen RParen
compound \"->\"
prefix \"-\"
binary Sub \"-\" 1
Item = 'fn' Ident ('->' Ident)? Expr
Expr =
  NameExpr
| PrefixExpr
NameExpr = Ident
PrefixExpr = PrefixOperator Expr
";

    #[test]
    fn parses_every_declaration() {
        let grammar = Grammar::parse(GRAMMAR).unwrap();
        assert_eq!(grammar.tokens.len(), 6);
        assert_eq!(grammar.tokens[0].doc, ["Words."]);
        assert_eq!(grammar.token("LParen").unwrap().description, "`(`");
        assert!(grammar.token("FnKw").unwrap().flags.item);
        assert_eq!(grammar.pairs.len(), 1);
        assert_eq!(grammar.operator_tokens("->").unwrap().len(), 2);
        let nodes: Vec<&str> = grammar.nodes().map(|rule| rule.name.as_str()).collect();
        assert_eq!(nodes, ["Item", "NameExpr", "PrefixExpr"]);
        assert_eq!(
            grammar.rule("Item").unwrap().body.to_string(),
            "'fn' Ident ('->' Ident)? Expr"
        );
        assert_eq!(
            grammar.rule("Expr").unwrap().body.to_string(),
            "NameExpr | PrefixExpr"
        );
    }

    #[test]
    fn rejects_unresolved_references() {
        let source = format!("{GRAMMAR}Bad = 'while'\n");
        let error = Grammar::parse(&source).unwrap_err();
        assert!(error.contains("'while'"), "{error}");
        let source = format!("{GRAMMAR}Bad = WhileExpr\n");
        let error = Grammar::parse(&source).unwrap_err();
        assert!(error.contains("WhileExpr"), "{error}");
    }

    #[test]
    fn rejects_malformed_declarations() {
        for (line, needle) in [
            ("token lower ident \"x\"", "capitalized"),
            ("token Dup ident \"x\"\ntoken Dup ident \"y\"", "twice"),
            ("token Semi punct \";;\"", "one ASCII punctuation"),
            ("token Bang punct \"!\" expr expr", "repeated"),
            ("token Odd ident \"x\" fancy", "not a token flag"),
            ("pair Ident RParen", "not a punctuation"),
            ("compound \"-\"", "at least two"),
            ("prefix \"->\"", "one token"),
            ("binary Arrow \"->\" 1\nprefix \"-\"", "declared twice"),
            ("binary Gt2 \">\" 0", "level of 1"),
            ("/// Lost.\n\nItem2 = Ident", "directly precede"),
            ("Empty =\n", "rule atom"),
        ] {
            let source = format!("{GRAMMAR}{line}\n");
            let error = Grammar::parse(&source).unwrap_err();
            assert!(error.contains(needle), "{line:?} gave {error:?}");
        }
    }
}
