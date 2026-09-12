//! The diagnostics registry, `sumi.diagnostics`: every group of codes and
//! every code, with its documentation. The renderers in `codegen` read it.

#[derive(Debug)]
pub struct Registry {
    pub groups: Vec<Group>,
}

#[derive(Debug)]
pub struct Group {
    pub doc: Vec<String>,
    pub name: String,
    pub codes: Vec<Code>,
}

#[derive(Debug)]
pub struct Code {
    pub doc: Vec<String>,
    pub name: String,
}

impl Registry {
    pub fn parse(source: &str) -> Result<Self, String> {
        let mut groups: Vec<Group> = Vec::new();
        let mut doc: Vec<String> = Vec::new();
        for (index, line) in source.lines().enumerate() {
            let line = line.trim_end();
            let at = |message: String| format!("sumi.diagnostics:{}: {message}", index + 1);
            if let Some(text) = line.strip_prefix("///") {
                doc.push(text.strip_prefix(' ').unwrap_or(text).to_owned());
                continue;
            }
            if line.trim().is_empty() || line.starts_with("//") {
                if !doc.is_empty() && !line.trim().is_empty() {
                    return Err(at("a comment cannot interrupt documentation".into()));
                }
                continue;
            }
            let mut words = line.split_whitespace();
            let (keyword, name) = (words.next(), words.next());
            if words.next().is_some() {
                return Err(at("one declaration per line".into()));
            }
            let Some(name) = name else {
                return Err(at(format!(
                    "expected `group name` or `code name`, found {line:?}"
                )));
            };
            kebab_case(name).map_err(&at)?;
            if doc.is_empty() {
                return Err(at(format!("{name} needs `///` documentation")));
            }
            let doc = std::mem::take(&mut doc);
            match keyword {
                Some("group") => {
                    if groups.iter().any(|group| group.name == name) {
                        return Err(at(format!("group {name} is declared twice")));
                    }
                    groups.push(Group {
                        doc,
                        name: name.to_owned(),
                        codes: Vec::new(),
                    });
                }
                Some("code") => {
                    let Some(group) = groups.last_mut() else {
                        return Err(at(format!("code {name} is declared before any group")));
                    };
                    if group.codes.iter().any(|code| code.name == name) {
                        return Err(at(format!("code {}/{name} is declared twice", group.name)));
                    }
                    group.codes.push(Code {
                        doc,
                        name: name.to_owned(),
                    });
                }
                _ => return Err(at(format!("unknown declaration {line:?}"))),
            }
        }
        if !doc.is_empty() {
            return Err("sumi.diagnostics ends with documentation of nothing".into());
        }
        if let Some(group) = groups.iter().find(|group| group.codes.is_empty()) {
            return Err(format!("group {} declares no code", group.name));
        }
        if groups.is_empty() {
            return Err("sumi.diagnostics declares no group".into());
        }
        Ok(Self { groups })
    }

    pub fn group(&self, name: &str) -> Option<&Group> {
        self.groups.iter().find(|group| group.name == name)
    }
}

/// Lowercase ASCII letters and digits in hyphen-separated words, which is
/// what a code's public spelling and its Rust constant are made from.
fn kebab_case(name: &str) -> Result<(), String> {
    let words: Vec<&str> = name.split('-').collect();
    let word = |word: &&str| {
        !word.is_empty()
            && word
                .bytes()
                .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit())
    };
    if words.iter().all(word) && name.bytes().next().is_some_and(|b| b.is_ascii_lowercase()) {
        Ok(())
    } else {
        Err(format!("{name:?} is not kebab-case"))
    }
}

/// The Rust constant a kebab-case name becomes.
pub fn constant(name: &str) -> String {
    name.to_ascii_uppercase().replace('-', "_")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_groups_and_codes_with_documentation() {
        let registry = Registry::parse(
            "/// Syntax.\ngroup syntax\n/// One.\ncode one\n// note\n/// Two lines\n/// long.\ncode two-2\n",
        )
        .unwrap();
        let group = registry.group("syntax").unwrap();
        assert_eq!(group.doc, ["Syntax."]);
        assert_eq!(group.codes.len(), 2);
        assert_eq!(group.codes[1].doc, ["Two lines", "long."]);
        assert_eq!(constant(&group.codes[1].name), "TWO_2");
    }

    #[test]
    fn rejects_malformed_declarations() {
        let rejected = [
            "code lonely\n",
            "/// G.\ngroup g\ncode undocumented\n",
            "/// G.\ngroup g\n/// C.\ncode Bad-Case\n",
            "/// G.\ngroup g\n/// C.\ncode c\n/// C.\ncode c\n",
            "/// G.\ngroup g\n",
            "/// G.\ngroup g\n/// C.\ncode c\n/// dangling\n",
            "/// G.\n// interrupted\ngroup g\n/// C.\ncode c\n",
        ];
        for source in rejected {
            assert!(Registry::parse(source).is_err(), "{source:?}");
        }
    }
}
