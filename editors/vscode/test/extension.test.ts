import path from "node:path";

import { describe, expect, test } from "bun:test";
import oniguruma from "vscode-oniguruma";
import textmate from "vscode-textmate";
import type { IToken, StateStack } from "vscode-textmate";

const { OnigScanner, OnigString, loadWASM } = oniguruma;
const { Registry } = textmate;

const root = path.join(import.meta.dir, "..");
const wasm = await Bun.file(
  path.join(root, "node_modules", "vscode-oniguruma", "release", "onig.wasm"),
).arrayBuffer();
await loadWASM(wasm);

const registry = new Registry({
  onigLib: Promise.resolve({
    createOnigScanner: (patterns: string[]) => new OnigScanner(patterns),
    createOnigString: (text: string) => new OnigString(text),
  }),
  loadGrammar: async (scopeName: string) => {
    expect(scopeName).toBe("source.sumi");
    return Bun.file(path.join(root, "syntaxes", "sumi.tmLanguage.json")).json();
  },
});
const loadedGrammar = await registry.loadGrammar("source.sumi");
if (loadedGrammar === null) {
  throw new Error("Sumi TextMate grammar did not load");
}
const grammar = loadedGrammar;

type TokenizedLine = { line: string; tokens: IToken[] };

function tokenize(source: string): TokenizedLine[] {
  let state: StateStack | null = null;
  return source.split("\n").map((line) => {
    const result = grammar.tokenizeLine(line, state);
    state = result.ruleStack;
    return { line, tokens: result.tokens };
  });
}

function scopesAt(tokenized: TokenizedLine[], lineIndex: number, text: string, occurrence = 0) {
  const { line, tokens } = tokenized[lineIndex];
  let start = -1;
  for (let count = 0, from = 0; count <= occurrence; count += 1) {
    start = line.indexOf(text, from);
    expect(start, `${JSON.stringify(text)} is present`).not.toBe(-1);
    from = start + text.length;
  }
  const token = tokens.find(({ startIndex, endIndex }) => startIndex <= start && start < endIndex);
  expect(
    token,
    `a grammar token covers ${JSON.stringify(text)} on line ${lineIndex + 1}`,
  ).toBeDefined();
  return token?.scopes ?? [];
}

describe("extension contributions", () => {
  test("registers Sumi and its language server", async () => {
    const manifest = await Bun.file(path.join(root, "package.json")).json();
    expect(manifest.main).toBe("./out/extension.js");
    expect(manifest.extensionKind).toEqual(["workspace"]);
    expect(manifest.activationEvents).toContain("onLanguage:sumi");
    expect(manifest.contributes.configuration.properties["sumi.server.path"].default).toBe("");
    expect(manifest.icon).toBe("images/icon.png");
    expect(manifest.contributes.snippets).toBeUndefined();
    expect(manifest.contributes.languages[0].extensions).toEqual([".su"]);
    expect(manifest.contributes.languages[0].icon).toEqual({
      light: "./images/file-icon-light.svg",
      dark: "./images/file-icon-dark.svg",
    });
    expect(manifest.contributes.grammars[0].scopeName).toBe("source.sumi");
    const lightIcon = Bun.file(path.join(root, "images", "file-icon-light.svg"));
    const darkIcon = Bun.file(path.join(root, "images", "file-icon-dark.svg"));
    expect(await lightIcon.exists()).toBeTrue();
    expect(await darkIcon.exists()).toBeTrue();

    const configuration = await Bun.file(path.join(root, "language-configuration.json")).json();
    expect(configuration.comments.lineComment).toBe("//");
    expect(configuration.brackets).toEqual([
      ["{", "}"],
      ["(", ")"],
    ]);
  });
});

describe("TextMate grammar", () => {
  test("scopes bounded for loops without matching keyword prefixes", () => {
    const lines = tokenize("for i in first..finish { forward(index) }");
    for (const keyword of ["for", "in"]) {
      expect(scopesAt(lines, 0, keyword)).toContain("keyword.control.sumi");
    }
    expect(scopesAt(lines, 0, "..")).toContain("keyword.operator.sumi");
    expect(scopesAt(lines, 0, "index")).toContain("variable.other.readwrite.sumi");
    expect(scopesAt(lines, 0, "forward")).toContain("entity.name.function.call.sumi");
  });

  test("scopes the current declarations, assignment, literals, calls, and comments", () => {
    const lines = tokenize(
      [
        "fn twice(x: int) -> int {",
        "  let mut answer = x * 2 // doubled",
        "  answer = twice(answer)",
        "  return answer",
        "}",
      ].join("\n"),
    );

    expect(scopesAt(lines, 0, "fn")).toContain("storage.type.function.sumi");
    expect(scopesAt(lines, 0, "twice")).toContain("entity.name.function.sumi");
    expect(scopesAt(lines, 0, "int")).toContain("entity.name.type.sumi");
    expect(scopesAt(lines, 1, "let")).toContain("keyword.declaration.sumi");
    expect(scopesAt(lines, 1, "mut")).toContain("storage.modifier.sumi");
    expect(scopesAt(lines, 1, "answer")).toContain("variable.other.definition.sumi");
    expect(scopesAt(lines, 1, "2")).toContain("constant.numeric.integer.sumi");
    expect(scopesAt(lines, 1, "//")).toContain("comment.line.double-slash.sumi");
    expect(scopesAt(lines, 2, "=")).toContain("keyword.operator.sumi");
    expect(scopesAt(lines, 2, "twice")).toContain("entity.name.function.call.sumi");
    expect(scopesAt(lines, 3, "return")).toContain("keyword.control.sumi");
  });

  test("keeps braces and names inside strings as string text", () => {
    const lines = tokenize(String.raw`"hello, {name}\n\t\"quoted\" \\ escaped"`);

    expect(scopesAt(lines, 0, "name")).toContain("string.quoted.double.sumi");
    expect(scopesAt(lines, 0, String.raw`\n`)).toContain("constant.character.escape.sumi");
    expect(scopesAt(lines, 0, String.raw`\"`)).toContain("constant.character.escape.sumi");
  });

  test("scopes the compiler's string escapes", () => {
    const lines = tokenize(String.raw`"\n \r \t \\ \" \0"`);
    const valid = [
      String.raw`\n`,
      String.raw`\r`,
      String.raw`\t`,
      String.raw`\\`,
      String.raw`\"`,
      String.raw`\0`,
    ];
    for (const escape of valid) {
      expect(scopesAt(lines, 0, escape)).toContain("constant.character.escape.sumi");
    }
  });

  test("ends an unterminated string at its line", () => {
    const lines = tokenize('"unterminated\nlet next = 1');
    expect(scopesAt(lines, 1, "let")).toContain("keyword.declaration.sumi");
    expect(scopesAt(lines, 1, "next")).toContain("variable.other.definition.sumi");
  });
});

const tokenDeclaration = await Bun.file(
  path.join(root, "..", "..", "crates", "lexer", "src", "kind.rs"),
).text();
const keywords = [...tokenDeclaration.matchAll(/^\s+\w+: keyword "([^"]+)",$/gm)].map(
  (match) => match[1],
);
const punctuation = [...tokenDeclaration.matchAll(/^\s+\w+: punct '(.)',$/gm)].map(
  (match) => match[1],
);

describe("compiler vocabulary synchronization", () => {
  test("reads every keyword and punctuation from the lexer declaration", () => {
    expect(keywords).toEqual(["_", "else", "false", "fn", "for", "if", "in", "let", "mut", "return", "true"]);
    expect(punctuation).toEqual([
      "(",
      ")",
      "{",
      "}",
      ",",
      ":",
      ".",
      "=",
      "<",
      ">",
      "!",
      "+",
      "-",
      "*",
      "/",
      "%",
      "&",
      "|",
    ]);
  });

  test.each(keywords)("scopes the compiler keyword %s", (keyword) => {
    expect(scopesAt(tokenize(keyword), 0, keyword).length).toBeGreaterThan(1);
  });

  test.each(punctuation)("scopes the compiler punctuation %s", (punctuation) => {
    expect(scopesAt(tokenize(punctuation), 0, punctuation).length).toBeGreaterThan(1);
  });
});
