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

const grammarPath = path.join(root, "syntaxes", "sumi.tmLanguage.json");
const onigLib = Promise.resolve({
  createOnigScanner: (patterns: string[]) => new OnigScanner(patterns),
  createOnigString: (text: string) => new OnigString(text),
});
const loadGrammar = async (scopeName: string) => {
  expect(scopeName).toBe("source.sumi");
  return Bun.file(grammarPath).json();
};
const registry = new Registry({
  onigLib,
  loadGrammar,
});
const themedRegistry = new Registry({
  onigLib,
  loadGrammar,
  theme: {
    settings: [
      { settings: { foreground: "#111111", background: "#FFFFFF" } },
      { scope: "string", settings: { foreground: "#CC0000" } },
    ],
  },
});
const [loadedGrammar, loadedThemedGrammar] = await Promise.all([
  registry.loadGrammar("source.sumi"),
  themedRegistry.loadGrammar("source.sumi"),
]);
if (loadedGrammar === null || loadedThemedGrammar === null) {
  throw new Error("Sumi TextMate grammar did not load");
}
const grammar = loadedGrammar;
const themedGrammar = loadedThemedGrammar;

type TokenizedLine = { line: string; tokens: IToken[] };

function tokenize(source: string): TokenizedLine[] {
  let state: StateStack | null = null;
  return source.split("\n").map((line) => {
    const result = grammar.tokenizeLine(line, state);
    state = result.ruleStack;
    return { line, tokens: result.tokens };
  });
}

function textStart(line: string, text: string, occurrence: number) {
  let start = -1;
  for (let count = 0, from = 0; count <= occurrence; count += 1) {
    start = line.indexOf(text, from);
    expect(start, `${JSON.stringify(text)} is present`).not.toBe(-1);
    from = start + text.length;
  }
  return start;
}

function foregroundAt(line: string, text: string, occurrence = 0) {
  const start = textStart(line, text, occurrence);
  const encoded = themedGrammar.tokenizeLine2(line, null).tokens;
  for (let index = 0; index < encoded.length; index += 2) {
    const end = index + 2 < encoded.length ? encoded[index + 2] : line.length;
    if (encoded[index] <= start && start < end) {
      const foregroundIndex = (encoded[index + 1] >>> 15) & 0x1ff;
      return themedRegistry.getColorMap()[foregroundIndex];
    }
  }
  throw new Error(`an encoded grammar token covers ${JSON.stringify(text)}`);
}

function scopesAt(tokenized: TokenizedLine[], lineIndex: number, text: string, occurrence = 0) {
  const { line, tokens } = tokenized[lineIndex];
  const start = textStart(line, text, occurrence);
  const token = tokens.find(({ startIndex, endIndex }) => startIndex <= start && start < endIndex);
  expect(token, `a grammar token covers ${JSON.stringify(text)} on line ${lineIndex + 1}`).toBeDefined();
  if (token === undefined) {
    throw new Error("expect().toBeDefined() did not stop the test");
  }
  return token.scopes;
}

describe("extension contributions", () => {
  test("manifest registers a dependency-free Sumi language", async () => {
    const manifest = await Bun.file(path.join(root, "package.json")).json();
    expect(manifest.main).toBeUndefined();
    expect(manifest.icon).toBe("images/icon.png");
    expect(manifest.contributes.snippets).toBeUndefined();
    expect(manifest.contributes.languages[0].extensions).toEqual([".sumi"]);
    expect(manifest.contributes.grammars[0].scopeName).toBe("source.sumi");

    const configuration = await Bun.file(path.join(root, "language-configuration.json")).json();
    expect(configuration.comments.lineComment).toBe("//");
    expect(configuration.brackets).toEqual([
      ["{", "}"],
      ["(", ")"],
    ]);
  });
});

describe("TextMate grammar", () => {
  test("scopes declarations, literals, calls, and comments", () => {
    const lines = tokenize([
      "fn twice(x: int) -> int {",
      "  let mut answer = x * 2 // doubled",
      "  return twice(answer)",
      "}",
    ].join("\n"));

    expect(scopesAt(lines, 0, "fn")).toContain("storage.type.function.sumi");
    expect(scopesAt(lines, 0, "twice")).toContain("entity.name.function.sumi");
    expect(scopesAt(lines, 0, "int")).toContain("entity.name.type.sumi");
    expect(scopesAt(lines, 1, "let")).toContain("keyword.declaration.sumi");
    expect(scopesAt(lines, 1, "mut")).toContain("storage.modifier.sumi");
    expect(scopesAt(lines, 1, "answer")).toContain("variable.other.definition.sumi");
    expect(scopesAt(lines, 1, "2")).toContain("constant.numeric.integer.sumi");
    expect(scopesAt(lines, 1, "//")).toContain("comment.line.double-slash.sumi");
    expect(scopesAt(lines, 2, "return")).toContain("keyword.control.sumi");
    expect(scopesAt(lines, 2, "twice")).toContain("entity.name.function.call.sumi");
  });

  test("distinguishes interpolated, block, and raw strings", () => {
    const source = [
      String.raw`let message = "value {twice(2)} and \n"`,
      "let raw = r#\"literal {not_a_hole}\"#",
      "let plain = r\"raw {still_not_a_hole}\" + 1",
      "let card = \"\"\"",
      "  value {if true { 1 } else { 2 }}",
      "  \"\"\"",
    ].join("\n");
    const lines = tokenize(source);

    expect(scopesAt(lines, 0, "value")).toContain("string.quoted.double.sumi");
    expect(scopesAt(lines, 0, "{")).toContain("meta.interpolation.sumi");
    expect(scopesAt(lines, 0, "twice")).toContain("entity.name.function.call.sumi");
    expect(scopesAt(lines, 0, "2")).toContain("constant.numeric.integer.sumi");
    expect(scopesAt(tokenize('"value {result}"'), 0, "result")).toContain(
      "variable.other.readwrite.sumi",
    );
    expect(scopesAt(lines, 0, "\\n")).toContain("constant.character.escape.sumi");
    expect(scopesAt(lines, 1, "not_a_hole")).toContain("string.quoted.other.raw.sumi");
    expect(scopesAt(lines, 1, "{")).not.toContain("meta.interpolation.sumi");
    expect(scopesAt(lines, 2, "still_not_a_hole")).toContain("string.quoted.other.raw.sumi");
    expect(scopesAt(lines, 2, "{")).not.toContain("meta.interpolation.sumi");
    expect(scopesAt(lines, 2, "1")).toContain("constant.numeric.integer.sumi");
    expect(scopesAt(lines, 4, "if")).toContain("keyword.control.sumi");
    expect(scopesAt(lines, 4, "true")).toContain("constant.language.boolean.sumi");
    expect(scopesAt(lines, 4, "1")).toContain("constant.numeric.integer.sumi");
    expect(scopesAt(lines, 4, "{", 1)).toContain("meta.embedded.expression.sumi");
    expect(scopesAt(lines, 4, "{", 1)).toContain("punctuation.section.block.begin.sumi");
    expect(scopesAt(lines, 5, "\"\"\"")).toContain("string.quoted.double.block.sumi");

    const scopedText = lines.flatMap(({ line, tokens }, lineIndex) =>
      tokens
        .filter(({ scopes }) => scopes.length > 1)
        .map(({ startIndex, endIndex, scopes }) => ({
          line: lineIndex + 1,
          text: line.slice(startIndex, endIndex),
          scopes: scopes.slice(1),
        })),
    );
    expect(scopedText).toMatchSnapshot();
  });

  test("does not inherit string colors inside interpolation holes", () => {
    const line = '"literal {if true { 1 } else { 2 }} tail"';

    expect(foregroundAt(line, "literal")).toBe("#CC0000");
    expect(foregroundAt(line, "if")).toBe("#111111");
    expect(foregroundAt(line, "{", 1)).toBe("#111111");
    expect(foregroundAt(line, "}", 1)).toBe("#111111");
    expect(foregroundAt(line, "tail")).toBe("#CC0000");
  });

  test.each([
    { slashes: 0, interpolates: true },
    { slashes: 1, interpolates: false },
    { slashes: 2, interpolates: true },
    { slashes: 3, interpolates: false },
    { slashes: 4, interpolates: true },
  ])("uses backslash parity before a hole ($slashes slashes)", ({ slashes, interpolates }) => {
    const lines = tokenize(`"${"\\".repeat(slashes)}{value}"`);
    expect(scopesAt(lines, 0, "{").includes("meta.interpolation.sumi")).toBe(interpolates);
    expect(scopesAt(lines, 0, "value").includes("variable.other.readwrite.sumi")).toBe(
      interpolates,
    );
  });

  test("recognizes escaped opening and closing braces", () => {
    const lines = tokenize(String.raw`"\{ \}"`);
    expect(scopesAt(lines, 0, String.raw`\{`)).toContain("constant.character.escape.sumi");
    expect(scopesAt(lines, 0, String.raw`\}`)).toContain("constant.character.escape.sumi");
  });

  test.each([
    ["plain", 'let raw = r"unterminated'],
    ["fenced", 'let raw = r#"unterminated'],
  ])("recovers after an unterminated %s raw string", (_kind, openingLine) => {
    const lines = tokenize(`${openingLine}\nlet next = 1`);
    expect(scopesAt(lines, 1, "let")).toContain("keyword.declaration.sumi");
    expect(scopesAt(lines, 1, "1")).toContain("constant.numeric.integer.sumi");
    expect(scopesAt(lines, 1, "next")).not.toContain("string.quoted.other.raw.sumi");
  });

  test("bounds malformed block-string holes to one line", () => {
    const lines = tokenize(
      ['let card = """', "  before {if true { 1", "  after", '  """'].join("\n"),
    );
    expect(scopesAt(lines, 2, "after")).toContain("string.quoted.double.block.sumi");
    expect(scopesAt(lines, 2, "after")).not.toContain("meta.interpolation.sumi");
    expect(scopesAt(lines, 3, '"""')).toContain("punctuation.definition.string.end.sumi");

    const ordinaryBlock = tokenize(["if true {", "  let value = 1", "}"].join("\n"));
    expect(scopesAt(ordinaryBlock, 1, "value")).toContain("meta.block.sumi");
  });

  test("distinguishes valid floats from a leading-dot expression", () => {
    const lines = tokenize(".5 0.5 1e3");
    expect(scopesAt(lines, 0, ".")).toContain("keyword.operator.sumi");
    expect(scopesAt(lines, 0, "5")).toContain("constant.numeric.integer.sumi");
    expect(scopesAt(lines, 0, "0.5")).toContain("constant.numeric.float.sumi");
    expect(scopesAt(lines, 0, "1e3")).toContain("constant.numeric.float.sumi");
  });

  test("keeps combining marks in identifiers and scopes the discard", () => {
    const decomposed = "cafe\u0301";
    const lines = tokenize(`let ${decomposed} = _`);
    expect(scopesAt(lines, 0, "\u0301")).toContain("variable.other.definition.sumi");
    expect(scopesAt(lines, 0, "_")).toContain("keyword.other.discard.sumi");
  });
});

const declaredGrammar = await Bun.file(path.join(root, "..", "..", "sumi.grammar")).text();
const keywords = [...declaredGrammar.matchAll(/^token \w+ keyword "([^"]+)"/gm)]
  .map((match) => match[1])
  .filter((keyword) => keyword !== "_");

describe("grammar synchronization", () => {
  test("the initial reserved keyword set is explicit", () => {
    expect(keywords).toEqual(["else", "false", "fn", "if", "let", "mut", "return", "true"]);
  });

  test.each(keywords)("scopes the reserved keyword %s", (keyword) => {
    const lines = tokenize(keyword);
    expect(
      scopesAt(lines, 0, keyword).some((scope) =>
        /^(?:constant\.language|keyword|storage\.)/.test(scope),
      ),
    ).toBeTrue();
  });
});
