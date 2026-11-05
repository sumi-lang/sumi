import path from "node:path";

import { describe, expect, test } from "bun:test";
import oniguruma from "vscode-oniguruma";
import textmate from "vscode-textmate";

const root = path.join(import.meta.dir, "..");

describe("extension contributions", () => {
  test("registers Sumi and its language server", async () => {
    const manifest = await Bun.file(path.join(root, "package.json")).json();
    expect(manifest.main).toBe("./out/extension.js");
    expect(manifest.extensionKind).toEqual(["workspace"]);
    expect(manifest.activationEvents).toContain("onLanguage:sumi");
    expect(manifest.contributes.configuration.properties["sumi.server.path"].default).toBe("");
    expect(manifest.icon).toBe("images/icon.png");
    expect(manifest.contributes.snippets).toBeUndefined();
    expect(manifest.contributes.commands).toEqual([
      { command: "sumi.restartServer", title: "Restart Language Server", category: "Sumi" },
    ]);
    expect(manifest.contributes.languages[0].extensions).toEqual([".su"]);
    expect(manifest.contributes.languages[0].icon).toEqual({
      light: "./images/file-icon-light.svg",
      dark: "./images/file-icon-dark.svg",
    });
    expect(manifest.contributes.configurationDefaults["[sumi]"]["editor.semanticHighlighting.enabled"]).toBeTrue();
    expect(await Bun.file(path.join(root, "images", "file-icon-light.svg")).exists()).toBeTrue();
    expect(await Bun.file(path.join(root, "images", "file-icon-dark.svg")).exists()).toBeTrue();

    const configuration = await Bun.file(path.join(root, "language-configuration.json")).json();
    expect(configuration.comments.lineComment).toBe("//");
    expect(configuration.brackets).toEqual([
      ["{", "}"],
      ["(", ")"],
    ]);
  });

  test("continues a whole-line comment on Enter, not a trailing or an empty one", async () => {
    const configuration = await Bun.file(path.join(root, "language-configuration.json")).json();
    const [rule] = configuration.onEnterRules;
    const before = new RegExp(rule.beforeText);
    expect(before.test("    // a note")).toBeTrue();
    expect(before.test("// a note")).toBeTrue();
    expect(before.test("let x = 1 // c")).toBeFalse();
    expect(before.test("    //")).toBeFalse();
    expect(before.test("    // ")).toBeFalse();
    expect(rule.action).toEqual({ indent: "none", appendText: "// " });
  });

  test("supplies comment metadata without duplicating compiler highlighting", async () => {
    await oniguruma.loadWASM(await Bun.file(
      path.join(root, "node_modules", "vscode-oniguruma", "release", "onig.wasm"),
    ).arrayBuffer());
    const registry = new textmate.Registry({
      onigLib: Promise.resolve({
        createOnigScanner: (patterns: string[]) => new oniguruma.OnigScanner(patterns),
        createOnigString: (text: string) => new oniguruma.OnigString(text),
      }),
      loadGrammar: async () => Bun.file(path.join(root, "syntaxes", "sumi.tmLanguage.json")).json(),
    });
    try {
      const grammar = await registry.loadGrammar("source.sumi");
      expect(grammar).not.toBeNull();
      const source = "fn f(x: int) = x / 2 // { ignored }";
      const tokens = grammar!.tokenizeLine(source, null).tokens;
      expect(tokens.map((token) => [source.slice(token.startIndex, token.endIndex), token.scopes])).toEqual([
        ["fn f(x: int) = x / 2 ", ["source.sumi"]],
        ["// { ignored }", ["source.sumi", "comment.line.double-slash.sumi"]],
      ]);
    } finally {
      registry.dispose();
    }
  });
});
