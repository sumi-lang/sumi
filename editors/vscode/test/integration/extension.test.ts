import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";

import * as vscode from "vscode";

const timeoutMs = 15_000;
let workspace: string;

suite("Sumi extension", () => {
  suiteSetup(() => {
    const configuredWorkspace = process.env.SUMI_TEST_WORKSPACE;
    assert.ok(configuredWorkspace, "the test CLI config supplies a workspace");
    workspace = configuredWorkspace;
  });

  suiteTeardown(async () => {
    await vscode.commands.executeCommand("workbench.action.closeAllEditors");
  });

  test("activates and publishes saved diagnostics", async () => {
    const extension = vscode.extensions.getExtension("sumi-lang.sumi-language");
    assert.ok(extension, "the Sumi development extension is installed");
    assert.equal(extension.isActive, false, "the extension starts inactive");

    const document = await openSaved("activation.su", "fn main() = 01");
    assert.equal(document.languageId, "sumi");
    const diagnostics = await waitForDiagnostics(
      document.uri,
      (current) => hasCode(current, "syntax/noncanonical-number"),
      "saved leading-zero diagnostic",
    );
    assert.equal(extension.isActive, true, "opening a Sumi file activates the extension");
    assertDiagnostic(diagnostics, "syntax/noncanonical-number", 12, 13);
  });

  test("applies a quick fix and clears diagnostics", async () => {
    const document = await openSaved("quick-fix.su", "fn main() = 01");
    await waitForDiagnostics(
      document.uri,
      (diagnostics) => hasCode(diagnostics, "syntax/noncanonical-number"),
      "quick-fix diagnostic",
    );
    const actions = await vscode.commands.executeCommand<(vscode.CodeAction | vscode.Command)[]>(
      "vscode.executeCodeActionProvider",
      document.uri,
      new vscode.Range(0, 12, 0, 13),
      vscode.CodeActionKind.QuickFix.value,
    );
    const quickFix = actions.find(
      (action): action is vscode.CodeAction =>
        action instanceof vscode.CodeAction && action.title === "remove the leading zeros",
    );
    assert.ok(quickFix?.edit, "the exact compiler quick fix is offered with an edit");
    assert.equal(await vscode.workspace.applyEdit(quickFix.edit), true);
    assert.equal(document.getText(), "fn main() = 1");
    await waitForDiagnostics(document.uri, (diagnostics) => diagnostics.length === 0, "quick-fix clearing");
  });

  test("updates semantic diagnostics after changes", async () => {
    const document = await openSaved("changes.su", "fn main() = 1");
    await waitForDiagnostics(document.uri, (diagnostics) => diagnostics.length === 0, "clean source");
    await replace(document, "fn main() = missing");
    const diagnostics = await waitForDiagnostics(
      document.uri,
      (current) => hasCode(current, "semantic/unknown-name"),
      "semantic diagnostic after an edit",
    );
    assertDiagnostic(diagnostics, "semantic/unknown-name", 12, 19);
  });

  test("formats a document", async () => {
    const document = await openSaved("format.su", "fn  main()=1");
    const formatting = await vscode.commands.executeCommand<vscode.TextEdit[]>(
      "vscode.executeFormatDocumentProvider",
      document.uri,
      { tabSize: 4, insertSpaces: true },
    );
    assert.ok(formatting.length > 0, "formatting returns concrete edits");
    const formatEdit = new vscode.WorkspaceEdit();
    for (const edit of formatting) formatEdit.replace(document.uri, edit.range, edit.newText);
    assert.equal(await vscode.workspace.applyEdit(formatEdit), true);
    assert.equal(document.getText(), "fn main() = 1\n");
  });

  test("updates diagnostics for an untitled document", async () => {
    const document = await vscode.workspace.openTextDocument({
      language: "sumi",
      content: "fn main() = 01",
    });
    assert.equal(document.isUntitled, true);
    const leadingZero = await waitForDiagnostics(
      document.uri,
      (diagnostics) => hasCode(diagnostics, "syntax/noncanonical-number"),
      "untitled leading-zero diagnostic",
    );
    assertDiagnostic(leadingZero, "syntax/noncanonical-number", 12, 13);

    await replace(document, "fn main() = 1");
    await waitForDiagnostics(document.uri, (diagnostics) => diagnostics.length === 0, "untitled clearing");
    await replace(document, "fn main() = missing");
    const semantic = await waitForDiagnostics(
      document.uri,
      (diagnostics) => hasCode(diagnostics, "semantic/unknown-name"),
      "untitled semantic update",
    );
    assertDiagnostic(semantic, "semantic/unknown-name", 12, 19);
  });

  test("completes the names in scope", async () => {
    const document = await openSaved(
      "completion.su",
      "fn double(x: int) -> int = x + x\nfn main() -> int {\n    let total = 1\n    tot\n}\n",
    );
    await waitForDiagnostics(
      document.uri,
      (diagnostics) => hasCode(diagnostics, "semantic/unknown-name"),
      "completion diagnostic",
    );
    const completions = await vscode.commands.executeCommand<vscode.CompletionList>(
      "vscode.executeCompletionItemProvider",
      document.uri,
      new vscode.Position(3, 7),
    );
    const labels = completions.items.map((item) =>
      typeof item.label === "string" ? item.label : item.label.label,
    );
    assert.ok(labels.includes("total"), `the local is offered: ${labels.join(", ")}`);
    assert.ok(labels.includes("double"), `the function is offered: ${labels.join(", ")}`);
    assert.ok(labels.includes("let"), `a statement keyword is offered: ${labels.join(", ")}`);
    const double = completions.items.find(
      (item) => (typeof item.label === "string" ? item.label : item.label.label) === "double",
    );
    assert.ok(double);
    assert.equal(double.kind, vscode.CompletionItemKind.Function);
    assert.equal(double.detail, "fn(int) -> int");
    assert.ok(double.insertText instanceof vscode.SnippetString, "a call inserts as a snippet");
    assert.equal(double.insertText.value, "double($0)");
  });

  test("follows a name to its definition, its references, and a rename", async () => {
    const document = await openSaved(
      "navigation.su",
      "fn double(x: int) -> int = x + x\nfn main() -> int {\n    let x = double(2)\n    x\n}\n",
    );
    await waitForDiagnostics(document.uri, (diagnostics) => diagnostics.length === 0, "clean source");
    const definitions = await vscode.commands.executeCommand<vscode.Location[]>(
      "vscode.executeDefinitionProvider",
      document.uri,
      new vscode.Position(2, 14),
    );
    assert.equal(definitions.length, 1);
    assert.deepEqual(definitions[0].range, new vscode.Range(0, 3, 0, 9));
    const references = await vscode.commands.executeCommand<vscode.Location[]>(
      "vscode.executeReferenceProvider",
      document.uri,
      new vscode.Position(0, 5),
    );
    assert.deepEqual(
      references.map((location) => location.range),
      [new vscode.Range(0, 3, 0, 9), new vscode.Range(2, 12, 2, 18)],
    );
    const rename = await vscode.commands.executeCommand<vscode.WorkspaceEdit>(
      "vscode.executeDocumentRenameProvider",
      document.uri,
      new vscode.Position(0, 27),
      "n",
    );
    assert.equal(await vscode.workspace.applyEdit(rename), true);
    assert.equal(
      document.getText(),
      "fn double(n: int) -> int = n + n\nfn main() -> int {\n    let x = double(2)\n    x\n}\n",
    );
    await assert.rejects(
      async () =>
        vscode.commands.executeCommand(
          "vscode.executeDocumentRenameProvider",
          document.uri,
          new vscode.Position(0, 27),
          "main",
        ),
      /already named `main`/,
      "a rename to a function's name is refused with its reason",
    );
  });

  test("hovers a name and hints inferred types and argument names", async () => {
    const document = await openSaved(
      "hover.su",
      "fn double(x: int) -> int = x + x\nfn main() -> int {\n    let y = double(2)\n    y\n}\n",
    );
    await waitForDiagnostics(document.uri, (diagnostics) => diagnostics.length === 0, "clean source");
    const hovers = await vscode.commands.executeCommand<vscode.Hover[]>(
      "vscode.executeHoverProvider",
      document.uri,
      new vscode.Position(2, 14),
    );
    assert.equal(hovers.length, 1);
    const content = hovers[0].contents[0];
    assert.ok(content instanceof vscode.MarkdownString);
    assert.equal(
      content.value,
      "```sumi\nfn double(x: int) -> int\n```\n\n```\nx ∈ [2, 2]\nresult ∈ [4, 4]\n```",
    );
    assert.deepEqual(hovers[0].range, new vscode.Range(2, 12, 2, 18));
    const hints = await vscode.commands.executeCommand<vscode.InlayHint[]>(
      "vscode.executeInlayHintProvider",
      document.uri,
      new vscode.Range(0, 0, 5, 0),
    );
    assert.deepEqual(
      hints.map((hint) => [hint.position.line, hint.position.character, hint.label, hint.kind]),
      [
        [2, 9, ": int", vscode.InlayHintKind.Type],
        [2, 19, "x:", vscode.InlayHintKind.Parameter],
      ],
    );
  });

  test("highlights the occurrences of a name", async () => {
    const document = await openSaved(
      "highlight.su",
      "fn main() -> int {\n    let mut total = 1\n    total = total + 1\n    total\n}\n",
    );
    await waitForDiagnostics(document.uri, (diagnostics) => diagnostics.length === 0, "clean source");
    const highlights = await vscode.commands.executeCommand<vscode.DocumentHighlight[]>(
      "vscode.executeDocumentHighlights",
      document.uri,
      new vscode.Position(3, 6),
    );
    assert.deepEqual(
      highlights.map((highlight) => [highlight.range.start.line, highlight.kind]),
      [
        [1, vscode.DocumentHighlightKind.Write],
        [2, vscode.DocumentHighlightKind.Write],
        [2, vscode.DocumentHighlightKind.Read],
        [3, vscode.DocumentHighlightKind.Read],
      ],
    );
  });

  test("returns recovered symbols for incomplete input", async () => {
    const document = await openSaved("incomplete.su", "fn unfinished() = {");
    const diagnostics = await waitForDiagnostics(
      document.uri,
      (current) => hasCode(current, "syntax/expected-token"),
      "incomplete syntax diagnostic",
    );
    assert.ok(hasCode(diagnostics, "syntax/expected-token"));
    const symbols = await vscode.commands.executeCommand<
      (vscode.DocumentSymbol | vscode.SymbolInformation)[]
    >("vscode.executeDocumentSymbolProvider", document.uri);
    const unfinished = symbols.find((symbol) => symbol.name === "unfinished");
    assert.ok(unfinished, "recovered syntax retains the incomplete function symbol");
    assert.equal(unfinished.kind, vscode.SymbolKind.Function);
  });
});

async function openSaved(name: string, text: string): Promise<vscode.TextDocument> {
  const file = path.join(workspace, name);
  fs.writeFileSync(file, text);
  return vscode.workspace.openTextDocument(file);
}

async function replace(document: vscode.TextDocument, text: string): Promise<void> {
  const edit = new vscode.WorkspaceEdit();
  edit.replace(
    document.uri,
    new vscode.Range(document.positionAt(0), document.positionAt(document.getText().length)),
    text,
  );
  assert.equal(await vscode.workspace.applyEdit(edit), true, `edit ${document.uri.toString()}`);
  assert.equal(document.getText(), text);
}

async function waitForDiagnostics(
  uri: vscode.Uri,
  predicate: (diagnostics: readonly vscode.Diagnostic[]) => boolean,
  label: string,
): Promise<readonly vscode.Diagnostic[]> {
  const current = vscode.languages.getDiagnostics(uri);
  if (predicate(current)) return current;
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      subscription.dispose();
      reject(
        new Error(
          `timed out waiting for ${label}; diagnostics: ${describe(vscode.languages.getDiagnostics(uri))}`,
        ),
      );
    }, timeoutMs);
    const subscription = vscode.languages.onDidChangeDiagnostics((event) => {
      if (!event.uris.some((changed) => changed.toString() === uri.toString())) return;
      const diagnostics = vscode.languages.getDiagnostics(uri);
      if (!predicate(diagnostics)) return;
      clearTimeout(timer);
      subscription.dispose();
      resolve(diagnostics);
    });
  });
}

function assertDiagnostic(
  diagnostics: readonly vscode.Diagnostic[],
  expectedCode: string,
  start: number,
  end: number,
): void {
  const diagnostic = diagnostics.find((candidate) => code(candidate) === expectedCode);
  assert.ok(diagnostic, `diagnostic ${expectedCode} is present: ${describe(diagnostics)}`);
  assert.equal(diagnostic.source, "sumi");
  assert.equal(diagnostic.severity, vscode.DiagnosticSeverity.Error);
  assert.deepEqual(diagnostic.range, new vscode.Range(0, start, 0, end));
}

function hasCode(diagnostics: readonly vscode.Diagnostic[], expected: string): boolean {
  return diagnostics.some((diagnostic) => code(diagnostic) === expected);
}

function code(diagnostic: vscode.Diagnostic): string | number | undefined {
  return typeof diagnostic.code === "object" ? diagnostic.code.value : diagnostic.code;
}

function describe(diagnostics: readonly vscode.Diagnostic[]): string {
  return JSON.stringify(
    diagnostics.map((diagnostic) => ({
      code: code(diagnostic),
      message: diagnostic.message,
      range: diagnostic.range,
    })),
  );
}
