import fs from "node:fs";
import path from "node:path";

import * as vscode from "vscode";
import {
  LanguageClient,
  type LanguageClientOptions,
  type ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  context.subscriptions.push(
    vscode.commands.registerCommand("sumi.restartServer", () => restart(context)),
    vscode.workspace.onDidChangeConfiguration((event) => {
      if (event.affectsConfiguration("sumi.server.path")) {
        void restart(context);
      }
    }),
  );
  await start(context);
}

export async function deactivate(): Promise<void> {
  await stop();
}

// The configured server, else the bundled one, else whatever `sumi-lsp` is on the path.
function serverCommand(context: vscode.ExtensionContext): string {
  const configured = vscode.workspace.getConfiguration("sumi.server").get<string>("path", "");
  const executable = process.platform === "win32" ? "sumi-lsp.exe" : "sumi-lsp";
  const bundled = context.asAbsolutePath(path.join("server", executable));
  return configured || (fs.existsSync(bundled) ? bundled : "sumi-lsp");
}

async function start(context: vscode.ExtensionContext): Promise<void> {
  const serverOptions: ServerOptions = { command: serverCommand(context) };
  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      { language: "sumi", scheme: "file" },
      { language: "sumi", scheme: "untitled" },
    ],
  };
  client = new LanguageClient("sumi", "Sumi Language Server", serverOptions, clientOptions);
  await client.start();
}

async function stop(): Promise<void> {
  const stopping = client;
  client = undefined;
  if (stopping !== undefined) {
    await stopping.stop();
    await stopping.dispose();
  }
}

// A new client, so a changed `sumi.server.path` is read; the old one is stopped first.
async function restart(context: vscode.ExtensionContext): Promise<void> {
  await stop();
  await start(context);
}
