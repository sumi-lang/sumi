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
  const configured = vscode.workspace.getConfiguration("sumi.server").get<string>("path", "");
  const executable = process.platform === "win32" ? "sumi-lsp.exe" : "sumi-lsp";
  const bundled = context.asAbsolutePath(path.join("server", executable));
  const command = configured || (fs.existsSync(bundled) ? bundled : "sumi-lsp");
  const serverOptions: ServerOptions = { command };
  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      { language: "sumi", scheme: "file" },
      { language: "sumi", scheme: "untitled" },
    ],
  };
  client = new LanguageClient("sumi", "Sumi Language Server", serverOptions, clientOptions);
  context.subscriptions.push(client);
  await client.start();
}

export async function deactivate(): Promise<void> {
  if (client !== undefined) {
    await client.stop();
    client = undefined;
  }
}
