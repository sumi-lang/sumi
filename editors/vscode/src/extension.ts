import fs from "node:fs";
import path from "node:path";

import * as vscode from "vscode";
import {
  CloseAction,
  type CloseHandlerResult,
  ErrorAction,
  type ErrorHandler,
  type ErrorHandlerResult,
  LanguageClient,
  type LanguageClientOptions,
  type ServerOptions,
  State,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;
let status: vscode.StatusBarItem | undefined;
// Restarts queue behind one another, so the command and a setting change never run two clients.
let restarting: Promise<void> = Promise.resolve();
// The current client's start, settled: a client still starting refuses to stop, which would leave
// its server running with nothing holding it.
let ready: Promise<void> = Promise.resolve();

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  status = vscode.window.createStatusBarItem("sumi.server", vscode.StatusBarAlignment.Left);
  status.name = "Sumi Language Server";
  context.subscriptions.push(
    status,
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

// The item is shown only while the server is not running: starting, stopped, or given up on.
function showStatus(text: string, tooltip: string): void {
  if (status === undefined) return;
  status.text = text;
  status.tooltip = tooltip;
  status.command = "sumi.restartServer";
  status.show();
}

// A server that failed to start or crashed too often is reported with the way back: the restart
// command, and the output with the server's own words.
function report(message: string, output: vscode.OutputChannel): void {
  showStatus("$(warning) Sumi: server stopped", `${message}\nClick to restart the server.`);
  void vscode.window.showErrorMessage(message, "Restart", "Go to output").then((choice) => {
    if (choice === "Restart") void vscode.commands.executeCommand("sumi.restartServer");
    if (choice === "Go to output") output.show(true);
  });
}

// The client's own policy, restarts up to `maxRestarts` times within three minutes, with the
// give-up reported by `report` rather than the client's notice, which offers no restart.
function errorHandler(name: () => string, output: () => vscode.OutputChannel): ErrorHandler {
  const maxRestarts = 4;
  const restarts: number[] = [];
  return {
    error(_error, _message, count): ErrorHandlerResult {
      return { action: count !== undefined && count <= 3 ? ErrorAction.Continue : ErrorAction.Shutdown };
    },
    closed(): CloseHandlerResult {
      restarts.push(Date.now());
      if (restarts.length <= maxRestarts) return { action: CloseAction.Restart };
      if (restarts[restarts.length - 1] - restarts[0] > 3 * 60 * 1000) {
        restarts.shift();
        return { action: CloseAction.Restart };
      }
      report(
        `The ${name()} crashed ${maxRestarts + 1} times in the last 3 minutes and was not restarted.`,
        output(),
      );
      return { action: CloseAction.DoNotRestart, handled: true };
    },
  };
}

async function start(context: vscode.ExtensionContext): Promise<void> {
  const serverOptions: ServerOptions = { command: serverCommand(context) };
  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      { language: "sumi", scheme: "file" },
      { language: "sumi", scheme: "untitled" },
    ],
    errorHandler: errorHandler(
      () => started?.name ?? "Sumi Language Server",
      () => (started as LanguageClient).outputChannel,
    ),
  };
  const started = new LanguageClient("sumi", "Sumi Language Server", serverOptions, clientOptions);
  client = started;
  started.onDidChangeState(({ newState }) => {
    if (client !== started) return;
    if (newState === State.Running) status?.hide();
    else if (newState === State.Starting) {
      showStatus("$(sync~spin) Sumi: starting", "Starting the language server.");
    }
  });
  showStatus("$(sync~spin) Sumi: starting", "Starting the language server.");
  ready = started.start().catch((error: unknown) => {
    if (client !== started) return;
    const reason = error instanceof Error ? error.message : String(error);
    report(`The Sumi language server failed to start: ${reason}`, started.outputChannel);
  });
  await ready;
}

async function stop(): Promise<void> {
  const stopping = client;
  client = undefined;
  await ready;
  // A client that never ran refuses to stop; nothing is running to stop then.
  if (stopping !== undefined) {
    await stopping.dispose().catch(() => undefined);
  }
}

// A new client, so a changed `sumi.server.path` is read; the old one is stopped first.
function restart(context: vscode.ExtensionContext): Promise<void> {
  restarting = restarting.then(stop).then(() => start(context));
  return restarting;
}
