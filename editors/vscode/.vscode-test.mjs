import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { defineConfig } from "@vscode/test-cli";

const extension = path.dirname(fileURLToPath(import.meta.url));
const generated = path.join(extension, ".vscode-test", `run-${process.pid}`);
const workspace = path.join(generated, "workspace");
const executable = process.platform === "win32" ? "sumi-lsp.exe" : "sumi-lsp";
const server = path.join(extension, "server", executable);
fs.mkdirSync(workspace, { recursive: true });
fs.mkdirSync(path.dirname(server), { recursive: true });
fs.copyFileSync(path.resolve(extension, "../../target/debug", executable), server);
fs.chmodSync(server, 0o755);

process.on("exit", () => {
  fs.rmSync(generated, { recursive: true, force: true });
  fs.rmSync(path.dirname(server), { recursive: true, force: true });
});

export default defineConfig({
  files: "out/test/**/*.test.js",
  version: "1.105.1",
  workspaceFolder: workspace,
  launchArgs: [
    "--disable-extensions",
    `--user-data-dir=${path.join(generated, "profile")}`,
    `--extensions-dir=${path.join(generated, "extensions")}`,
  ],
  env: {
    SUMI_TEST_WORKSPACE: workspace,
  },
  mocha: {
    ui: "tdd",
    timeout: 20_000,
  },
});
