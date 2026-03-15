#!/usr/bin/env node
"use strict";

const { execSync } = require("child_process");
const fs = require("fs");
const path = require("path");
const os = require("os");

const VERSION = require("../package.json").version;
const BIN_DIR = path.join(__dirname, "..", "bin");

const PLATFORMS = {
  "linux-x64": "linux-x86_64",
  "linux-arm64": "linux-aarch64",
  "darwin-x64": "darwin-x86_64",
  "darwin-arm64": "darwin-aarch64",
  "win32-x64": "windows-x86_64",
};

const platform = `${os.platform()}-${os.arch()}`;
const target = PLATFORMS[platform];

if (!target) {
  console.warn(
    `@simple-lang/mcp-server: unsupported platform ${platform}. ` +
    `Please install the Simple compiler manually from https://github.com/ormastes/simple/releases`
  );
  process.exit(0);
}

const REPO = "ormastes/simple";
const BINARY_NAME = os.platform() === "win32" ? "simple.exe" : "simple";
const RELEASE_URL = `https://github.com/${REPO}/releases/download/v${VERSION}/${target}.tar.gz`;

if (!fs.existsSync(BIN_DIR)) {
  fs.mkdirSync(BIN_DIR, { recursive: true });
}

const binPath = path.join(BIN_DIR, BINARY_NAME);
if (fs.existsSync(binPath)) {
  console.log("@simple-lang/mcp-server: binary already exists, skipping download.");
  process.exit(0);
}

console.log(`@simple-lang/mcp-server: downloading Simple compiler for ${target}...`);

try {
  execSync(
    `curl -fsSL "${RELEASE_URL}" | tar xz -C "${BIN_DIR}" --strip-components=1`,
    { stdio: "inherit" }
  );
  if (os.platform() !== "win32") {
    fs.chmodSync(binPath, 0o755);
  }
  console.log("@simple-lang/mcp-server: installed successfully.");
} catch (err) {
  console.warn(
    `@simple-lang/mcp-server: failed to download binary. ` +
    `Please install the Simple compiler manually.\n` +
    `  Download: https://github.com/${REPO}/releases`
  );
  process.exit(0);
}
