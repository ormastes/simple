#!/usr/bin/env node
// Launcher for T32 MCP Server native binary.
// This is a thin wrapper for npm distribution — the actual server
// is a compiled native binary, not a Node.js application.

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

function getBinaryName() {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  return `t32_mcp_server${ext}`;
}

function findBinary() {
  const name = getBinaryName();

  // 1. Check native/ directory (npm postinstall download location)
  const nativePath = path.join(__dirname, '..', 'native', name);
  if (fs.existsSync(nativePath)) return nativePath;

  // 2. Check project checkout bin/ directory
  const projectPath = path.join(__dirname, '..', '..', '..', 'bin', name);
  if (fs.existsSync(projectPath)) return projectPath;

  // 3. Check bin/release/ directory
  const releasePath = path.join(__dirname, '..', '..', '..', 'bin', 'release', name);
  if (fs.existsSync(releasePath)) return releasePath;

  // 4. Fall back to PATH
  return name;
}

const binary = findBinary();

const child = spawn(binary, process.argv.slice(2), {
  stdio: 'inherit',
  env: {
    ...process.env,
    SIMPLE_LOG: process.env.SIMPLE_LOG || 'error'
  }
});

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: T32 MCP Server binary not found at: ${binary}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching T32 MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => process.exit(code ?? 1));
