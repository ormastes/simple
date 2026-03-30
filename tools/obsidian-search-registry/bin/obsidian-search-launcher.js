#!/usr/bin/env node
// Launcher for Obsidian Search MCP Server native binary.
// This is a thin wrapper for npm distribution — the actual server
// is a compiled native binary, not a Node.js application.

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

function getBinaryName() {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  return `obsidian_search_server${ext}`;
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
    OBSIDIAN_VAULT_PATH: process.env.OBSIDIAN_VAULT_PATH || '',
    SIMPLE_LIB: process.env.SIMPLE_LIB || path.join(__dirname, '..', '..', '..', 'src'),
    SIMPLE_LOG: process.env.SIMPLE_LOG || 'error'
  }
});

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: Obsidian Search Server binary not found at: ${binary}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching Obsidian Search Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => process.exit(code ?? 1));
