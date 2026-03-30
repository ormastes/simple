#!/usr/bin/env node
// Launcher for Obsidian LSP-MCP Server.
// Finds the Simple runtime from the downloaded bootstrap package
// and runs the Obsidian search entry point.
// Modes: "bridge" (default) or "mcp"

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

function findRuntime() {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const nativeDir = path.join(__dirname, '..', 'native');

  // 1. Check extracted bootstrap package
  if (fs.existsSync(nativeDir)) {
    const entries = fs.readdirSync(nativeDir).filter(e => e.startsWith('simple-bootstrap-'));
    if (entries.length > 0) {
      const pkgDir = path.join(nativeDir, entries[0]);
      const binary = path.join(pkgDir, 'bin', `simple${ext}`);
      if (fs.existsSync(binary)) {
        return { binary, repoRoot: pkgDir };
      }
    }
  }

  // 2. Check project checkout (development)
  const projectRoot = path.join(__dirname, '..', '..', '..');
  const devBinary = path.join(projectRoot, 'bin', 'release', `simple${ext}`);
  if (fs.existsSync(devBinary)) {
    return { binary: devBinary, repoRoot: projectRoot };
  }

  // 3. Fall back to PATH
  return { binary: `simple${ext}`, repoRoot: process.cwd() };
}

// Parse mode from first argument
const args = process.argv.slice(2);
let mode = 'bridge';
const passArgs = [];
if (args.length > 0 && (args[0] === 'bridge' || args[0] === 'mcp')) {
  mode = args[0];
  passArgs.push(...args.slice(1));
} else {
  passArgs.push(...args);
}

const { binary, repoRoot } = findRuntime();

const entryFile = mode === 'mcp'
  ? 'examples/obsidian-search/src/main.spl'
  : 'examples/obsidian-search/src/main_bridge.spl';
const entryPath = path.join(repoRoot, entryFile);

// SIMPLE_LIB needs both obsidian-search/src and the main src
const sep = os.platform() === 'win32' ? ';' : ':';
const simpleLib = [
  path.join(repoRoot, 'examples', 'obsidian-search', 'src'),
  path.join(repoRoot, 'src')
].join(sep);

const child = spawn(binary, [entryPath, ...passArgs], {
  stdio: 'inherit',
  env: {
    ...process.env,
    SIMPLE_LIB: simpleLib,
    SIMPLE_BINARY: binary,
    OBSIDIAN_VAULT_PATH: process.env.OBSIDIAN_VAULT_PATH || '',
    SIMPLE_LOG: process.env.SIMPLE_LOG || 'error',
    RUST_LOG: process.env.RUST_LOG || 'error'
  }
});

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: Simple runtime not found at: ${binary}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching Obsidian LSP-MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => process.exit(code ?? 1));
