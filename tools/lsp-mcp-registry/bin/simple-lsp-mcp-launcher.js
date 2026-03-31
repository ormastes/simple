#!/usr/bin/env node
// Launcher for Simple LSP-MCP Server.
// Finds the Simple runtime from the downloaded bootstrap package
// and runs the LSP-MCP bridge entry point.

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

const ENTRY = 'src/app/simple_lsp_mcp/main.spl';

function findRuntime() {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const nativeDir = path.join(__dirname, '..', 'native');

  // 1. Check extracted bootstrap package
  if (fs.existsSync(nativeDir)) {
    const entries = fs.readdirSync(nativeDir).filter(e => e.startsWith('simple-bootstrap-'));
    if (entries.length > 0) {
      const pkgDir = path.join(nativeDir, entries[0]);
      // Primary: bin/simple (correct packaging)
      const binary = path.join(pkgDir, 'bin', `simple${ext}`);
      if (fs.existsSync(binary)) {
        return { binary, repoRoot: pkgDir };
      }
      // Fallback: src/compiler_rust/bin/release/simple (legacy SPK layout)
      const legacyBinary = path.join(pkgDir, 'src', 'compiler_rust', 'bin', 'release', `simple${ext}`);
      if (fs.existsSync(legacyBinary)) {
        return { binary: legacyBinary, repoRoot: pkgDir };
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

const { binary, repoRoot } = findRuntime();
const entryPath = path.join(repoRoot, ENTRY);

const child = spawn(binary, [entryPath, ...process.argv.slice(2)], {
  stdio: 'inherit',
  env: {
    ...process.env,
    SIMPLE_LIB: path.join(repoRoot, 'src'),
    SIMPLE_BINARY: binary,
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
    process.stderr.write(`Error launching Simple LSP-MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => process.exit(code ?? 1));
