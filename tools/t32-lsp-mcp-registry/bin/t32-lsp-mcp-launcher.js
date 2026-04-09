#!/usr/bin/env node
// Launcher for TRACE32 CMM LSP-MCP Server.
// Finds the Simple runtime from the downloaded bootstrap package
// and runs the T32 LSP-MCP server entry point.

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

const T32_ROOT_REL = 'examples/10_tooling/trace32_tools';

function getWrapperPath(repoRoot) {
  const ext = os.platform() === 'win32' ? '.cmd' : '';
  return path.join(repoRoot, 'bin', `t32_lsp_mcp_server${ext}`);
}

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
  const nativeBinary = path.join(projectRoot, 'src', 'compiler_rust', 'target', 'release', `simple${ext}`);
  if (fs.existsSync(nativeBinary)) {
    return { binary: nativeBinary, repoRoot: projectRoot };
  }
  const devSymlink = path.join(projectRoot, 'bin', `simple${ext}`);
  if (fs.existsSync(devSymlink)) {
    return { binary: devSymlink, repoRoot: projectRoot };
  }

  // 3. Fall back to PATH
  return { binary: `simple${ext}`, repoRoot: process.cwd() };
}

const { binary, repoRoot } = findRuntime();
const wrapperPath = getWrapperPath(repoRoot);
const t32Root = path.join(repoRoot, T32_ROOT_REL);
const env = {
  ...process.env,
  SIMPLE_BINARY: binary,
  SIMPLE_LIB: process.env.SIMPLE_LIB || t32Root,
  SIMPLE_RUNTIME: process.env.SIMPLE_RUNTIME || binary,
  T32_LSP_MCP_TOOL_RUNNER: process.env.T32_LSP_MCP_TOOL_RUNNER ||
    path.join(repoRoot, T32_ROOT_REL, 't32_lsp_mcp', 'tool_runner.spl'),
  T32_LSP_MCP_TOOL_DAEMON: process.env.T32_LSP_MCP_TOOL_DAEMON ||
    path.join(repoRoot, T32_ROOT_REL, 'cmm_lsp', 'mcp_daemon.spl'),
  T32_LSP_MCP_TOOL_DAEMON_DIR: process.env.T32_LSP_MCP_TOOL_DAEMON_DIR ||
    path.join(os.tmpdir(), 't32_lsp_mcp_shared'),
  SIMPLE_LOG: process.env.SIMPLE_LOG || 'error',
  RUST_LOG: process.env.RUST_LOG || 'error'
};

const child = fs.existsSync(wrapperPath)
  ? spawn(wrapperPath, process.argv.slice(2), { stdio: 'inherit', env })
  : spawn(binary, [
      'run',
      path.join(repoRoot, T32_ROOT_REL, 't32_lsp_mcp', 'main.spl'),
      ...process.argv.slice(2)
    ], {
      stdio: 'inherit',
      env
    });

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: Simple runtime not found at: ${binary}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching T32 LSP-MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => process.exit(code ?? 1));
