#!/usr/bin/env node
// Launcher for TRACE32 CMM LSP-MCP Server.
// Prefer the generated wrapper so the registry package matches the repo's
// supported runtime-selection path.
// Hosted `simple run .../main.spl` fallback is legacy-only and must be opted
// into explicitly with SIMPLE_ALLOW_HOSTED_FALLBACK=1.

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

const T32_ROOT_REL = 'examples/10_tooling/trace32_tools';
const ENTRY = path.join(T32_ROOT_REL, 't32_lsp_mcp', 'main.spl');

function allowHostedFallback() {
  return process.env.SIMPLE_ALLOW_HOSTED_FALLBACK === '1';
}

function getWrapperPath(repoRoot) {
  const ext = os.platform() === 'win32' ? '.cmd' : '';
  return path.join(repoRoot, 'bin', `t32_lsp_mcp_server${ext}`);
}

function resolveRuntime(rootDir) {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const candidates = [
    path.join(rootDir, 'bin', `simple${ext}`),
    path.join(rootDir, 'bin', 'release', `simple${ext}`),
    path.join(rootDir, 'src', 'compiler_rust', 'target', 'bootstrap', `simple${ext}`),
    path.join(rootDir, 'src', 'compiler_rust', 'target', 'release', `simple${ext}`),
    path.join(rootDir, 'src', 'compiler_rust', 'bin', 'release', `simple${ext}`)
  ];
  for (const candidate of candidates) {
    if (fs.existsSync(candidate)) {
      return candidate;
    }
  }
  return null;
}

function findLaunchTarget() {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const nativeDir = path.join(__dirname, '..', 'native');
  const projectRoot = path.join(__dirname, '..', '..', '..');
  const sourceRoot = process.env.SIMPLE_SOURCE_ROOT;

  if (sourceRoot && fs.existsSync(path.join(sourceRoot, ENTRY))) {
    const sourceWrapper = getWrapperPath(sourceRoot);
    if (fs.existsSync(sourceWrapper)) {
      return { command: sourceWrapper, repoRoot: sourceRoot, mode: 'wrapper' };
    }
    if (allowHostedFallback()) {
      const runtime = process.env.SIMPLE_BINARY || resolveRuntime(sourceRoot) || `simple${ext}`;
      return { command: runtime, repoRoot: sourceRoot, args: ['run', path.join(sourceRoot, ENTRY)], mode: 'runtime' };
    }
  }

  const projectWrapper = getWrapperPath(projectRoot);
  if (fs.existsSync(projectWrapper)) {
    return { command: projectWrapper, repoRoot: projectRoot, mode: 'wrapper' };
  }
  if (allowHostedFallback()) {
    const runtime = process.env.SIMPLE_BINARY || resolveRuntime(projectRoot);
    if (runtime) {
      return { command: runtime, repoRoot: projectRoot, args: ['run', path.join(projectRoot, ENTRY)], mode: 'runtime' };
    }
  }

  if (fs.existsSync(nativeDir)) {
    const entries = fs.readdirSync(nativeDir).filter(e => e.startsWith('simple-bootstrap-'));
    if (entries.length > 0) {
      const pkgDir = path.join(nativeDir, entries[0]);
      const wrapperPath = getWrapperPath(pkgDir);
      if (fs.existsSync(wrapperPath)) {
        return { command: wrapperPath, repoRoot: pkgDir, mode: 'wrapper' };
      }
      if (allowHostedFallback()) {
        const runtime = process.env.SIMPLE_BINARY || resolveRuntime(pkgDir) || `simple${ext}`;
        return { command: runtime, repoRoot: pkgDir, args: ['run', path.join(pkgDir, ENTRY)], mode: 'runtime' };
      }
    }
  }

  if (allowHostedFallback()) {
    return { command: `simple${ext}`, repoRoot: process.cwd(), args: ['run', path.join(process.cwd(), ENTRY)], mode: 'runtime' };
  }

  throw new Error(
    'No TRACE32 LSP-MCP wrapper or native server path found. Install the packaged wrapper or set ' +
    'SIMPLE_ALLOW_HOSTED_FALLBACK=1 to opt into the legacy hosted runtime path.'
  );
}

let resolved;
try {
  resolved = findLaunchTarget();
} catch (err) {
  process.stderr.write(`Error: ${err.message}\n`);
  process.exit(1);
}
const { command, repoRoot, args = [], mode } = resolved;
const t32Root = path.join(repoRoot, T32_ROOT_REL);
const env = {
  ...process.env,
  SIMPLE_LIB: process.env.SIMPLE_LIB || t32Root,
  T32_LSP_MCP_TOOL_RUNNER: process.env.T32_LSP_MCP_TOOL_RUNNER ||
    path.join(repoRoot, T32_ROOT_REL, 't32_lsp_mcp', 'tool_runner.spl'),
  T32_LSP_MCP_TOOL_DAEMON: process.env.T32_LSP_MCP_TOOL_DAEMON ||
    path.join(repoRoot, T32_ROOT_REL, 'cmm_lsp', 'mcp_daemon.spl'),
  T32_LSP_MCP_TOOL_DAEMON_DIR: process.env.T32_LSP_MCP_TOOL_DAEMON_DIR ||
    path.join(os.tmpdir(), 't32_lsp_mcp_shared'),
  SIMPLE_LOG: process.env.SIMPLE_LOG || 'error',
  RUST_LOG: process.env.RUST_LOG || 'error'
};
if (mode === 'runtime') {
  env.SIMPLE_BINARY = process.env.SIMPLE_BINARY || command;
  env.SIMPLE_RUNTIME = process.env.SIMPLE_RUNTIME || command;
}

const child = spawn(command, [...args, ...process.argv.slice(2)], {
  cwd: repoRoot,
  stdio: 'inherit',
  env
});

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: TRACE32 LSP-MCP launcher target not found at: ${command}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching T32 LSP-MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => {
  if ((code ?? 1) !== 0 && mode === 'wrapper') {
    process.stderr.write('TRACE32 LSP-MCP wrapper launch failed.\n');
  }
  process.exit(code ?? 1);
});
