#!/usr/bin/env node
// Launcher for Obsidian LSP-MCP Server.
// Prefer the generated wrapper so the registry package matches the repo's
// supported runtime-selection path.
// Hosted `simple run ...main*.spl` fallback is legacy-only and must be opted
// into explicitly with SIMPLE_ALLOW_HOSTED_FALLBACK=1.
// Modes: "bridge" (default) or "mcp"

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

function allowHostedFallback() {
  return process.env.SIMPLE_ALLOW_HOSTED_FALLBACK === '1';
}

function getWrapperPath(repoRoot) {
  const ext = os.platform() === 'win32' ? '.cmd' : '';
  return path.join(repoRoot, 'bin', `obsidian_lsp_mcp_server${ext}`);
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

function findLaunchTarget(entryFile) {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const nativeDir = path.join(__dirname, '..', 'native');
  const projectRoot = path.join(__dirname, '..', '..', '..');
  const entryRel = entryFile.replace(/\\/g, '/');
  const sourceRoot = process.env.SIMPLE_SOURCE_ROOT;

  if (sourceRoot && fs.existsSync(path.join(sourceRoot, entryRel))) {
    const sourceWrapper = getWrapperPath(sourceRoot);
    if (fs.existsSync(sourceWrapper)) {
      return { command: sourceWrapper, repoRoot: sourceRoot, mode: 'wrapper' };
    }
    if (allowHostedFallback()) {
      const runtime = process.env.SIMPLE_BINARY || resolveRuntime(sourceRoot) || `simple${ext}`;
      return { command: runtime, repoRoot: sourceRoot, args: ['run', path.join(sourceRoot, entryRel)], mode: 'runtime' };
    }
  }

  const projectWrapper = getWrapperPath(projectRoot);
  if (fs.existsSync(projectWrapper)) {
    return { command: projectWrapper, repoRoot: projectRoot, mode: 'wrapper' };
  }
  if (allowHostedFallback()) {
    const runtime = process.env.SIMPLE_BINARY || resolveRuntime(projectRoot);
    if (runtime) {
      return { command: runtime, repoRoot: projectRoot, args: ['run', path.join(projectRoot, entryRel)], mode: 'runtime' };
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
        return { command: runtime, repoRoot: pkgDir, args: ['run', path.join(pkgDir, entryRel)], mode: 'runtime' };
      }
    }
  }

  if (allowHostedFallback()) {
    return { command: `simple${ext}`, repoRoot: process.cwd(), args: ['run', path.join(process.cwd(), entryRel)], mode: 'runtime' };
  }

  throw new Error(
    'No Obsidian LSP-MCP wrapper or native server path found. Install the packaged wrapper or set ' +
    'SIMPLE_ALLOW_HOSTED_FALLBACK=1 to opt into the legacy hosted runtime path.'
  );
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

const entryFile = mode === 'mcp'
  ? 'examples/obsidian-search/src/main.spl'
  : 'examples/obsidian-search/src/main_bridge.spl';

let resolved;
try {
  resolved = findLaunchTarget(entryFile);
} catch (err) {
  process.stderr.write(`Error: ${err.message}\n`);
  process.exit(1);
}
const { command, repoRoot, args: launchArgs = [], mode: launchMode } = resolved;

// SIMPLE_LIB needs both obsidian-search/src and the main src
const sep = os.platform() === 'win32' ? ';' : ':';
const simpleLib = [
  path.join(repoRoot, 'examples', 'obsidian-search', 'src'),
  path.join(repoRoot, 'src')
].join(sep);

const env = {
  ...process.env,
  SIMPLE_LIB: simpleLib,
  OBSIDIAN_VAULT_PATH: process.env.OBSIDIAN_VAULT_PATH || '',
  SIMPLE_LOG: process.env.SIMPLE_LOG || 'error',
  RUST_LOG: process.env.RUST_LOG || 'error'
};
if (launchMode === 'runtime') {
  env.SIMPLE_BINARY = process.env.SIMPLE_BINARY || command;
}

const child = spawn(command, [...launchArgs, ...passArgs], {
  cwd: repoRoot,
  stdio: 'inherit',
  env
});

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: Obsidian LSP-MCP launcher target not found at: ${command}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching Obsidian LSP-MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => {
  if ((code ?? 1) !== 0 && launchMode === 'wrapper') {
    process.stderr.write('Obsidian LSP-MCP wrapper launch failed.\n');
  }
  process.exit(code ?? 1);
});
