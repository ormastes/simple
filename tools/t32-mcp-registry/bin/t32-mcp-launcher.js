#!/usr/bin/env node
// Launcher for TRACE32 MCP Server.
// Prefer the generated wrapper so the registry package matches the repo's
// supported runtime-selection and cold-start path.
// Hosted `simple run ...frontend_cold.spl` fallback is legacy-only and must be
// opted into explicitly with SIMPLE_ALLOW_HOSTED_FALLBACK=1.

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

const ENTRY = path.join(
  'examples',
  '10_tooling',
  'trace32_tools',
  't32_mcp',
  'frontend_cold.spl'
);

function allowHostedFallback() {
  return process.env.SIMPLE_ALLOW_HOSTED_FALLBACK === '1';
}

function getWrapperPath(repoRoot) {
  const ext = os.platform() === 'win32' ? '.cmd' : '';
  return path.join(repoRoot, 'bin', `t32_mcp_server${ext}`);
}

function resolveRuntime(pkgDir) {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const candidates = [
    path.join(pkgDir, 'bin', `simple${ext}`),
    path.join(pkgDir, 'bin', 'release', `simple${ext}`),
    path.join(pkgDir, 'src', 'compiler_rust', 'target', 'bootstrap', `simple${ext}`),
    path.join(pkgDir, 'src', 'compiler_rust', 'target', 'release', `simple${ext}`),
    path.join(pkgDir, 'src', 'compiler_rust', 'bin', 'release', `simple${ext}`)
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
    'No TRACE32 MCP wrapper or native server path found. Install the packaged wrapper or set ' +
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

const env = {
  ...process.env,
  SIMPLE_LOG: process.env.SIMPLE_LOG || 'error',
  RUST_LOG: process.env.RUST_LOG || 'error'
};
if (mode === 'runtime') {
  env.SIMPLE_BINARY = process.env.SIMPLE_BINARY || command;
}

const child = spawn(command, [...args, ...process.argv.slice(2)], {
  cwd: repoRoot,
  stdio: 'inherit',
  env: {
    ...env,
    SIMPLE_LIB: process.env.SIMPLE_LIB || path.join(repoRoot, 'src')
  }
});

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: TRACE32 MCP launcher target not found at: ${command}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching T32 MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => {
  if ((code ?? 1) !== 0 && mode === 'wrapper') {
    process.stderr.write('TRACE32 MCP wrapper launch failed.\n');
  }
  process.exit(code ?? 1);
});
