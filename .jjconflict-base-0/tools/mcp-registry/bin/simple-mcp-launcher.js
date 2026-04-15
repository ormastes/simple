#!/usr/bin/env node
// Launcher for Simple MCP Server.
// Prefer the native MCP binary when it is available, and fall back to
// the Simple runtime + source entry only for older bootstrap bundles.

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

const ENTRY = 'src/app/mcp/main.spl';

function platformDirs() {
  const platform = os.platform();
  const arch = os.arch();
  if (platform === 'darwin' && arch === 'arm64') {
    return ['aarch64-apple-darwin-macho', 'aarch64-apple-darwin', 'darwin-aarch64', 'macos-arm64'];
  }
  if (platform === 'darwin' && arch === 'x64') {
    return ['x86_64-apple-darwin-macho', 'x86_64-apple-darwin', 'darwin-x86_64', 'macos-x86_64'];
  }
  if (platform === 'linux' && arch === 'x64') {
    return ['x86_64-unknown-linux-gnu', 'linux-x86_64'];
  }
  if (platform === 'linux' && arch === 'arm64') {
    return ['aarch64-unknown-linux-gnu', 'linux-aarch64'];
  }
  if (platform === 'win32' && arch === 'x64') {
    return ['x86_64-pc-windows-msvc', 'x86_64-pc-windows-gnu', 'windows-x86_64'];
  }
  if (platform === 'win32' && arch === 'arm64') {
    return ['aarch64-pc-windows-msvc', 'aarch64-pc-windows-gnu', 'windows-aarch64'];
  }
  if (platform === 'freebsd' && arch === 'x64') {
    return ['x86_64-unknown-freebsd', 'freebsd-x86_64'];
  }
  return [];
}

function resolveNativeServer(rootDir) {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const candidates = [];
  for (const platformDir of platformDirs()) {
    candidates.push(path.join(rootDir, 'bin', 'release', platformDir, `simple_mcp_server${ext}`));
  }
  candidates.push(
    path.join(rootDir, 'bin', 'release', `simple_mcp_server${ext}`),
    path.join(rootDir, 'bin', `simple_mcp_server${ext}`),
    path.join(rootDir, 'src', 'compiler_rust', 'bin', 'release', `simple_mcp_server${ext}`)
  );

  for (const candidate of candidates) {
    if (fs.existsSync(candidate)) {
      return candidate;
    }
  }

  return null;
}

function findRuntime() {
  const ext = os.platform() === 'win32' ? '.exe' : '';
  const nativeDir = path.join(__dirname, '..', 'native');
  const projectRoot = path.join(__dirname, '..', '..', '..');

  // 1. Prefer a live project checkout over any cached bootstrap bundle.
  // The native bundle can lag behind the current source tree during development.
  const devServer = resolveNativeServer(projectRoot);
  if (devServer) {
    return { command: devServer, args: [], repoRoot: projectRoot, mode: 'native' };
  }
  for (const platformDir of platformDirs()) {
    const devBinary = path.join(projectRoot, 'bin', 'release', platformDir, `simple${ext}`);
    if (fs.existsSync(devBinary)) {
      return { command: devBinary, args: ['run', path.join(projectRoot, ENTRY)], repoRoot: projectRoot, mode: 'runtime' };
    }
  }
  const flatDevBinary = path.join(projectRoot, 'bin', 'release', `simple${ext}`);
  if (fs.existsSync(flatDevBinary)) {
    return { command: flatDevBinary, args: ['run', path.join(projectRoot, ENTRY)], repoRoot: projectRoot, mode: 'runtime' };
  }
  // Fallback: bin/simple symlink (common dev setup)
  const devSymlink = path.join(projectRoot, 'bin', `simple${ext}`);
  if (fs.existsSync(devSymlink)) {
    return { command: devSymlink, args: ['run', path.join(projectRoot, ENTRY)], repoRoot: projectRoot, mode: 'runtime' };
  }

  // 2. Check extracted bootstrap package
  if (fs.existsSync(nativeDir)) {
    const entries = fs.readdirSync(nativeDir).filter(e => e.startsWith('simple-bootstrap-'));
    if (entries.length > 0) {
      const pkgDir = path.join(nativeDir, entries[0]);
      const nativeServer = resolveNativeServer(pkgDir);
      if (nativeServer) {
        return { command: nativeServer, args: [], repoRoot: pkgDir, mode: 'native' };
      }
      // Primary: bin/simple (correct packaging)
      const binary = path.join(pkgDir, 'bin', `simple${ext}`);
      if (fs.existsSync(binary)) {
        return { command: binary, args: ['run', path.join(pkgDir, ENTRY)], repoRoot: pkgDir, mode: 'runtime' };
      }
      // Fallback: platform-specific deployed runtime under bin/release/<platform>/simple
      const legacyBinary = path.join(pkgDir, 'src', 'compiler_rust', 'bin', 'release', `simple${ext}`);
      if (fs.existsSync(legacyBinary)) {
        return { command: legacyBinary, args: ['run', path.join(pkgDir, ENTRY)], repoRoot: pkgDir, mode: 'runtime' };
      }
    }
  }

  // 3. Fall back to PATH
  return { command: `simple${ext}`, args: ['run', path.join(process.cwd(), ENTRY)], repoRoot: process.cwd(), mode: 'runtime' };
}

const { command, args, repoRoot, mode } = findRuntime();

const child = spawn(command, [...args, ...process.argv.slice(2)], {
  cwd: repoRoot,
  stdio: 'inherit',
  env: {
    ...process.env,
    SIMPLE_LIB: path.join(repoRoot, 'src'),
    SIMPLE_BINARY: process.env.SIMPLE_BINARY || command,
    SIMPLE_LOG: process.env.SIMPLE_LOG || 'error',
    RUST_LOG: process.env.RUST_LOG || 'error'
  }
});

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: Simple MCP launcher target not found at: ${command}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching Simple MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => {
  if ((code ?? 1) !== 0 && mode === 'native') {
    process.stderr.write('Simple MCP native launch failed.\n');
  }
  process.exit(code ?? 1);
});
