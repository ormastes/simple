#!/usr/bin/env node
// Launcher for TRACE32 MCP Server.
// Prefer the generated wrapper so the registry package matches the repo's
// supported runtime-selection and cold-start path.

const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');
const os = require('os');

function getWrapperPath(repoRoot) {
  const ext = os.platform() === 'win32' ? '.cmd' : '';
  return path.join(repoRoot, 'bin', `t32_mcp_server${ext}`);
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

const env = {
  ...process.env,
  SIMPLE_BINARY: binary,
  SIMPLE_LOG: process.env.SIMPLE_LOG || 'error',
  RUST_LOG: process.env.RUST_LOG || 'error'
};

// The repo wrapper selects the stable frontend and sets the correct runtime
// environment. Fall back to direct runtime execution only if the wrapper is
// missing from the package layout.
const child = fs.existsSync(wrapperPath)
  ? spawn(wrapperPath, process.argv.slice(2), { stdio: 'inherit', env })
  : spawn(binary, [
      path.join(repoRoot, 'examples', '10_tooling', 'trace32_tools', 't32_mcp', 'frontend_cold.spl'),
      ...process.argv.slice(2)
    ], {
      stdio: 'inherit',
      env: {
        ...env,
        SIMPLE_LIB: process.env.SIMPLE_LIB || path.join(repoRoot, 'src')
      }
    });

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: Simple runtime not found at: ${binary}\n` +
      `Run 'npm run postinstall' to download, or build from source.\n`
    );
  } else {
    process.stderr.write(`Error launching T32 MCP Server: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code) => process.exit(code ?? 1));
