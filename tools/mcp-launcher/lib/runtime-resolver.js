'use strict';

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

/**
 * Resolve the Simple runtime binary using a 6-step fallback chain.
 * Returns { runtime: absolutePath, kind: string } or throws.
 */
function resolveRuntime(repoRoot, diag) {
  const candidates = [
    { path: path.join(repoRoot, 'src', 'compiler_rust', 'target', 'bootstrap', 'simple'), kind: 'rust-bootstrap' },
    { path: path.join(repoRoot, 'bin', 'simple'), kind: 'bin-simple' },
    { path: path.join(repoRoot, 'bin', 'release', 'simple'), kind: 'bin-release' },
    { path: path.join(repoRoot, 'src', 'compiler_rust', 'target', 'release', 'simple'), kind: 'rust-release' },
  ];

  // On Windows, try .exe variants
  if (process.platform === 'win32') {
    const exeCandidates = candidates.map(c => ({
      path: c.path + '.exe',
      kind: c.kind
    }));
    candidates.push(...exeCandidates);
  }

  // Check SIMPLE_BINARY env override
  const envBinary = process.env.SIMPLE_BINARY;
  if (envBinary && isExecutable(envBinary)) {
    diag.info('runtime resolved from SIMPLE_BINARY env', { runtime: envBinary });
    return { runtime: envBinary, kind: 'env-override' };
  }

  for (const c of candidates) {
    // Resolve symlinks to find the real binary
    let realPath;
    try {
      realPath = fs.realpathSync(c.path);
    } catch (_) {
      continue;
    }
    if (isExecutable(realPath)) {
      diag.info('runtime resolved', { runtime: realPath, kind: c.kind });
      return { runtime: realPath, kind: c.kind };
    }
  }

  // Last resort: try 'simple' on PATH
  try {
    const which = process.platform === 'win32' ? 'where' : 'which';
    const result = execFileSync(which, ['simple'], {
      stdio: ['ignore', 'pipe', 'ignore'],
      timeout: 2000
    }).toString().trim().split('\n')[0];
    if (result && isExecutable(result)) {
      diag.info('runtime resolved from PATH', { runtime: result });
      return { runtime: result, kind: 'path' };
    }
  } catch (_) {
    // Not on PATH
  }

  throw new Error('No Simple runtime found. Checked: ' +
    candidates.map(c => c.path).join(', '));
}

function isExecutable(p) {
  try {
    fs.accessSync(p, fs.constants.X_OK);
    return true;
  } catch (_) {
    return false;
  }
}

module.exports = { resolveRuntime, isExecutable };
