'use strict';

const fs = require('fs');
const path = require('path');
const os = require('os');
const { spawnSync } = require('child_process');

/**
 * Check if a native binary is healthy (responds to --version within timeout).
 * Uses a signature-based cache file to avoid repeated probes.
 */
function isNativeHealthy(binaryPath, diag) {
  if (!binaryPath) return false;
  try {
    fs.accessSync(binaryPath, fs.constants.X_OK);
  } catch (_) {
    return false;
  }

  // Check signature cache
  const cacheFile = getNativeHealthCachePath(binaryPath);
  const sig = getNativeSignature(binaryPath);

  const cached = readCachedHealth(cacheFile, sig);
  if (cached !== null) {
    diag.debug('native health cache hit', { status: cached });
    return cached === 'healthy';
  }

  // Probe
  diag.info('probing native binary', { path: binaryPath });
  const result = spawnSync(binaryPath, ['--version'], {
    stdio: 'ignore',
    timeout: 2000
  });

  const status = result.status === 0 ? 'healthy' : 'unhealthy';
  writeCachedHealth(cacheFile, sig, status);
  diag.info('native health probe result', { status });
  return status === 'healthy';
}

/**
 * Run a quick health check for the launcher itself.
 * Verifies runtime is found and executable.
 */
function runHealthCheck(runtime, diag) {
  diag.info('health check', { runtime });
  const result = spawnSync(runtime, ['--version'], {
    stdio: 'ignore',
    timeout: 5000
  });
  const ok = result.status === 0;
  diag.info('health check result', { ok, exitCode: result.status });
  return ok;
}

function getNativeHealthCachePath(binaryPath) {
  const cwd = process.cwd().replace(/^\/+/, '').replace(/[^A-Za-z0-9._-]/g, '_') || 'workspace';
  const name = path.basename(binaryPath);
  return path.join(os.tmpdir(), `mcp_native_health_${name}_${cwd}.state`);
}

function getNativeSignature(binaryPath) {
  try {
    const stat = fs.statSync(binaryPath);
    return `${stat.mtimeMs}:${stat.size}`;
  } catch (_) {
    return 'unknown';
  }
}

function readCachedHealth(cacheFile, expectedSig) {
  try {
    const content = fs.readFileSync(cacheFile, 'utf8');
    const lines = content.trim().split('\n');
    const sigLine = lines.find(l => l.startsWith('sig='));
    const statusLine = lines.find(l => l.startsWith('status='));
    if (sigLine && statusLine) {
      const cachedSig = sigLine.slice(4);
      const cachedStatus = statusLine.slice(7);
      if (cachedSig === expectedSig) return cachedStatus;
    }
  } catch (_) { /* no cache */ }
  return null;
}

function writeCachedHealth(cacheFile, sig, status) {
  try {
    fs.writeFileSync(cacheFile, `sig=${sig}\nstatus=${status}\n`);
  } catch (_) { /* best-effort */ }
}

module.exports = { isNativeHealthy, runHealthCheck };
