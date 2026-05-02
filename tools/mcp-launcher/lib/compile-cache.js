'use strict';

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

/**
 * Optionally compile a .spl entry to .smf cache file.
 * Returns the artifact path to exec (cache file or original entry).
 *
 * CRITICAL: stdin is NOT inherited — uses 'ignore' to prevent consuming
 * MCP protocol messages from the parent's stdin.
 */
function compileIfNeeded(config, runtime, repoRoot, simpleLib, diag) {
  if (!config || !config.enabled) return null;

  const variant = process.env.T32_MCP_FRONTEND || config.defaultVariant || 'main';
  const variantEntry = config.variants[variant];
  if (!variantEntry) {
    diag.warn('unknown compile variant', { variant, available: Object.keys(config.variants) });
    return null;
  }

  const entryAbs = path.join(repoRoot, variantEntry);
  const cacheDir = path.join(repoRoot, config.cacheDir);
  const cacheFile = path.join(cacheDir, variant + '.smf');
  const minBytes = config.minCacheBytes || 512;
  const timeoutMs = config.timeoutMs || 30000;

  // Check if cache is fresh
  if (isCacheFresh(cacheFile, entryAbs, runtime, minBytes)) {
    diag.debug('cache hit', { cacheFile, variant });
    return cacheFile;
  }

  // Compile with stdin isolated
  diag.info('compiling', { entry: variantEntry, cacheFile, variant });
  fs.mkdirSync(cacheDir, { recursive: true });

  const logFd = diag.getLogFd();
  try {
    execFileSync(runtime, ['compile', entryAbs, '-o', cacheFile], {
      cwd: repoRoot,
      stdio: ['ignore', logFd, logFd],  // stdin=/dev/null, stdout+stderr→log
      timeout: timeoutMs,
      env: {
        ...process.env,
        SIMPLE_LIB: path.join(repoRoot, simpleLib),
        SIMPLE_BINARY: runtime,
        SIMPLE_MEMORY_LIMIT_MB: process.env.SIMPLE_MEMORY_LIMIT_MB || '512',
        SIMPLE_TIMEOUT_SECONDS: '120'
      }
    });
  } catch (err) {
    diag.warn('compile failed, will use source entry', { error: err.message });
    safeUnlink(cacheFile);
    return null;
  }

  // Validate cache is non-trivial
  try {
    const size = fs.statSync(cacheFile).size;
    if (size < minBytes) {
      diag.warn('compiled cache too small (stub), using source', { size, minBytes });
      safeUnlink(cacheFile);
      return null;
    }
    diag.info('compile success', { cacheFile, size });
    return cacheFile;
  } catch (_) {
    return null;
  }
}

function isCacheFresh(cacheFile, entryFile, runtime, minBytes) {
  try {
    const cacheStat = fs.statSync(cacheFile);
    if (cacheStat.size < minBytes) return false;
    const entryMtime = fs.statSync(entryFile).mtimeMs;
    const runtimeMtime = fs.statSync(runtime).mtimeMs;
    return cacheStat.mtimeMs > entryMtime && cacheStat.mtimeMs > runtimeMtime;
  } catch (_) {
    return false;
  }
}

function safeUnlink(p) {
  try { fs.unlinkSync(p); } catch (_) { /* ignore */ }
}

module.exports = { compileIfNeeded };
