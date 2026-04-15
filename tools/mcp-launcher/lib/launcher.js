'use strict';

const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');
const { Diagnostics } = require('./diagnostics');
const { resolveRuntime, isExecutable } = require('./runtime-resolver');
const { compileIfNeeded } = require('./compile-cache');
const { isNativeHealthy, runHealthCheck } = require('./health-check');

/**
 * Resolve the repo root by walking up from a starting directory,
 * looking for VERSION file or .mcp.json.
 */
function resolveRepoRoot(startDir) {
  let dir = startDir;
  for (let i = 0; i < 10; i++) {
    if (fs.existsSync(path.join(dir, 'VERSION')) ||
        fs.existsSync(path.join(dir, '.mcp.json'))) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }
  return startDir;
}

/**
 * Compute workspace suffix for temp directories.
 */
function workspaceSuffix() {
  return process.cwd().replace(/^\/+/, '').replace(/[^A-Za-z0-9._-]/g, '_') || 'workspace';
}

/**
 * Substitute template variables in env values.
 */
function substituteEnv(value, vars) {
  return value
    .replace(/\$\{RUNTIME\}/g, vars.runtime || '')
    .replace(/\$\{REPO_ROOT\}/g, vars.repoRoot || '')
    .replace(/\$\{WORKSPACE_SUFFIX\}/g, vars.workspaceSuffix || '');
}

/**
 * Build the environment for the server process.
 */
function buildEnv(serverConfig, vars) {
  const env = { ...process.env };

  // Apply server-level env
  for (const [k, v] of Object.entries(serverConfig.env || {})) {
    if (!env[k]) env[k] = substituteEnv(v, vars);
  }

  // Apply extra env (server-specific, higher priority)
  for (const [k, v] of Object.entries(serverConfig.extraEnv || {})) {
    const resolved = substituteEnv(v, vars);
    // Only set if the resolved value is non-empty and file exists (for binary paths)
    if (k.endsWith('_BIN') && resolved && !isExecutable(resolved)) continue;
    if (resolved) env[k] = resolved;
  }

  // Always set SIMPLE_LIB
  env.SIMPLE_LIB = env.SIMPLE_LIB || path.join(vars.repoRoot, serverConfig.simpleLib);

  return env;
}

/**
 * Main launcher function.
 *
 * @param {string} serverName - Server key from servers.json
 * @param {object} serverConfig - Server config object
 * @param {object} opts - { healthCheck: bool, variant: string }
 */
function launch(serverName, serverConfig, opts = {}) {
  const launcherDir = path.resolve(__dirname, '..');
  const repoRoot = resolveRepoRoot(path.resolve(launcherDir, '..', '..'));
  const diag = new Diagnostics(serverName, repoRoot, {
    level: process.env.MCP_LAUNCHER_LOG || process.env.SIMPLE_LOG || 'error'
  });

  diag.info('launcher start', {
    server: serverName,
    pid: process.pid,
    cwd: process.cwd(),
    repoRoot
  });

  // Step 1: Check for native binary
  let runtime = null;
  let runtimeKind = null;

  if (serverConfig.nativeBinary) {
    const nativePath = path.join(repoRoot, serverConfig.nativeBinary);
    if (isNativeHealthy(nativePath, diag)) {
      runtime = nativePath;
      runtimeKind = 'native';
      diag.info('using native binary', { path: nativePath });
    }
  }

  // Step 2: Resolve runtime if no native binary
  if (!runtime) {
    const resolved = resolveRuntime(repoRoot, diag);
    runtime = resolved.runtime;
    runtimeKind = resolved.kind;
  }

  // Step 3: Health check mode
  if (opts.healthCheck) {
    const ok = runHealthCheck(runtime, diag);
    diag.close();
    process.exit(ok ? 0 : 1);
  }

  // Step 4: Determine entry point
  let entry = path.join(repoRoot, serverConfig.entry);

  // Step 5: Optional compile cache (stdin-isolated)
  if (serverConfig.compile && runtimeKind !== 'native') {
    const cached = compileIfNeeded(
      serverConfig.compile,
      runtime,
      repoRoot,
      serverConfig.simpleLib,
      diag
    );
    if (cached) {
      entry = cached;
      diag.info('using cached artifact', { entry: cached });
    }
  }

  // For native binary, entry is not used — exec the binary directly
  const args = runtimeKind === 'native'
    ? [...(opts.passthrough || [])]
    : [entry, ...(opts.passthrough || [])];

  // Step 6: Build environment
  const vars = {
    runtime,
    repoRoot,
    workspaceSuffix: workspaceSuffix()
  };
  const env = buildEnv(serverConfig, vars);

  // Ensure SIMPLE_BINARY and SIMPLE_RUNTIME are set
  env.SIMPLE_BINARY = env.SIMPLE_BINARY || runtime;
  env.SIMPLE_RUNTIME = env.SIMPLE_RUNTIME || runtime;

  diag.info('exec', {
    runtime,
    runtimeKind,
    entry,
    argsCount: args.length
  });

  // Step 7: Exec — inherit stdio so MCP protocol flows through
  const logFd = diag.getLogFd();
  const child = spawn(runtime, args, {
    cwd: repoRoot,
    stdio: ['inherit', 'inherit', logFd],
    env
  });

  child.on('exit', (code, signal) => {
    diag.info('server exit', { code, signal });
    diag.close();
    process.exit(code || 0);
  });

  child.on('error', (err) => {
    diag.error('spawn error', { error: err.message });
    diag.close();
    process.exit(1);
  });

  // Forward signals
  for (const sig of ['SIGINT', 'SIGTERM', 'SIGHUP']) {
    process.on(sig, () => {
      child.kill(sig);
    });
  }
}

module.exports = { launch, resolveRepoRoot, buildEnv, workspaceSuffix };
