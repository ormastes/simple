#!/usr/bin/env node
// Cross-platform launcher for the Codex Stitch MCP proxy.

const { spawn, execSync } = require('child_process');
const fs = require('fs');
const os = require('os');
const path = require('path');

// Singleton: kill older sibling wrappers with the same parent. See the
// matching block in codex_chrome_devtools_mcp.js for rationale.
// Escape hatch: SIMPLE_DISABLE_WRAPPER_SINGLETON=1.
function killOlderSiblings() {
  if (process.platform === 'win32') return;
  if (process.env.SIMPLE_DISABLE_WRAPPER_SINGLETON === '1') return;
  try {
    const myPid = process.pid;
    const myPpid = process.ppid;
    const scriptBase = path.basename(__filename);
    const out = execSync('ps -axo pid,ppid,command', { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
    for (const line of out.split('\n')) {
      const m = line.trim().match(/^(\d+)\s+(\d+)\s+(.*)$/);
      if (!m) continue;
      const pid = parseInt(m[1], 10);
      const ppid = parseInt(m[2], 10);
      const cmd = m[3];
      if (pid === myPid || ppid !== myPpid) continue;
      if (!cmd.includes(scriptBase)) continue;
      try { process.kill(pid, 'SIGTERM'); } catch (_) {}
    }
  } catch (_) {
    // best effort
  }
}
killOlderSiblings();

function stripQuotes(value) {
  if (value.length >= 2) {
    const first = value[0];
    const last = value[value.length - 1];
    if ((first === '"' && last === '"') || (first === "'" && last === "'")) {
      return value.slice(1, -1);
    }
  }
  return value;
}

function loadEnvSh(baseEnv) {
  const home = os.homedir();
  if (!home) return baseEnv;

  const envPath = path.join(home, '.security', 'env.sh');
  if (!fs.existsSync(envPath)) return baseEnv;

  const merged = { ...baseEnv };
  const lines = fs.readFileSync(envPath, 'utf8').split(/\r?\n/);
  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) continue;

    const match = trimmed.match(/^(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)=(.*)$/);
    if (!match) continue;

    merged[match[1]] = stripQuotes(match[2].trim());
  }
  return merged;
}

const isWindows = process.platform === 'win32';
const command = isWindows ? 'npx.cmd' : 'npx';
const args = ['-y', '@_davideast/stitch-mcp', 'proxy', ...process.argv.slice(2)];
const env = loadEnvSh({ ...process.env });

const child = spawn(command, args, {
  stdio: 'inherit',
  env,
});

let exiting = false;
let killTimer = null;
function terminateChild(reason) {
  if (exiting) return;
  exiting = true;
  try { child.kill('SIGTERM'); } catch (_) {}
  killTimer = setTimeout(() => {
    try { child.kill('SIGKILL'); } catch (_) {}
    process.exit(0);
  }, 2000);
  killTimer.unref();
}

// macOS has no PR_SET_PDEATHSIG; poll ppid so we exit when the launching
// CLI dies ungracefully. Without this, the wrapper + npm exec + stitch-mcp
// chain is reparented to launchd and survives forever.
const initialPpid = process.ppid;
const ppidWatch = setInterval(() => {
  if (process.ppid === 1 || process.ppid !== initialPpid) {
    terminateChild('parent died');
  }
}, 1000);
ppidWatch.unref();

for (const sig of ['SIGTERM', 'SIGINT', 'SIGHUP', 'SIGQUIT']) {
  process.on(sig, () => terminateChild(`received ${sig}`));
}

child.on('error', (err) => {
  if (err.code === 'ENOENT') {
    process.stderr.write(
      `Error: ${command} was not found in PATH.\n` +
      'Install Node.js/npm so Codex can start the Stitch MCP proxy.\n'
    );
  } else {
    process.stderr.write(`Error launching Stitch MCP proxy: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code, signal) => {
  clearInterval(ppidWatch);
  if (killTimer) clearTimeout(killTimer);
  // Don't re-signal self — our SIGTERM/SIGINT handlers would swallow it.
  if (signal) {
    process.exit(128 + (require('os').constants.signals[signal] || 0));
  }
  process.exit(code ?? 1);
});
