#!/usr/bin/env node
// Cross-platform launcher for the Codex Chrome DevTools MCP.

const { spawn, execSync } = require('child_process');
const path = require('path');

// Singleton: kill older sibling wrappers with the same parent. Codex sometimes
// respawns its MCP fleet without killing predecessors, leaving N>1 wrappers
// (and N grandchild Chromium processes) per session. The newer wrapper sweeps
// the older. Escape hatch: SIMPLE_DISABLE_WRAPPER_SINGLETON=1.
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
    // best effort — never block startup on this
  }
}
killOlderSiblings();

const isWindows = process.platform === 'win32';
const command = isWindows ? 'npx.cmd' : 'npx';
const args = [
  '-y',
  'chrome-devtools-mcp@latest',
  '--headless',
  '--isolated',
  '--no-usage-statistics',
  ...process.argv.slice(2),
];

const env = { ...process.env };
if (isWindows) {
  env.SystemRoot = env.SystemRoot || 'C:\\Windows';
  env.PROGRAMFILES = env.PROGRAMFILES || env.ProgramFiles || 'C:\\Program Files';
  env.ProgramFiles = env.ProgramFiles || env.PROGRAMFILES;
}

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
// CLI dies ungracefully (SIGKILL, terminal close). Without this, the
// wrapper + npm exec + chrome-devtools-mcp chain is reparented to launchd
// and survives forever, leaking ~7 MB private RSS per orphan.
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
      'Install Node.js/npm so Codex can start the Chrome DevTools MCP.\n'
    );
  } else {
    process.stderr.write(`Error launching Chrome DevTools MCP: ${err.message}\n`);
  }
  process.exit(1);
});

child.on('exit', (code, signal) => {
  clearInterval(ppidWatch);
  if (killTimer) clearTimeout(killTimer);
  // Don't re-signal self — our SIGTERM/SIGINT handlers would swallow it
  // and we'd never actually exit. Mirror the child's outcome via exit code.
  if (signal) {
    process.exit(128 + (require('os').constants.signals[signal] || 0));
  }
  process.exit(code ?? 1);
});
