#!/usr/bin/env node
// Cross-platform launcher for the Codex Chrome DevTools MCP.

const { spawn } = require('child_process');

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
  if (signal) {
    process.kill(process.pid, signal);
    return;
  }
  process.exit(code ?? 1);
});
