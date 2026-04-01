#!/usr/bin/env node
// Cross-platform launcher for the Codex Stitch MCP proxy.

const { spawn } = require('child_process');
const fs = require('fs');
const os = require('os');
const path = require('path');

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
  if (signal) {
    process.kill(process.pid, signal);
    return;
  }
  process.exit(code ?? 1);
});
