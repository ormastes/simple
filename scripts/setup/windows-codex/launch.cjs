// Keep ordinary Windows CLI sessions out of the shared background daemon.
const fs = require('node:fs');
const path = require('node:path');
const { spawnSync } = require('node:child_process');

const { entry } = JSON.parse(fs.readFileSync(path.join(__dirname, 'target.json'), 'utf8'));
const args = process.argv.slice(2);
// These commands intentionally manage/use the shared server. Use codex.cmd
// directly if a PowerShell profile defines its own codex function.
const serverCommand = ['agents', 'app-server', 'remote-control'].includes(args[0]);
const remote = args.some(arg => arg === '--remote' || arg.startsWith('--remote='));
if (!serverCommand && !remote && !args.includes('--no-daemon')) {
  args.unshift('--no-daemon');
}
const result = spawnSync(process.execPath, [entry, ...args], { stdio: 'inherit' });
if (result.error) {
  console.error(`Cannot start Codex: ${result.error.message}`);
}
process.exit(result.status ?? 1);
