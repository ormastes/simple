// Synthetic JSONL child; cleanup is a private stop-file, never a PID-wide kill.
const fs = require('node:fs');
const readline = require('node:readline');
const [mode, stopFile] = process.argv.slice(2);
const heartbeat = setInterval(() => {
  if (fs.existsSync(stopFile)) process.exit(0);
}, 25);
const input = readline.createInterface({ input: process.stdin });
input.on('line', line => {
  const request = JSON.parse(line);
  process.stdout.write(JSON.stringify({ jsonrpc: '2.0', id: request.id,
    result: { fixturePid: process.pid } }) + '\n');
});
input.on('close', () => {
  if (mode === 'cooperative') { clearInterval(heartbeat); process.exit(0); }
});
if (mode === 'stubborn') process.on('SIGTERM', () => {});
