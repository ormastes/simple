// Real bridge/child processes; no Simple runtime or external MCP account is used.
const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { spawn } = require('node:child_process');
const bridgePath = path.resolve(__dirname, '../../../../bin/mcp_stdio_bridge.js');
const fixturePath = path.resolve(__dirname, '../../../fixtures/mcp/bridge_lifecycle_child.cjs');
const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
function alive(pid) {
  try { process.kill(pid, 0); return true; }
  catch (error) { if (error.code === 'ESRCH') return false; throw error; }
}
async function within(promise, milliseconds) {
  let timer;
  try { return await Promise.race([promise, new Promise(resolve => { timer = setTimeout(() => resolve(null), milliseconds); })]); }
  finally { clearTimeout(timer); }
}
async function launch(mode, missing = false) {
  const folder = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-mcp-owned-'));
  const stopFile = path.join(folder, 'stop-owned-fixture');
  const command = missing ? path.join(folder, 'missing-command') : process.execPath;
  const args = missing ? [] : [fixturePath, mode, stopFile];
  const child = spawn(process.execPath, [bridgePath, '--', command, ...args], {
    cwd: folder, stdio: ['pipe', 'pipe', 'pipe'], windowsHide: true,
  });
  let output = '';
  let fixturePid;
  let resolveReady;
  const ready = new Promise(resolve => { resolveReady = resolve; });
  const closed = new Promise((resolve, reject) => {
    child.once('error', reject);
    child.once('close', (code, signal) => resolve({ code, signal }));
  });
  child.stdout.on('data', data => {
    output += data.toString('utf8');
    const found = output.match(/"fixturePid":(\d+)/);
    if (found) { fixturePid = Number(found[1]); resolveReady(fixturePid); }
  });
  child.stderr.resume();
  child.stdin.on('error', () => {});
  if (!missing) child.stdin.write('{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}\n');
  return { child, closed, ready, get fixturePid() { return fixturePid; }, async cleanup() {
    // Only this fixture watches this unique file. Never signal a reported PID.
    fs.writeFileSync(stopFile, 'stop');
    if (fixturePid) {
      const deadline = Date.now() + 2000;
      while (alive(fixturePid) && Date.now() < deadline) await delay(25);
      assert.equal(alive(fixturePid), false, 'owned fixture cleanup did not finish');
    }
    if (child.exitCode === null && child.signalCode === null) child.kill('SIGKILL');
    assert.notEqual(await within(closed, 2000), null, 'owned bridge cleanup did not finish');
    fs.rmSync(folder, { recursive: true, force: true });
  } };
}
async function cooperativeSession() {
  const run = await launch('cooperative');
  try {
    assert.notEqual(await within(run.ready, 2000), null, 'fixture initialize response missing');
    run.child.stdin.end();
    const result = await within(run.closed, 3000);
    assert.notEqual(result, null, 'bridge stayed alive after normal client EOF');
    assert.equal(result.code, 0);
    assert.equal(alive(run.fixturePid), false, 'owned child survived normal close');
  } finally { await run.cleanup(); }
}
test('normal close waits for the owned child to exit', cooperativeSession);
test('start failure exits even while client stdin remains open', async () => {
  const run = await launch('cooperative', true);
  try {
    const result = await within(run.closed, 3000);
    assert.notEqual(result, null, 'spawn failure left the bridge waiting on client stdin');
    assert.notEqual(result.code, 0);
  } finally { await run.cleanup(); }
});
test('client EOF bounds shutdown of a child that ignores EOF', async () => {
  const run = await launch('stubborn');
  try {
    assert.notEqual(await within(run.ready, 2000), null, 'fixture initialize response missing');
    run.child.stdin.end();
    assert.notEqual(await within(run.closed, 5000), null, 'owned child and bridge leaked after client EOF');
    assert.equal(alive(run.fixturePid), false, 'owned stubborn child survived bridge close');
  } finally { await run.cleanup(); }
});
test('three independent sessions leave none of their owned children alive', async () => {
  for (let i = 0; i < 3; i++) await cooperativeSession();
});
