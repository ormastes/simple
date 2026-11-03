'use strict';
// Run only against a qualified native server: node this-file --server ABSOLUTE_BINARY.
// No default binary: the tracked Rust seed is not an admitted MCP producer.
const assert = require('node:assert/strict');
const { spawn } = require('node:child_process');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const readline = require('node:readline');

const server = process.argv[2] === '--server' && process.argv[3];
if (!server) {
  console.error('TEST_BLOCKED: supply --server with a qualified native LSP MCP binary');
  process.exit(77);
}
assert(path.isAbsolute(server) && fs.statSync(server).isFile(), 'server must be an absolute executable file');
const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-lsp-lifecycle-'));
const clients = new Set();
const descendants = new Set();
const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
let passed = 0;

function live(pid) {
  try {
    process.kill(pid, 0);
    // An exited POSIX orphan can remain a zombie until its host init reaps it.
    if (process.platform === 'linux') {
      const stat = fs.readFileSync(`/proc/${pid}/stat`, 'utf8');
      if (stat.slice(stat.lastIndexOf(')') + 2).startsWith('Z ')) return false;
    }
    return true;
  } catch (error) {
    if (error.code === 'ESRCH' || error.code === 'ENOENT') return false;
    throw error;
  }
}

async function until(predicate, timeout, message) {
  const end = Date.now() + timeout;
  while (!predicate()) {
    assert(Date.now() < end, message);
    await delay(25);
  }
}

function client(env = {}) {
  const child = spawn(server, [], {
    cwd: directory,
    env: { ...process.env, ...env },
    stdio: ['pipe', 'pipe', 'pipe'],
    windowsHide: true,
  });
  clients.add(child);
  let error;
  let exited = false;
  let exitCode;
  let stderr = '';
  const responses = new Map();
  child.on('error', value => { error = value; });
  child.on('close', code => { exited = true; exitCode = code; });
  child.stderr.on('data', data => { stderr = (stderr + data.toString()).slice(-8192); });
  child.stdin.on('error', value => { error = value; });
  readline.createInterface({ input: child.stdout }).on('line', line => {
    try {
      const response = JSON.parse(line);
      if (Object.hasOwn(response, 'id')) responses.set(response.id, response);
    } catch { /* non-protocol output cannot satisfy the response assertion */ }
  });
  let sequence = 0;
  return {
    child,
    async request(method, params = {}, timeout = 5000) {
      const id = ++sequence;
      child.stdin.write(JSON.stringify({ jsonrpc: '2.0', id, method, params }) + '\n');
      await until(() => error || exited || responses.has(id), timeout, `${method} timed out; ${stderr}`);
      if (error) throw error;
      assert(responses.has(id), `${method} exited before responding; ${stderr}`);
      const response = responses.get(id);
      assert.equal(response.jsonrpc, '2.0');
      assert.equal(response.error, undefined, JSON.stringify(response));
      return response.result;
    },
    async close() {
      child.stdin.end();
      await until(() => exited, 5000, `owned server PID ${child.pid} did not exit on EOF; ${stderr}`);
      assert.equal(exitCode, 0, stderr);
      assert.equal(live(child.pid), false);
      clients.delete(child);
    },
  };
}

async function initialize(connection) {
  const result = await connection.request('initialize', {
    protocolVersion: '2025-06-18', capabilities: {},
    clientInfo: { name: 'tracked-pid-lifecycle', version: '1' },
  });
  assert.equal(result.serverInfo.name, 'simple-lsp-mcp');
}

async function run() {
  // Exact original lifecycle gate: track only launched PIDs, never scan/kill by name.
  for (let i = 0; i < 3; i++) {
    const connection = client();
    await initialize(connection);
    await connection.close();
    passed++;
  }
  const empty = client();
  await empty.close();
  passed++;

  // Independent stdio clients must survive another client's disconnect.
  const first = client();
  const second = client();
  await initialize(first);
  await initialize(second);
  await first.close();
  await second.request('ping');
  await second.close();
  passed++;

  // Real diagnostics handler -> bounded native owner -> delegate + descendant.
  // Node interprets cwd/check as its script when invoked with ["check", file].
  const pidFile = path.join(directory, 'descendant.pid');
  fs.writeFileSync(path.join(directory, 'check'), `
const { spawn } = require('node:child_process');
const fs = require('node:fs');
const child = spawn(process.execPath, ['-e', 'setInterval(() => {}, 1000)'], { stdio: 'inherit', windowsHide: true });
fs.writeFileSync(process.env.LSP_TEST_PID_FILE, String(child.pid));
setInterval(() => {}, 1000);
`);
  const diagnostic = client({ SIMPLE_BINARY: process.execPath, SIMPLE_LSP_ENABLE_DIAGNOSTICS: '1', LSP_TEST_PID_FILE: pidFile });
  await initialize(diagnostic);
  const response = diagnostic.request('tools/call', { name: 'lsp_diagnostics', arguments: { file: 'fixture.spl' } }, 20000);
  // Attach immediately so early request failures do not become unhandled rejections.
  response.catch(() => {});
  await until(() => fs.existsSync(pidFile), 5000, 'diagnostics never launched the delegate fixture');
  const pid = Number(fs.readFileSync(pidFile, 'utf8'));
  assert(Number.isSafeInteger(pid) && pid > 0, 'invalid tracked descendant PID');
  descendants.add(pid);
  assert.equal(live(pid), true, 'fixture descendant was never live');
  const result = await response;
  assert.match(JSON.stringify(result), /timeout|timed out/i, 'diagnostics must retain timeout failure output');
  await until(() => !live(pid), 3000, `diagnostics leaked owned descendant ${pid}`);
  descendants.delete(pid);
  await diagnostic.request('ping');
  await diagnostic.close();
  passed++;
  console.log(`PASS: ${passed} native lifecycle/cleanup cases`);
}

run().catch(error => {
  console.error(error.stack);
  process.exitCode = 1;
}).finally(async () => {
  // Failure cleanup is restricted to PIDs launched and recorded by this test.
  for (const child of clients) child.kill('SIGKILL');
  for (const pid of descendants) {
    try { process.kill(pid, 'SIGKILL'); } catch (error) { if (error.code !== 'ESRCH') console.error(error); }
  }
  await delay(100);
  fs.rmSync(directory, { recursive: true, force: true });
});
