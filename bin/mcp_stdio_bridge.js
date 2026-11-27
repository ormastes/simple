#!/usr/bin/env node
const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');

const sep = process.argv.indexOf('--');
if (sep < 0 || sep === process.argv.length - 1) {
  process.exit(2);
}

const childCmd = process.argv[sep + 1];
const childArgs = process.argv.slice(sep + 2);
const cwd = process.cwd();
const logDir = path.join(cwd, '.simple', 'logs');
fs.mkdirSync(logDir, { recursive: true });
const logPath = path.join(logDir, 'mcp_stdio_bridge.log');

let clientMode = 'framed';
let inBuf = Buffer.alloc(0);
let childBuf = '';

const child = spawn(childCmd, childArgs, {
  cwd,
  env: { ...process.env },
  stdio: ['pipe', 'pipe', 'pipe'],
});

// This bridge owns only this direct child. Never signal by name or enumerate PIDs.
let stopping = false;
let childExited = false;
let failureCode = null;
let terminateTimer;
let killTimer;

function stopOwnedChild(code = null) {
  if (code !== null) failureCode = code;
  if (stopping) return;
  stopping = true;
  process.stdin.pause();
  child.stdin.end();
  terminateTimer = setTimeout(() => {
    if (childExited) return;
    child.kill('SIGTERM');
    killTimer = setTimeout(() => {
      if (!childExited) child.kill('SIGKILL');
    }, 1000);
  }, 1000);
}

function clearShutdownTimers() {
  clearTimeout(terminateTimer);
  clearTimeout(killTimer);
}

function log(line) {
  fs.appendFileSync(logPath, `${new Date().toISOString()} ${line}\n`);
}

function emit(body) {
  if (clientMode === 'jsonl') {
    process.stdout.write(body + '\n');
  } else {
    const len = Buffer.byteLength(body);
    process.stdout.write(`Content-Length: ${len}\r\n\r\n${body}`);
  }
}

function forwardMessage(body) {
  if (stopping || childExited) return;
  child.stdin.write(body.trimEnd() + '\n');
}

function parseInput() {
  while (inBuf.length > 0) {
    const text = inBuf.toString('utf8');
    if (text.startsWith('Content-Length:')) {
      clientMode = 'framed';
      let headerEnd = text.indexOf('\r\n\r\n');
      let sepLen = 4;
      if (headerEnd < 0) {
        headerEnd = text.indexOf('\n\n');
        sepLen = 2;
      }
      if (headerEnd < 0) return;
      const match = text.slice(0, headerEnd).match(/Content-Length:\s*(\d+)/i);
      if (!match) {
        inBuf = Buffer.alloc(0);
        return;
      }
      const bodyStart = Buffer.byteLength(text.slice(0, headerEnd + sepLen));
      const len = Number(match[1]);
      if (inBuf.length < bodyStart + len) return;
      const body = inBuf.slice(bodyStart, bodyStart + len).toString('utf8');
      inBuf = inBuf.slice(bodyStart + len);
      forwardMessage(body);
      continue;
    }

    const nl = text.indexOf('\n');
    if (nl < 0) return;
    clientMode = 'jsonl';
    const line = text.slice(0, nl).trim();
    inBuf = inBuf.slice(Buffer.byteLength(text.slice(0, nl + 1)));
    if (line !== '') forwardMessage(line);
  }
}

function parseChild() {
  while (childBuf.length > 0) {
    if (childBuf.startsWith('Content-Length:')) {
      let headerEnd = childBuf.indexOf('\r\n\r\n');
      let sepLen = 4;
      if (headerEnd < 0) {
        headerEnd = childBuf.indexOf('\n\n');
        sepLen = 2;
      }
      if (headerEnd < 0) return;
      const match = childBuf.slice(0, headerEnd).match(/Content-Length:\s*(\d+)/i);
      if (!match) {
        childBuf = '';
        return;
      }
      const start = headerEnd + sepLen;
      const len = Number(match[1]);
      if (childBuf.length < start + len) return;
      emit(childBuf.slice(start, start + len));
      childBuf = childBuf.slice(start + len);
      continue;
    }

    const nl = childBuf.indexOf('\n');
    if (nl < 0) return;
    const line = childBuf.slice(0, nl).trim();
    childBuf = childBuf.slice(nl + 1);
    if (line !== '') emit(line);
  }
}

process.stdin.on('data', chunk => {
  inBuf = Buffer.concat([inBuf, chunk]);
  parseInput();
});
process.stdin.on('end', () => stopOwnedChild());
process.stdin.on('error', () => stopOwnedChild(1));
process.stdout.on('error', () => stopOwnedChild(1));
process.on('SIGTERM', () => stopOwnedChild(143));
process.on('SIGINT', () => stopOwnedChild(130));
child.stdin.on('error', () => stopOwnedChild(1));

child.stdout.on('data', chunk => {
  childBuf += chunk.toString('utf8');
  parseChild();
});
child.stderr.on('data', chunk => log(`child-stderr ${chunk.toString('utf8').trim()}`));
child.on('error', err => {
  log(`child-error ${err.message}`);
  stopOwnedChild(1);
});
child.on('exit', () => {
  childExited = true;
  clearShutdownTimers();
});
// close also follows spawn failure (which need not emit exit), and waits for pipes.
child.on('close', code => {
  childExited = true;
  clearShutdownTimers();
  process.stdin.destroy();
  if (childBuf.trim() !== '') parseChild();
  const exitCode = failureCode ?? (code === null ? 1 : code);
  if (process.stdout.destroyed) {
    process.exit(exitCode);
  } else {
    process.stdout.write('', () => process.exit(exitCode));
  }
});
