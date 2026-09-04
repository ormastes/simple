'use strict';

const fs = require('fs');

const port = Number(process.argv[2]);
const expectedUrl = process.argv[3];
const proofPath = process.argv[4];

function fail(reason) {
  if (proofPath && !fs.existsSync(proofPath)) {
    fs.writeFileSync(proofPath, JSON.stringify({ok: false, reason}, null, 2) + '\n');
  }
  process.stderr.write(`caret-electron-live: ${reason}\n`);
  process.exit(1);
}

async function pageTarget() {
  for (let attempt = 0; attempt < 40; attempt += 1) {
    try {
      const response = await fetch(`http://127.0.0.1:${port}/json`);
      const targets = await response.json();
      const target = targets.find((item) => item.type === 'page' && item.url === expectedUrl);
      if (target && target.webSocketDebuggerUrl) return target;
    } catch (_) {
      // Electron may not have opened its debugger socket yet.
    }
    await new Promise((resolve) => setTimeout(resolve, 250));
  }
  return null;
}

async function evaluate(target) {
  return new Promise((resolve, reject) => {
    const socket = new WebSocket(target.webSocketDebuggerUrl);
    const timer = setTimeout(() => {
      socket.close();
      reject(new Error('dom-evaluation-timeout'));
    }, 15000);
    socket.addEventListener('open', () => {
      socket.send(JSON.stringify({
        id: 1,
        method: 'Runtime.evaluate',
        params: {
          awaitPromise: true,
          returnByValue: true,
          expression: `(async () => {
            const prompt = document.querySelector('#prompt');
            const form = document.querySelector('#chat-form');
            if (!prompt || !form) return {ok:false, reason:'caret-dom-missing'};
            prompt.value = 'test';
            prompt.dispatchEvent(new Event('input', {bubbles:true}));
            form.requestSubmit();
            for (let i = 0; i < 80; i += 1) {
              const user = document.querySelector('.message.user');
              const assistant = document.querySelector('.message.assistant');
              if (user && assistant) return {
                ok: document.title === 'LLM Caret' &&
                    user.textContent === 'test' && assistant.textContent === 'hello',
                title: document.title,
                user: user.textContent,
                assistant: assistant.textContent
              };
              await new Promise((done) => setTimeout(done, 100));
            }
            return {ok:false, reason:'assistant-not-rendered'};
          })()`
        }
      }));
    });
    socket.addEventListener('message', (event) => {
      const message = JSON.parse(String(event.data));
      if (message.id !== 1) return;
      clearTimeout(timer);
      socket.close();
      if (message.error) reject(new Error(message.error.message));
      else resolve(message.result.result.value);
    });
    socket.addEventListener('error', () => {
      clearTimeout(timer);
      reject(new Error('devtools-websocket-error'));
    });
  });
}

(async () => {
  if (!Number.isInteger(port) || port <= 0 || !expectedUrl || !proofPath) {
    fail('invalid-arguments');
  }
  if (fs.existsSync(proofPath)) fs.unlinkSync(proofPath);
  const target = await pageTarget();
  if (!target) fail('caret-page-target-missing');
  try {
    const result = await evaluate(target);
    const proof = {ok: result.ok === true, url: target.url, ...result};
    fs.writeFileSync(proofPath, JSON.stringify(proof, null, 2) + '\n');
    if (!proof.ok) fail(proof.reason || 'visible-turn-mismatch');
    process.stdout.write('caret-electron-live: PASS user=test assistant=hello\n');
  } catch (error) {
    fail(error.message || 'unknown-error');
  }
})();
