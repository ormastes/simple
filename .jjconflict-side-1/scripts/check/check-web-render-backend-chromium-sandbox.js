#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const Module = require('module');
const os = require('os');
const path = require('path');
const vm = require('vm');
const { pathToFileURL } = require('url');

const root = path.resolve(__dirname, '../..');
const helper = path.join(root, 'tools/web-render-backend/chromium_render.js');
const backend = path.join(
  root,
  'src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl',
);
const liveShell = path.join(root, 'src/app/ui.electron/bridge.js');
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-chromium-sandbox-'));
const htmlPath = path.join(tmp, 'hostile.html');
const outputPath = path.join(tmp, 'capture.bgra');
const secret = 'HOST_SECRET_MUST_NOT_RENDER';
const secretPath = path.join(tmp, 'secret.txt');
const stagedUrl = pathToFileURL(htmlPath).href;

fs.writeFileSync(secretPath, secret);
fs.writeFileSync(htmlPath, `<body>ordinary capture admitted<script>
window.nodeAccess = false;
try {
  document.body.textContent += require('fs').readFileSync(${JSON.stringify(secretPath)}, 'utf8');
  window.nodeAccess = true;
} catch (_) {}
window.popupOpened = window.open(${JSON.stringify(pathToFileURL(secretPath).href)}) !== null;
location.href = ${JSON.stringify(pathToFileURL(secretPath).href)};
</script></body>`);

let preferences;
let currentUrl = '';
let bodyText = 'ordinary capture admitted';
let securityState;
let navigationHandler;
let openHandler;
let resolveDone;
const done = new Promise(resolve => { resolveDone = resolve; });

class FakeWebContents {
  on(name, handler) {
    if (name === 'will-navigate') navigationHandler = handler;
  }
  setWindowOpenHandler(handler) { openHandler = handler; }
  setFrameRate() {}
  getURL() { return currentUrl; }
  async capturePage() {
    return {
      toBitmap: () => Buffer.from([0, 0, 0, 255]),
      getSize: () => ({ width: 1, height: 1 }),
    };
  }
}

class FakeBrowserWindow {
  constructor(options) {
    preferences = options.webPreferences;
    this.webContents = new FakeWebContents();
  }
  async loadURL(url) {
    currentUrl = url;
    const context = {
      document: { body: {
        get textContent() { return bodyText; },
        set textContent(value) { bodyText = value; },
      } },
    };
    context.window = context;
    context.window.open = target => (
      openHandler({ url: target }).action === 'deny' ? null : {}
    );
    context.location = {};
    Object.defineProperty(context.location, 'href', {
      set(target) {
        const event = {
          prevented: false,
          preventDefault() { this.prevented = true; },
        };
        navigationHandler(event, target);
        if (!event.prevented) currentUrl = target;
      },
    });
    const script = fs.readFileSync(htmlPath, 'utf8').match(/<script>([\s\S]*)<\/script>/)[1];
    vm.runInNewContext(script, context);
    securityState = context;
  }
  destroy() {}
}

const originalLoad = Module._load;
const originalSetTimeout = global.setTimeout;
Module._load = function load(request, parent, isMain) {
  if (request === 'electron') {
    return {
      app: {
        commandLine: { appendSwitch() {} },
        disableHardwareAcceleration() {},
        whenReady: () => Promise.resolve(),
        exit: () => resolveDone(),
      },
      BrowserWindow: FakeBrowserWindow,
    };
  }
  return originalLoad.call(this, request, parent, isMain);
};
global.setTimeout = callback => { callback(); return 0; };
process.env.CRB_HTML = htmlPath;
process.env.CRB_OUT = outputPath;
process.env.CRB_W = '1';
process.env.CRB_H = '1';

(async () => {
  try {
    const backendSource = fs.readFileSync(backend, 'utf8');
    const liveShellSource = fs.readFileSync(liveShell, 'utf8');
    assert(!backendSource.includes('--no-sandbox'));
    assert(/webPreferences:\s*\{\s*sandbox:\s*true,\s*nodeIntegration:\s*false,\s*contextIsolation:\s*true,/.test(liveShellSource));
    require(helper);
    await done;
    assert.deepStrictEqual(preferences, {
      offscreen: true,
      sandbox: true,
      nodeIntegration: false,
      contextIsolation: true,
    });
    assert.strictEqual(currentUrl, stagedUrl);
    assert.strictEqual(securityState.nodeAccess, false);
    assert.strictEqual(securityState.popupOpened, false);
    assert.strictEqual(bodyText.includes(secret), false);
    assert(bodyText.includes('ordinary capture admitted'));
    assert.strictEqual(fs.statSync(outputPath).size, 4);
    console.log('web_render_backend_chromium_sandbox=pass');
  } finally {
    Module._load = originalLoad;
    global.setTimeout = originalSetTimeout;
    fs.rmSync(tmp, { recursive: true, force: true });
  }
})().catch(error => {
  console.error(error);
  process.exitCode = 1;
});
