// Test-only process broker for the Chromium primitive differential oracle.
//
// This uses Electron's supported BrowserWindow/WebContents API; it does not
// bind Blink, Viz, or GPU private ABI.  It is intentionally a child-process
// endpoint for the frozen C ABI bridge, rather than a production renderer.
//
// Usage: electron --no-sandbox chromium_primitive_oracle_broker.js request.json
// A successful invocation writes exactly one Chromium receipt JSON value to
// stdout.  Failure writes diagnostics to stderr and exits non-zero.

'use strict';

const crypto = require('crypto');
const fs = require('fs');
const { app, BrowserWindow } = require('electron');

const MAX_REQUEST_BYTES = 1024 * 1024;
const REQUIRED = ['rect', 'text', 'image', 'pointer', 'keyboard', 'scroll', 'resize'];

function fail(message) {
  process.stderr.write(`REAL_CHROMIUM_ORACLE_UNAVAILABLE ${message}\n`);
  app.exit(2);
}

function digest(value) {
  return crypto.createHash('sha256').update(value).digest('hex');
}

function scalar(fields) {
  return Object.keys(fields).sort().map((key) => `${key}=${String(fields[key])}`).join(';');
}

function event(sequence, layer, operation, objectId, parentId, result, error, payload, fields, profile) {
  return {
    schema_version: 1, run_id: request.run_id, sequence, monotonic_ns: sequence,
    layer_id: layer, operation, object_id: objectId, parent_id: parentId,
    result_class: result, error_class: error, payload_digest: digest(payload),
    scalar_fields: scalar(fields), environment_profile_id: profile,
  };
}

function center(box) {
  return { x: Math.round(box.left + box.width / 2), y: Math.round(box.top + box.height / 2) };
}

function waitForOracleInput(webContents) {
  return webContents.executeJavaScript(`new Promise((resolve, reject) => {
    const deadline = Date.now() + 1000;
    const check = () => {
      const input = window.__oracle;
      if (input.pointer > 0 && input.ctrlalt > 0 && input.scroll > 0 && input.resize > 0) {
        resolve(input);
        return;
      }
      if (Date.now() >= deadline) {
        reject(new Error('trusted-input-timeout:' + JSON.stringify(input)));
        return;
      }
      requestAnimationFrame(check);
    };
    check();
  })`);
}

// Electron prepends its app/script argument differently from node, while the
// request file is always the final argument in the launcher contract.
const requestPath = process.argv[process.argv.length - 1];
if (!requestPath) fail('request-path-required');
let request;
try {
  const bytes = fs.readFileSync(requestPath);
  if (bytes.length === 0 || bytes.length > MAX_REQUEST_BYTES) fail('request-size-out-of-range');
  request = JSON.parse(bytes.toString('utf8'));
} catch (error) {
  fail(`invalid-request:${error.message}`);
}
if (!Array.isArray(request.primitives) || !REQUIRED.every((name) => request.primitives.includes(name))) {
  fail('primitive-subset-required');
}
if (request.schema_version !== 1 || typeof request.run_id !== 'string' || typeof request.environment_profile_id !== 'string') {
  fail('schema-v1-run-and-environment-required');
}

app.commandLine.appendSwitch('force-color-profile', 'srgb');
// Match chromium_render.js: CPU capture is still a genuine Chromium paint
// receipt on hosts without a usable Viz/GPU compositor.  The GPU layer below
// remains unavailable and cannot be promoted as offload/readback evidence.
app.disableHardwareAcceleration();
app.whenReady().then(async () => {
  const width = Number(request.viewport_width || 480);
  const height = Number(request.viewport_height || 320);
  if (!Number.isInteger(width) || !Number.isInteger(height) || width < 1 || height < 1 || width > 4096 || height > 4096) {
    fail('viewport-out-of-range');
    return;
  }
  const win = new BrowserWindow({
    // This oracle deliberately uses a headful Xvfb window.  Offscreen
    // rendering did not deliver wheel/viewport events to the renderer.
    width, height, show: true,
    webPreferences: { sandbox: true, nodeIntegration: false, contextIsolation: true },
    backgroundColor: '#ffffff',
  });
  try {
    const dataImage = 'data:image/gif;base64,R0lGODlhAQABAIAAAAAAAP///ywAAAAAAQABAAACAUwAOw==';
    await win.loadURL(`data:text/html,${encodeURIComponent(`<!doctype html><meta charset=utf-8>
      <style>body{margin:0;font:16px sans-serif}#rect{width:80px;height:40px;background:#2468ac;border:3px solid #135}#scroll{height:30px;overflow:scroll}#content{height:120px}#img{width:1px;height:1px}</style>
      <div id=rect>text</div><img id=img src="${dataImage}"><div id=scroll><div id=content>scroll</div></div><input id=key value=""><script>
      const rectBox=document.getElementById('rect');
      const keyBox=document.getElementById('key');
      const scrollBox=document.getElementById('scroll');
      window.__oracle={pointer:0,pointerTrusted:false,ctrlalt:0,ctrlaltTrusted:false,scroll:0,scrollTrusted:false,resize:0,resizeTrusted:false};
      rectBox.addEventListener('click',e=>{window.__oracle.pointer++;window.__oracle.pointerTrusted=e.isTrusted});
      keyBox.addEventListener('keydown',e=>{if(e.ctrlKey&&e.altKey){window.__oracle.ctrlalt++;window.__oracle.ctrlaltTrusted=e.isTrusted}});
      scrollBox.addEventListener('scroll',e=>{window.__oracle.scroll++;window.__oracle.scrollTrusted=e.isTrusted});
      addEventListener('resize',e=>{window.__oracle.resize++;window.__oracle.resizeTrusted=e.isTrusted});
      </script>`)}`);
    win.show();
    win.focus();
    win.webContents.focus();
    const targets = await win.webContents.executeJavaScript(`(() => ({rect:(() => {const r=rect.getBoundingClientRect();return {left:r.left,top:r.top,width:r.width,height:r.height}})(), key:(() => {const r=key.getBoundingClientRect();return {left:r.left,top:r.top,width:r.width,height:r.height}})(), scroll:(() => {const r=document.getElementById('scroll').getBoundingClientRect();return {left:r.left,top:r.top,width:r.width,height:r.height}})()}))()`);
    const rectPoint = center(targets.rect);
    win.webContents.sendInputEvent({ type: 'mouseMove', x: rectPoint.x, y: rectPoint.y });
    win.webContents.sendInputEvent({ type: 'mouseDown', x: rectPoint.x, y: rectPoint.y, button: 'left', clickCount: 1 });
    win.webContents.sendInputEvent({ type: 'mouseUp', x: rectPoint.x, y: rectPoint.y, button: 'left', clickCount: 1 });
    const keyPoint = center(targets.key);
    win.webContents.sendInputEvent({ type: 'mouseDown', x: keyPoint.x, y: keyPoint.y, button: 'left', clickCount: 1 });
    win.webContents.sendInputEvent({ type: 'mouseUp', x: keyPoint.x, y: keyPoint.y, button: 'left', clickCount: 1 });
    win.webContents.sendInputEvent({ type: 'keyDown', keyCode: 'A', modifiers: ['control', 'alt'] });
    win.webContents.sendInputEvent({ type: 'keyUp', keyCode: 'A', modifiers: ['control', 'alt'] });
    // CDP input marks the wheel event trusted; do not emulate it by mutating
    // scrollTop or dispatching a synthetic DOM event.
    const cdp = win.webContents.debugger;
    cdp.attach('1.3');
    const scrollPoint = center(targets.scroll);
    await cdp.sendCommand('Input.dispatchMouseEvent', {
      type: 'mouseMoved', x: scrollPoint.x, y: scrollPoint.y, button: 'none', buttons: 0,
    });
    await cdp.sendCommand('Input.dispatchMouseEvent', {
      type: 'mouseWheel', x: scrollPoint.x, y: scrollPoint.y,
      deltaX: 0, deltaY: 40, button: 'none', buttons: 0, pointerType: 'mouse',
    });
    // A BrowserWindow content-bounds change is the canonical native resize
    // source and changes the renderer viewport rather than only window chrome.
    const bounds = win.getContentBounds();
    const resized = new Promise((resolve) => win.once('resize', resolve));
    win.setContentBounds({ x: bounds.x, y: bounds.y, width: bounds.width + 1, height: bounds.height + 1 });
    await resized;
    await waitForOracleInput(win.webContents);
    const [dom, bitmap] = await Promise.all([
      win.webContents.executeJavaScript(`(() => { const rectBox=document.getElementById('rect'), imageBox=document.getElementById('img'), scrollBox=document.getElementById('scroll'), r=rectBox.getBoundingClientRect(), i=imageBox.getBoundingClientRect(); return {rect:[r.left,r.top,r.width,r.height],text:getComputedStyle(rectBox).font,image:[i.width,i.height],scroll:scrollBox.scrollTop,input:window.__oracle}; })()`),
      win.webContents.capturePage(),
    ]);
    if (!dom.input.pointerTrusted || !dom.input.ctrlaltTrusted || !dom.input.scrollTrusted || !dom.input.resizeTrusted) {
      throw new Error(`untrusted-input-receipt:${JSON.stringify(dom.input)}`);
    }
    let gpuStatus = {};
    let gpuInfo = {};
    let gpuError = '';
    try {
      [gpuStatus, gpuInfo] = await Promise.all([app.getGPUFeatureStatus(), app.getGPUInfo('basic')]);
    } catch (error) {
      // A CPU-only host is a real, explicit unavailable result; it must not
      // turn an otherwise valid Chromium CPU receipt into fixture output.
      gpuError = String(error.message || error);
    }
    const browser = `electron=${process.versions.electron};chrome=${process.versions.chrome};platform=${process.platform}`;
    const device = gpuError ? 'unavailable' : JSON.stringify(gpuInfo.gpuDevice || gpuInfo.auxAttributes || {});
    const profile = request.environment_profile_id;
    const events = [
      event(0, 'web_dom', 'tree', 'root', '', 'ok', '', JSON.stringify(dom), { tag: 'div' }, profile),
      event(1, 'web_style', 'computed', 'rect', 'root', 'ok', '', dom.text, { border: '3px', font: dom.text }, profile),
      event(2, 'web_layout', 'boxes', 'root', '', 'ok', '', JSON.stringify(dom), { image: `${dom.image[0]}x${dom.image[1]}`, rect: dom.rect.join(','), scroll: dom.scroll }, profile),
      event(3, 'web_paint', 'cpu_readback', 'frame', 'root', 'ok', '', bitmap.toBitmap(), { source: 'electron-capturePage-bgra' }, profile),
      event(4, 'web_input', 'dispatch', 'root', '', 'ok', '', JSON.stringify(dom.input), { ctrlalt: dom.input.ctrlalt, ctrlalt_trusted: dom.input.ctrlaltTrusted, pointer: dom.input.pointer, pointer_trusted: dom.input.pointerTrusted, resize: dom.input.resize, resize_trusted: dom.input.resizeTrusted, scroll: dom.input.scroll, scroll_trusted: dom.input.scrollTrusted }, profile),
      // capturePage proves CPU-visible pixels, not a device-origin GPU readback.
      event(5, 'web_gpu', 'requested', 'frame', 'root', 'unavailable', gpuError ? 'gpu-host-unavailable' : 'no-device-origin-readback', JSON.stringify(gpuStatus), { browser, device_digest: digest(device), receipt: 'unavailable' }, profile),
    ];
    const response = { schema_version: 1, run_id: request.run_id, environment_profile_id: profile,
      ui_environment_profile_id: request.ui_environment_profile_id || 'electron-offscreen', arch: process.arch,
      transport: 'electron-public-api-ipc', enabled_features: ['primitive-v1', 'electron-public-api'],
      venus_version: 'n/a', device_identity: device, oracle_identity: browser,
      device_origin_readback: false, fallback_used: false, dropped_events: 0, complete: true, events };
    process.stdout.write(`${JSON.stringify(response)}\n`);
    if (cdp.isAttached()) cdp.detach();
    win.destroy();
    app.exit(0);
  } catch (error) {
    if (win.webContents.debugger.isAttached()) win.webContents.debugger.detach();
    if (!win.isDestroyed()) win.destroy();
    fail(`electron-execution-failed:${error.message}`);
  }
}).catch((error) => fail(`electron-ready-failed:${error.message}`));
