// Verify the Simple WM browser bridge routes real Chromium DOM events into
// window_cmd and input_event frames. This runs the repo's actual wm.js in an
// Electron/Chromium page and uses electron-ipc mode so no server is required.
//
// Prints: WM_EVENT_CHECK {json}
const { app, BrowserWindow } = require('electron');
const fs = require('fs');
const os = require('os');
const path = require('path');
const crypto = require('crypto');
const { pathToFileURL } = require('url');

const FONT_TEXT = 'WEB';
const FONT_COMPOSITION_ID = 'html-layout';
const FONT_IDENTITY = 'sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081;axes=wght=400,wdth=100';
const EXPECTED_RUN_ID = process.env.SIMPLE_WEB_FONT_RUN_ID || '';

app.commandLine.appendSwitch('force-color-profile', 'srgb');
app.disableHardwareAcceleration();

function escapeScriptEnd(source) {
  return String(source || '').replace(/<\/script/gi, '<\\/script');
}

function loadCompositionReceipt(root) {
  if (!/^[A-Za-z0-9._:-]+$/.test(EXPECTED_RUN_ID)) {
    throw new Error('missing or invalid SIMPLE_WEB_FONT_RUN_ID');
  }
  const receiptPath = process.env.SIMPLE_WEB_FONT_COMPOSITION_RECEIPT ||
    path.join(root, 'build/test-artifacts/simple-web-font-composition/receipt.env');
  const fields = Object.fromEntries(
    fs.readFileSync(receiptPath, 'utf8').split(/\r?\n/).filter(Boolean).map(line => {
      const split = line.indexOf('=');
      return [line.slice(0, split), line.slice(split + 1)];
    })
  );
  if (fields.schema !== 'simple-web-font-composition-v1' ||
      fields.status !== 'pass' ||
      fields.run_id !== EXPECTED_RUN_ID ||
      fields.producer !== 'pure-simple-html-webir-drawir-engine2d' ||
      fields.composition_id !== FONT_COMPOSITION_ID ||
      fields.text !== FONT_TEXT ||
      fields.font_identity !== FONT_IDENTITY) {
    throw new Error('invalid Simple Web font composition receipt');
  }
  const artifactPath = path.resolve(root, fields.pixel_artifact_path || '');
  const artifactBytes = fs.readFileSync(artifactPath);
  const artifact = JSON.parse(artifactBytes.toString('utf8'));
  const checksum = artifact.pixels.reduce(
    (sum, pixel, index) => (sum + Number(pixel) * (index + 1)) % 2147483647, 0
  );
  const sha256 = crypto.createHash('sha256').update(artifactBytes).digest('hex');
  if (artifact.producer !== fields.producer ||
      artifact.format !== 'argb-u32' ||
      artifact.width !== Number(fields.viewport_width) ||
      artifact.height !== Number(fields.viewport_height) ||
      artifact.pixels.length !== Number(fields.pixel_count) ||
      checksum !== Number(fields.pixel_checksum) ||
      artifactBytes.length !== Number(fields.pixel_artifact_size_bytes) ||
      sha256 !== fields.pixel_artifact_sha256) {
    throw new Error('invalid Simple Web font composition artifact');
  }
  return { ...fields, receipt_path: receiptPath, artifact_path: artifactPath };
}

function makeHtml(root, receipt) {
  const wmJs = fs.readFileSync(path.join(root, 'src/app/ui.web/wm.js'), 'utf8');
  const fontUrl = pathToFileURL(path.join(root, 'assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf')).href;
  return `<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <style>
    @font-face { font-family: SimplePinnedMono; src: url('${fontUrl}') format('truetype'); font-style: normal; font-weight: 400; }
    html, body { margin: 0; width: 800px; height: 600px; background: #f8fafc; }
    #wm-desktop { position: relative; width: 800px; height: 560px; }
    #wm-taskbar { position: absolute; left: 0; top: 560px; width: 800px; height: 40px; }
    .wm-window { position: absolute; border: 1px solid #334155; background: #fff; }
    .wm-titlebar { height: 34px; display: flex; align-items: center; gap: 6px; background: rgb(229, 231, 235); cursor: grab; }
    .wm-titlebar-icon { width: 18px; height: 18px; display: inline-grid; place-items: center; border-radius: 999px; background: rgb(37, 99, 235); color: rgb(255, 255, 255); }
    .wm-title { min-width: 0; color: rgb(17, 24, 39); font-size: 12px; font-weight: 700; }
    .wm-title-input { min-width: 142px; width: 158px; height: 24px; color: rgb(17, 24, 39); background: rgb(241, 245, 249); border: 1px solid rgb(148, 163, 184); cursor: text; }
    .wm-title-context { color: rgb(71, 85, 105); font-size: 11px; }
    .wm-traffic-lights button { width: 18px; height: 18px; border-radius: 999px; border: 0; }
    .wm-btn-close { background: rgb(239, 68, 68); }
    .wm-btn-minimize { background: rgb(234, 179, 8); }
    .wm-btn-maximize { background: rgb(34, 197, 94); }
    .wm-body { padding: 8px; }
  </style>
</head>
<body>
  <div id="wm-desktop"></div>
  <div id="wm-taskbar"></div>
  <script>
    window.__wmFrames = [];
    window.__wmReady = false;
    window.simpleUI = {
      sendFrame(frame) { window.__wmFrames.push(frame); },
      notifyWmReady() { window.__wmReady = true; },
      onNativeWindowEvent() {}
    };
  </script>
  <script>${escapeScriptEnd(wmJs)}</script>
  <script>
    window.simpleWM = new SimpleWindowManager({
      transport: 'electron-ipc',
      rendererModuleUrl: './missing-retained-renderer.js'
    });
  </script>
</body>
</html>`;
}

async function main() {
  const root = process.env.SIMPLE_REPO_ROOT || process.cwd();
  const receipt = loadCompositionReceipt(root);
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-wm-event-check-'));
  const htmlPath = path.join(tmpDir, 'wm_event_check.html');
  fs.writeFileSync(htmlPath, makeHtml(root, receipt));

  await app.whenReady();
  const win = new BrowserWindow({
    width: 800,
    height: 600,
    show: false,
    webPreferences: { offscreen: true, sandbox: false },
    backgroundColor: '#ffffff',
  });
  await win.loadFile(htmlPath);
  await win.webContents.executeJavaScript(`new Promise((resolve, reject) => {
    const startedAt = Date.now();
    const poll = () => {
      if (window.__wmReady && window.simpleWM) {
        resolve(true);
        return;
      }
      if (Date.now() - startedAt > 3000) {
        reject(new Error('timed out waiting for SimpleWindowManager'));
        return;
      }
      requestAnimationFrame(poll);
    };
    poll();
  })`);

  const result = await win.webContents.executeJavaScript(`(async function(){
    const out = {
      target: 'electron',
      surface_id: 'wm-browser-event-routing',
      proof_source: 'tools/web-render-backend/wm_event_check.js',
      browser_engine: 'chromium',
      electron_user_agent: navigator.userAgent,
      ready: !!window.__wmReady
    };
    const wm = window.simpleWM;
    out.wm_found = !!wm;
    if (!wm) return out;

    wm.receiveElectronMessage({
      type: 'openWindow',
      windowId: 'win1',
      title: 'Terminal',
      appId: 'terminal',
      x: 50,
      y: 60,
      width: 320,
      height: 220,
      html: '<div id="font-proof" style="display:inline-block;font-family:SimplePinnedMono,monospace;font-size:16px;line-height:20px;color:#111827">${receipt.text}</div><input id="field" data-canonical-id="win1#field" value=""><button id="ok" data-canonical-id="win1#ok">OK</button>'
    });
    await new Promise((resolve, reject) => {
      const startedAt = Date.now();
      const poll = () => {
        if (document.querySelector('.wm-titlebar') && document.querySelector('#field') && document.querySelector('#ok')) {
          resolve(true);
          return;
        }
        if (Date.now() - startedAt > 3000) {
          reject(new Error('timed out waiting for MDI window DOM'));
          return;
        }
        requestAnimationFrame(poll);
      };
      poll();
    });

    function eventTarget(selector) {
      const el = document.querySelector(selector);
      if (!el) throw new Error('missing selector ' + selector);
      return el;
    }
    function dispatch(el, type, init) {
      const Ctor = type.startsWith('pointer') && window.PointerEvent ? PointerEvent : MouseEvent;
      el.dispatchEvent(new Ctor(type, Object.assign({ bubbles: true, cancelable: true, button: 0 }, init || {})));
    }
    function frames(kind, cmd) {
      return window.__wmFrames.filter(f => {
        if (kind && f.t !== kind) return false;
        if (!cmd) return true;
        return f.payload && (f.payload.kind === cmd || f.payload.cmd_type === cmd || f.payload.event?.kind === cmd);
      });
    }
    function frameName(frame) {
      const payload = frame && frame.payload ? frame.payload : {};
      const kind = payload.kind || payload.cmd_type || payload.event?.kind || 'unknown';
      return frame && frame.t ? frame.t + ':' + kind : 'unknown:' + kind;
    }

    const titlebar = eventTarget('.wm-titlebar');
    const title = eventTarget('.wm-title');
    const titleInput = eventTarget('.wm-title-input');
    const closeButton = eventTarget('.wm-btn-close');
    const minimizeButton = eventTarget('.wm-btn-minimize');
    const maximizeButton = eventTarget('.wm-btn-maximize');
    const performanceNowAvailable = !!(window.performance && typeof window.performance.now === 'function');
    const perfStart = performanceNowAvailable ? window.performance.now() : 0;
    const animationFrameAvailable = typeof window.requestAnimationFrame === 'function';
    let animationFrameCount = 0;
    const styleProbe = document.createElement('style');
    styleProbe.textContent = '@keyframes simple-wm-proof-pulse { from { opacity: 0.25; } to { opacity: 0.95; } } .simple-wm-proof-animation { animation: simple-wm-proof-pulse 120ms linear 2; }';
    document.head.appendChild(styleProbe);
    const animationProbe = document.createElement('div');
    animationProbe.className = 'simple-wm-proof-animation';
    animationProbe.style.cssText = 'position:fixed;left:-1000px;top:-1000px;width:8px;height:8px;';
    document.body.appendChild(animationProbe);
    if (animationFrameAvailable) {
      await new Promise(resolve => {
        requestAnimationFrame(() => {
          animationFrameCount += 1;
          requestAnimationFrame(() => {
            animationFrameCount += 1;
            resolve();
          });
        });
      });
    }
    const titlebarStyle = getComputedStyle(titlebar);
    const titleStyle = getComputedStyle(title);
    const titleInputStyle = getComputedStyle(titleInput);
    const closeStyle = getComputedStyle(closeButton);
    const minimizeStyle = getComputedStyle(minimizeButton);
    const maximizeStyle = getComputedStyle(maximizeButton);
    const animationProbeStyle = getComputedStyle(animationProbe);
    out.performance_now_available = performanceNowAvailable;
    out.performance_now_delta_ms = performanceNowAvailable ? Math.max(0, window.performance.now() - perfStart) : 0;
    out.animation_frame_available = animationFrameAvailable;
    out.animation_frame_count = animationFrameCount;
    out.css_animation_probe = animationProbeStyle.animationName === 'simple-wm-proof-pulse';
    out.title_text = title.textContent;
    out.title_context_text = eventTarget('.wm-title-context').textContent;
    out.traffic_button_count = document.querySelectorAll('.wm-traffic-lights button').length;
    out.title_input_tag = titleInput.tagName.toLowerCase();
    out.titlebar_height = titlebarStyle.height;
    out.titlebar_display = titlebarStyle.display;
    out.titlebar_cursor = titlebarStyle.cursor;
    out.titlebar_background = titlebarStyle.backgroundColor;
    out.title_color = titleStyle.color;
    out.title_font_weight = Number.parseFloat(titleStyle.fontWeight);
    out.title_input_min_width = titleInputStyle.minWidth;
    out.title_input_width = titleInputStyle.width;
    out.title_input_width_px = Number.parseFloat(titleInputStyle.width);
    out.title_input_height = titleInputStyle.height;
    out.title_input_cursor = titleInputStyle.cursor;
    out.title_input_background = titleInputStyle.backgroundColor;
    out.close_button_background = closeStyle.backgroundColor;
    out.minimize_button_background = minimizeStyle.backgroundColor;
    out.maximize_button_background = maximizeStyle.backgroundColor;
    let inputToPaintMs = 0;
    const interactionStart = performanceNowAvailable ? window.performance.now() : 0;
    const beforeRect = eventTarget('.wm-window').getBoundingClientRect();
    dispatch(titlebar, 'mousedown', { clientX: 90, clientY: 72 });
    dispatch(document, 'mousemove', { clientX: 126, clientY: 98 });
    dispatch(document, 'mouseup', { clientX: 126, clientY: 98 });
    const expectedMoveX = Math.round(beforeRect.x + 36);
    const expectedMoveY = Math.round(beforeRect.y + 26);

    titleInput.value = '/tmp/project';
    titleInput.dispatchEvent(new KeyboardEvent('keydown', { bubbles: true, cancelable: true, key: 'Enter' }));

    maximizeButton.click();

    const bodyInput = eventTarget('#field');
    bodyInput.value = 'Hello Simple';
    bodyInput.dispatchEvent(new Event('input', { bubbles: true }));

    const bodyButton = eventTarget('#ok');
    dispatch(bodyButton, 'pointerdown', { clientX: 80, clientY: 122 });
    dispatch(bodyButton, 'pointerup', { clientX: 80, clientY: 122 });
    if (performanceNowAvailable && animationFrameAvailable) {
      await new Promise(resolve => requestAnimationFrame(resolve));
      inputToPaintMs = Math.max(0, window.performance.now() - interactionStart);
    }

    out.window_cmd_count = frames('window_cmd').length;
    out.input_event_count = frames('input_event').length;
    out.focus_count = frames('window_cmd', 'focus').length;
    out.move_count = frames('window_cmd', 'move').length;
    out.maximize_count = frames('window_cmd', 'maximize').length;
    out.title_command_count = frames('window_cmd', 'title_command').length;
    out.text_input_count = frames('input_event', 'text_input').length;
    out.pointer_down_count = frames('input_event', 'pointer_down').length;
    out.pointer_up_count = frames('input_event', 'pointer_up').length;
    out.input_to_paint_ms = inputToPaintMs;
    out.event_sequence = window.__wmFrames.map(frameName);
    out.move_payload = frames('window_cmd', 'move')[0]?.payload || null;
    out.title_payload = frames('window_cmd', 'title_command')[0]?.payload || null;
    out.text_payload = frames('input_event', 'text_input')[0]?.payload || null;
    out.expected_move_x = expectedMoveX;
    out.expected_move_y = expectedMoveY;
    const fontProof = eventTarget('#font-proof');
    await document.fonts.load('16px SimplePinnedMono', '${FONT_TEXT}');
    const fontRect = fontProof.getBoundingClientRect();
    const fontStyle = getComputedStyle(fontProof);
    out.font_text = fontProof.textContent;
    out.simple_composition_run_id = '${receipt.run_id}';
    out.font_composition_id = '${receipt.composition_id}';
    out.font_identity = '${receipt.font_identity}';
    out.font_family = fontStyle.fontFamily;
    out.font_loaded = document.fonts.check('16px SimplePinnedMono', '${FONT_TEXT}');
    out.simple_composition_receipt_path = '${receipt.receipt_path}';
    out.simple_composition_artifact_path = '${receipt.artifact_path}';
    out.simple_composition_pixel_count = ${receipt.pixel_count};
    out.simple_composition_pixel_checksum = ${receipt.pixel_checksum};
    out.simple_composition_artifact_size_bytes = ${receipt.pixel_artifact_size_bytes};
    out.simple_composition_artifact_sha256 = '${receipt.pixel_artifact_sha256}';
    out.font_rect = {
      x: Math.floor(fontRect.x),
      y: Math.floor(fontRect.y),
      width: Math.ceil(fontRect.width),
      height: Math.ceil(fontRect.height)
    };
    out.font_frame_event_count = window.__wmFrames.length;
    out.font_frame_correlation_id = [out.surface_id, out.simple_composition_run_id, out.font_composition_id, out.font_identity, out.font_text, out.simple_composition_pixel_checksum, out.font_frame_event_count].join('|');
    out.pass = out.ready && out.wm_found &&
      out.focus_count >= 1 &&
      out.move_count >= 1 &&
      out.maximize_count >= 1 &&
      out.title_command_count >= 1 &&
      out.text_input_count >= 1 &&
      out.pointer_down_count >= 1 &&
      out.pointer_up_count >= 1 &&
      out.performance_now_available === true &&
      out.performance_now_delta_ms >= 0 &&
      out.input_to_paint_ms > 0 &&
      out.animation_frame_available === true &&
      out.animation_frame_count >= 2 &&
      out.css_animation_probe === true &&
      out.move_payload.window_id_hint === 'win1' &&
      out.move_payload.source === 'native_event' &&
      Array.isArray(out.event_sequence) &&
      out.event_sequence.join(',') === 'host_wm_pointer:down,window_cmd:focus,window_cmd:move,window_cmd:title_command,window_cmd:maximize,input_event:text_input,input_event:pointer_down,input_event:pointer_up' &&
      out.move_payload.x === expectedMoveX &&
      out.move_payload.y === expectedMoveY &&
      out.title_text === 'Terminal' &&
      out.title_context_text === 'terminal' &&
      out.traffic_button_count === 3 &&
      out.title_input_tag === 'input' &&
      out.titlebar_height === '34px' &&
      out.titlebar_display === 'flex' &&
      out.titlebar_cursor === 'grab' &&
      out.titlebar_background === 'rgb(229, 231, 235)' &&
      out.title_color === 'rgb(17, 24, 39)' &&
      Number(out.title_font_weight) >= 700 &&
      out.title_input_min_width === '142px' &&
      out.title_input_width_px >= 142 &&
      out.title_input_height === '24px' &&
      out.title_input_cursor === 'text' &&
      out.title_input_background === 'rgb(241, 245, 249)' &&
      out.close_button_background === 'rgb(239, 68, 68)' &&
      out.minimize_button_background === 'rgb(234, 179, 8)' &&
      out.maximize_button_background === 'rgb(34, 197, 94)' &&
      out.title_payload.command_text === '/tmp/project' &&
      out.text_payload.event.text === 'Hello Simple' &&
      out.simple_composition_run_id === '${EXPECTED_RUN_ID}' &&
      out.font_text === '${FONT_TEXT}' &&
      out.font_composition_id === '${FONT_COMPOSITION_ID}' &&
      out.font_identity === '${FONT_IDENTITY}' &&
      out.font_family.includes('SimplePinnedMono') &&
      out.font_loaded === true &&
      out.font_frame_event_count === out.event_sequence.length;
    return out;
  })();`);

  const frameDir = process.env.BUILD_DIR || tmpDir;
  fs.mkdirSync(frameDir, { recursive: true });
  const framePath = path.join(frameDir, 'wm-font-frame.bgra');
  const fontRect = result.font_rect || {};
  const frameImage = await win.webContents.capturePage({
    x: Number(fontRect.x) || 0,
    y: Number(fontRect.y) || 0,
    width: Number(fontRect.width) || 1,
    height: Number(fontRect.height) || 1,
  });
  const frameSize = frameImage.getSize();
  const frameBitmap = frameImage.toBitmap();
  fs.writeFileSync(framePath, frameBitmap);
  let frameChecksum = 0;
  let frameNonBackgroundPixels = 0;
  for (let i = 0; i + 3 < frameBitmap.length; i += 4) {
    const b = frameBitmap[i];
    const g = frameBitmap[i + 1];
    const r = frameBitmap[i + 2];
    const a = frameBitmap[i + 3];
    frameChecksum = (frameChecksum + (b + 3 * g + 5 * r + 7 * a) * (i / 4 + 1)) % 2147483647;
    if (a !== 0 && (r !== 255 || g !== 255 || b !== 255)) frameNonBackgroundPixels += 1;
  }
  result.font_frame_path = framePath;
  result.font_frame_width = frameSize.width;
  result.font_frame_height = frameSize.height;
  result.font_frame_byte_count = frameBitmap.length;
  result.font_frame_pixel_checksum = frameChecksum;
  result.font_frame_nonbackground_pixels = frameNonBackgroundPixels;
  result.pass = result.pass &&
    frameSize.width > 0 &&
    frameSize.height > 0 &&
    frameBitmap.length === frameSize.width * frameSize.height * 4 &&
    frameChecksum > 0 &&
    frameNonBackgroundPixels > 0;
  result.electron_process_version = process.versions.electron || '';
  result.chrome_process_version = process.versions.chrome || '';
  console.log('WM_EVENT_CHECK ' + JSON.stringify(result));
  win.destroy();
  app.exit(result.pass ? 0 : 1);
}

main().catch(err => {
  console.error('WM_EVENT_CHECK_ERROR ' + (err && err.stack ? err.stack : err));
  app.exit(1);
});
