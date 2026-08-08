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

const FONT_TEXT = 'WEB';
const FONT_COMPOSITION_ID = 'html-layout';
const FONT_IDENTITY = 'sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081;axes=wght=400,wdth=100';
const EXPECTED_RUN_ID = process.env.SIMPLE_WEB_FONT_RUN_ID || '';
const AETHERIC_PROOF_PATH = process.env.AETHERIC_HOST_WEB_GUI_PROOF || '';

app.commandLine.appendSwitch('force-color-profile', 'srgb');

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

function proofFields(proofPath) {
  const result = {};
  for (const line of fs.readFileSync(proofPath, 'utf8').split(/\r?\n/)) {
    const index = line.indexOf('=');
    if (index > 0) result[line.slice(0, index)] = line.slice(index + 1);
  }
  return result;
}

function loadProductionEnvelope(root) {
  if (!AETHERIC_PROOF_PATH) {
    throw new Error('missing AETHERIC_HOST_WEB_GUI_PROOF');
  }
  const proofPath = path.resolve(root, AETHERIC_PROOF_PATH);
  const proofStat = fs.lstatSync(proofPath);
  if (!proofStat.isFile() || proofStat.isSymbolicLink() || proofStat.nlink > 1) {
    throw new Error('invalid Aetheric production proof artifact');
  }
  const fields = proofFields(proofPath);
  const required = [
    'schema', 'status', 'producer', 'theme_id', 'theme_source_manifest_sha256',
    'theme_material_sha256', 'html_path', 'html_sha256',
    'computed_window_background', 'computed_window_border_color',
    'computed_window_border_radius', 'computed_window_box_shadow',
    'computed_titlebar_backdrop_filter', 'computed_titlebar_webkit_backdrop_filter',
    'computed_inactive_border', 'computed_inactive_shadow',
    'computed_active_border', 'computed_active_shadow',
    'post_action_semantic_state', 'blur_or_tolerance_used',
    'synthetic_fixture', 'raw_source_execution', 'compatibility_renderer'
  ];
  if (required.some(key => !fields[key])) {
    throw new Error('incomplete Aetheric production proof');
  }
  if (fields.schema !== 'aetheric-host-web-gui-v1' ||
      fields.status !== 'pass' ||
      fields.producer !== 'production-html-webir-drawir-electron' ||
      fields.theme_id !== 'aetheric_dark' ||
      !/^[0-9a-f]{64}$/.test(fields.theme_source_manifest_sha256) ||
      !/^[0-9a-f]{64}$/.test(fields.theme_material_sha256) ||
      fields.blur_or_tolerance_used !== 'false' ||
      fields.synthetic_fixture !== 'false' ||
      fields.raw_source_execution !== 'false' ||
      fields.compatibility_renderer !== 'false') {
    throw new Error('Aetheric production proof is not admissible');
  }
  const htmlPath = path.resolve(root, fields.html_path);
  const htmlStat = fs.lstatSync(htmlPath);
  if (!htmlStat.isFile() || htmlStat.isSymbolicLink() || htmlStat.nlink > 1 ||
      crypto.createHash('sha256').update(fs.readFileSync(htmlPath)).digest('hex') !== fields.html_sha256) {
    throw new Error('Aetheric production HTML artifact mismatch');
  }
  return { ...fields, proof_path: proofPath, html_path: htmlPath };
}

function serializeForRenderer(value) {
  return JSON.stringify(value)
    .replace(/</g, '\\u003c')
    .replace(/>/g, '\\u003e')
    .replace(/&/g, '\\u0026')
    .replace(/\u2028/g, '\\u2028')
    .replace(/\u2029/g, '\\u2029');
}

function admittedRendererEnvelope(envelope) {
  const keys = [
    'schema', 'producer', 'proof_path', 'html_path', 'html_sha256', 'theme_id',
    'theme_source_manifest_sha256', 'theme_material_sha256', 'post_action_semantic_state',
    'blur_or_tolerance_used', 'synthetic_fixture', 'raw_source_execution',
    'compatibility_renderer', 'computed_window_background', 'computed_window_border_color',
    'computed_window_border_radius', 'computed_window_box_shadow',
    'computed_titlebar_backdrop_filter', 'computed_titlebar_webkit_backdrop_filter',
    'computed_inactive_border', 'computed_inactive_shadow', 'computed_active_border',
    'computed_active_shadow'
  ];
  return Object.freeze(Object.fromEntries(keys.map(key => [key, envelope[key]])));
}

function makeHtml(root, receipt, envelope) {
  const wmJs = fs.readFileSync(path.join(root, 'src/app/ui.web/wm.js'), 'utf8');
  const html = fs.readFileSync(envelope.html_path, 'utf8');
  if (!html.includes("data-aetheric-production-surface='true'") || !html.match(/<body[^>]*>/i)) {
    throw new Error('Aetheric production HTML surface is missing');
  }
  const injected = `
  <div id="wm-desktop" data-aetheric-event-surface="true"></div>
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
  </script>`;
  return html.replace(/<\/body\s*>/i, injected + '\n</body>');
}

async function main() {
  const root = process.env.SIMPLE_REPO_ROOT || process.cwd();
  const receipt = loadCompositionReceipt(root);
  const envelope = loadProductionEnvelope(root);
  const rendererEnvelope = admittedRendererEnvelope(envelope);
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-wm-event-check-'));
  const htmlPath = path.join(tmpDir, 'wm_event_check.html');
  const preloadPath = path.join(tmpDir, 'wm_event_runtime_preload.js');
  fs.writeFileSync(preloadPath, [
    "const { contextBridge } = require('electron');",
    'contextBridge.exposeInMainWorld("__simpleElectronRuntime", Object.freeze({',
    '  rendererSandboxed: process.sandboxed === true,',
    '}));',
  ].join('\n'));
  fs.writeFileSync(htmlPath, makeHtml(root, receipt, envelope));

  await app.whenReady();
  const win = new BrowserWindow({
    width: 800,
    show: false,
    webPreferences: {
      offscreen: true,
      sandbox: true,
      contextIsolation: true,
      nodeIntegration: false,
      preload: preloadPath,
    },
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
    const productionEnvelope = Object.freeze(${serializeForRenderer(rendererEnvelope)});
    const out = {
      target: 'electron',
      surface_id: 'wm-browser-event-routing',
      proof_source: 'tools/web-render-backend/wm_event_check.js',
      browser_engine: 'chromium',
      electron_user_agent: navigator.userAgent,
      renderer_sandboxed: window.__simpleElectronRuntime?.rendererSandboxed === true,
      ready: !!window.__wmReady,
      production_envelope_schema: productionEnvelope.schema,
      production_envelope_producer: productionEnvelope.producer,
      production_envelope_path: productionEnvelope.proof_path,
      production_html_path: productionEnvelope.html_path,
      production_html_sha256: productionEnvelope.html_sha256,
      theme_id: productionEnvelope.theme_id,
      theme_source_manifest_sha256: productionEnvelope.theme_source_manifest_sha256,
      theme_material_sha256: productionEnvelope.theme_material_sha256,
      production_post_action_semantic_state: productionEnvelope.post_action_semantic_state,
      production_blur_or_tolerance_used: productionEnvelope.blur_or_tolerance_used,
      production_synthetic_fixture: productionEnvelope.synthetic_fixture,
      production_raw_source_execution: productionEnvelope.raw_source_execution,
      production_compatibility_renderer: productionEnvelope.compatibility_renderer
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

    const eventWindow = eventTarget('[data-surface-id="win1"]');
    const titlebar = eventWindow.querySelector('.wm-titlebar');
    const title = eventWindow.querySelector('.wm-title');
    const titleInput = eventWindow.querySelector('.wm-title-input');
    const closeButton = eventWindow.querySelector('.wm-btn-close');
    const minimizeButton = eventWindow.querySelector('.wm-btn-minimize');
    const maximizeButton = eventWindow.querySelector('.wm-btn-maximize');
    if (!titlebar || !title || !titleInput || !closeButton || !minimizeButton || !maximizeButton) {
      throw new Error('missing WM event controls in production envelope');
    }
    const productionWindow = eventTarget('[data-aetheric-production-surface="true"] .wm-window.focused');
    const productionTitlebar = productionWindow.querySelector('.wm-titlebar');
    if (!productionTitlebar) throw new Error('missing Aetheric production titlebar');
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
    const initialAnimationProbeStyle = getComputedStyle(animationProbe);
    const probeAnimation = animationProbe.getAnimations()[0] || null;
    const initialAnimationCurrentTime = probeAnimation &&
      Number.isFinite(Number(probeAnimation.currentTime))
      ? Number(probeAnimation.currentTime)
      : -1;
    const initialAnimationOpacity = Number.parseFloat(initialAnimationProbeStyle.opacity);
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
    const finalAnimationCurrentTime = probeAnimation &&
      Number.isFinite(Number(probeAnimation.currentTime))
      ? Number(probeAnimation.currentTime)
      : -1;
    const finalAnimationOpacity = Number.parseFloat(animationProbeStyle.opacity);
    const animationMotionObserved =
      finalAnimationCurrentTime > initialAnimationCurrentTime ||
      finalAnimationOpacity !== initialAnimationOpacity;
    const productionWindowStyle = getComputedStyle(productionWindow);
    const productionTitlebarStyle = getComputedStyle(productionTitlebar);
    out.performance_now_available = performanceNowAvailable;
    out.performance_now_delta_ms = performanceNowAvailable ? Math.max(0, window.performance.now() - perfStart) : 0;
    out.animation_frame_available = animationFrameAvailable;
    out.animation_frame_count = animationFrameCount;
    out.css_animation_initial_opacity = initialAnimationOpacity;
    out.css_animation_final_opacity = finalAnimationOpacity;
    out.css_animation_initial_current_time_ms = initialAnimationCurrentTime;
    out.css_animation_final_current_time_ms = finalAnimationCurrentTime;
    out.css_animation_motion_observed = animationMotionObserved;
    out.css_animation_probe =
      animationProbeStyle.animationName === 'simple-wm-proof-pulse' &&
      animationMotionObserved;
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
    out.computed_window_background = productionWindowStyle.backgroundColor;
    out.computed_window_border_color = productionWindowStyle.borderColor;
    out.computed_window_border_radius = productionWindowStyle.borderRadius;
    out.computed_window_box_shadow = productionWindowStyle.boxShadow;
    out.computed_titlebar_backdrop_filter = productionTitlebarStyle.backdropFilter;
    out.computed_titlebar_webkit_backdrop_filter = productionTitlebarStyle.webkitBackdropFilter;
    out.computed_inactive_border = getComputedStyle(eventTarget('[data-aetheric-production-surface="true"] .wm-window[data-window-state="inactive"]')).borderColor;
    out.computed_inactive_shadow = getComputedStyle(eventTarget('[data-aetheric-production-surface="true"] .wm-window[data-window-state="inactive"]')).boxShadow;
    out.computed_active_border = productionWindowStyle.borderColor;
    out.computed_active_shadow = productionWindowStyle.boxShadow;
    let inputToPaintMs = 0;
    const interactionStart = performanceNowAvailable ? window.performance.now() : 0;
    const beforeRect = eventWindow.getBoundingClientRect();
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
    out.post_action_semantic_state = eventWindow.style.left === '0px' &&
      eventWindow.style.top === '0px' && eventWindow.style.width === '100%' &&
      eventWindow.style.height === '100%' && bodyInput.value === 'Hello Simple'
      ? 'maximized-and-text-input'
      : 'post-action-state-missing';
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
      out.css_animation_motion_observed === true &&
      out.css_animation_probe === true &&
      out.theme_id === 'aetheric_dark' &&
      out.production_envelope_schema === 'aetheric-host-web-gui-v1' &&
      out.production_envelope_producer === 'production-html-webir-drawir-electron' &&
      out.production_blur_or_tolerance_used === 'false' &&
      out.production_synthetic_fixture === 'false' &&
      out.production_raw_source_execution === 'false' &&
      out.production_compatibility_renderer === 'false' &&
      out.computed_window_background === productionEnvelope.computed_window_background &&
      out.computed_window_border_color === productionEnvelope.computed_window_border_color &&
      out.computed_window_border_radius === productionEnvelope.computed_window_border_radius &&
      out.computed_window_box_shadow === productionEnvelope.computed_window_box_shadow &&
      out.computed_titlebar_backdrop_filter === productionEnvelope.computed_titlebar_backdrop_filter &&
      out.computed_titlebar_webkit_backdrop_filter === productionEnvelope.computed_titlebar_webkit_backdrop_filter &&
      out.computed_inactive_border === productionEnvelope.computed_inactive_border &&
      out.computed_inactive_shadow === productionEnvelope.computed_inactive_shadow &&
      out.computed_active_border === productionEnvelope.computed_active_border &&
      out.computed_active_shadow === productionEnvelope.computed_active_shadow &&
      out.post_action_semantic_state === 'maximized-and-text-input' &&
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
      out.titlebar_display === 'flex' &&
      out.title_input_width_px > 0 &&
      out.title_input_height !== 'auto' &&
      out.title_input_cursor === 'text' &&
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
  const gpuFeatureStatus = app.getGPUFeatureStatus();
  result.gpu_feature_status = {
    gpu_compositing: gpuFeatureStatus.gpu_compositing || '',
    webgl: gpuFeatureStatus.webgl || '',
  };
  result.pass = result.pass &&
    result.renderer_sandboxed === true &&
    result.gpu_feature_status.gpu_compositing === 'enabled' &&
    result.gpu_feature_status.webgl === 'enabled' &&
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
