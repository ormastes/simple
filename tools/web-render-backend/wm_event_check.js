// Verify the Simple WM browser bridge routes real Chromium DOM events into
// window_cmd and input_event frames. This runs the repo's actual wm.js in an
// Electron/Chromium page and uses electron-ipc mode so no server is required.
//
// Prints: WM_EVENT_CHECK {json}
const { app, BrowserWindow } = require('electron');
const fs = require('fs');
const os = require('os');
const path = require('path');

app.commandLine.appendSwitch('force-color-profile', 'srgb');
app.disableHardwareAcceleration();

function escapeScriptEnd(source) {
  return String(source || '').replace(/<\/script/gi, '<\\/script');
}

function makeHtml(root) {
  const wmJs = fs.readFileSync(path.join(root, 'src/app/ui.web/wm.js'), 'utf8');
  return `<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <style>
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
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-wm-event-check-'));
  const htmlPath = path.join(tmpDir, 'wm_event_check.html');
  fs.writeFileSync(htmlPath, makeHtml(root));

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
    const out = { ready: !!window.__wmReady };
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
      html: '<input id="field" data-canonical-id="win1#field" value=""><button id="ok" data-canonical-id="win1#ok">OK</button>'
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

    const titlebar = eventTarget('.wm-titlebar');
    const title = eventTarget('.wm-title');
    const titleInput = eventTarget('.wm-title-input');
    const closeButton = eventTarget('.wm-btn-close');
    const minimizeButton = eventTarget('.wm-btn-minimize');
    const maximizeButton = eventTarget('.wm-btn-maximize');
    const titlebarStyle = getComputedStyle(titlebar);
    const titleStyle = getComputedStyle(title);
    const titleInputStyle = getComputedStyle(titleInput);
    const closeStyle = getComputedStyle(closeButton);
    const minimizeStyle = getComputedStyle(minimizeButton);
    const maximizeStyle = getComputedStyle(maximizeButton);
    out.title_text = title.textContent;
    out.title_context_text = eventTarget('.wm-title-context').textContent;
    out.traffic_button_count = document.querySelectorAll('.wm-traffic-lights button').length;
    out.title_input_tag = titleInput.tagName.toLowerCase();
    out.titlebar_height = titlebarStyle.height;
    out.titlebar_display = titlebarStyle.display;
    out.titlebar_cursor = titlebarStyle.cursor;
    out.titlebar_background = titlebarStyle.backgroundColor;
    out.title_color = titleStyle.color;
    out.title_font_weight = titleStyle.fontWeight;
    out.title_input_min_width = titleInputStyle.minWidth;
    out.title_input_width = titleInputStyle.width;
    out.title_input_width_px = Number.parseFloat(titleInputStyle.width);
    out.title_input_height = titleInputStyle.height;
    out.title_input_cursor = titleInputStyle.cursor;
    out.title_input_background = titleInputStyle.backgroundColor;
    out.close_button_background = closeStyle.backgroundColor;
    out.minimize_button_background = minimizeStyle.backgroundColor;
    out.maximize_button_background = maximizeStyle.backgroundColor;
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

    out.window_cmd_count = frames('window_cmd').length;
    out.input_event_count = frames('input_event').length;
    out.focus_count = frames('window_cmd', 'focus').length;
    out.move_count = frames('window_cmd', 'move').length;
    out.maximize_count = frames('window_cmd', 'maximize').length;
    out.title_command_count = frames('window_cmd', 'title_command').length;
    out.text_input_count = frames('input_event', 'text_input').length;
    out.pointer_down_count = frames('input_event', 'pointer_down').length;
    out.pointer_up_count = frames('input_event', 'pointer_up').length;
    out.move_payload = frames('window_cmd', 'move')[0]?.payload || null;
    out.title_payload = frames('window_cmd', 'title_command')[0]?.payload || null;
    out.text_payload = frames('input_event', 'text_input')[0]?.payload || null;
    out.expected_move_x = expectedMoveX;
    out.expected_move_y = expectedMoveY;
    out.pass = out.ready && out.wm_found &&
      out.focus_count >= 1 &&
      out.move_count >= 1 &&
      out.maximize_count >= 1 &&
      out.title_command_count >= 1 &&
      out.text_input_count >= 1 &&
      out.pointer_down_count >= 1 &&
      out.pointer_up_count >= 1 &&
      out.move_payload.window_id_hint === 'win1' &&
      out.move_payload.source === 'native_event' &&
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
      out.text_payload.event.text === 'Hello Simple';
    return out;
  })();`);

  console.log('WM_EVENT_CHECK ' + JSON.stringify(result));
  win.destroy();
  app.exit(result.pass ? 0 : 1);
}

main().catch(err => {
  console.error('WM_EVENT_CHECK_ERROR ' + (err && err.stack ? err.stack : err));
  app.exit(1);
});
