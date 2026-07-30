// Verify the chromium web-render backend is genuinely interactive: load the page
// and exercise a text input and submit button through Chromium's input path.
//
// Env: CRB_HTML (input .html). Prints a JSON result line.
const { app, BrowserWindow } = require('electron');
app.commandLine.appendSwitch('force-color-profile', 'srgb');
app.disableHardwareAcceleration();

const htmlPath = process.env.CRB_HTML;

function clickAt(webContents, point) {
  webContents.sendInputEvent({ type: 'mouseMove', x: point.x, y: point.y });
  webContents.sendInputEvent({
    type: 'mouseDown', x: point.x, y: point.y, button: 'left', clickCount: 1
  });
  webContents.sendInputEvent({
    type: 'mouseUp', x: point.x, y: point.y, button: 'left', clickCount: 1
  });
}

app.whenReady().then(async () => {
  const win = new BrowserWindow({ width: 800, height: 600, show: true,
    webPreferences: { sandbox: false } });
  await win.loadFile(htmlPath);
  await new Promise(r => setTimeout(r, 300));
  const targets = await win.webContents.executeJavaScript(`(function(){
    const out = {
      text_focus_events: 0,
      text_beforeinput_events: 0,
      text_input_events: 0,
      button_clicks: 0,
      submit_events: 0
    };
    window.__chromiumEventCheck = out;

    const name = document.getElementById('name');
    out.text_input_found = !!name;
    if (name) {
      window.__chromiumTextFocus = new Promise(resolve => {
        const timeout = setTimeout(() => resolve(false), 500);
        name.addEventListener('focus', () => {
          clearTimeout(timeout);
          resolve(true);
        }, { once: true });
      });
      name.addEventListener('focus', event => {
        out.text_focus_events++;
        out.text_focus_trusted = event.isTrusted;
      });
      name.addEventListener('beforeinput', event => {
        out.text_beforeinput_events++;
        out.text_beforeinput_trusted = event.isTrusted;
        out.text_beforeinput_type = event.inputType;
      });
      name.addEventListener('input', event => {
        out.text_input_events++;
        out.text_input_trusted = event.isTrusted;
        out.text_input_type = event.inputType;
      });
      name.scrollIntoView({ block: 'center' });
    }

    const btn = document.querySelector('button[type="submit"], input[type="submit"]');
    out.button_found = !!btn;
    if (btn) {
      out.button_id = btn.id;
      out.button_tag = btn.tagName.toLowerCase();
      out.button_type = btn.type;
      btn.addEventListener('click', event => {
        out.button_clicks++;
        out.button_click_trusted = event.isTrusted;
        out.button_click_default_prevented = event.defaultPrevented;
      });
      document.addEventListener('submit', event => {
        out.submit_events++;
        out.submit_trusted = event.isTrusted;
        out.submit_cancelable = event.cancelable;
        out.submit_default_prevented_before_cancel = event.defaultPrevented;
        out.submitter_matches_button = event.submitter === btn;
        out.submitter_id = event.submitter ? event.submitter.id : '';
        out.submitter_tag = event.submitter ? event.submitter.tagName.toLowerCase() : '';
        out.submitter_type = event.submitter ? event.submitter.type : '';
        event.preventDefault();
        out.submit_default_prevented = event.defaultPrevented;
        out.submit_canceled = event.cancelable && event.defaultPrevented;
      }, true);
    }

    function center(element) {
      if (!element) return null;
      const rect = element.getBoundingClientRect();
      return { x: Math.round(rect.left + rect.width / 2),
        y: Math.round(rect.top + rect.height / 2) };
    }
    return { textPoint: center(name), buttonFound: !!btn };
  })();`);

  win.focus();
  win.webContents.focus();
  if (targets.textPoint) {
    clickAt(win.webContents, targets.textPoint);
    await win.webContents.executeJavaScript(`window.__chromiumTextFocus`);
    await win.webContents.executeJavaScript(
      `(function(){
        const name = document.getElementById('name');
        window.__chromiumEventCheck.text_focused = document.activeElement === name;
        name.select();
        return true;
      })();`
    );
    await win.webContents.insertText('Hello Simple');
  }

  const buttonPoint = targets.buttonFound
    ? await win.webContents.executeJavaScript(`(function(){
        const btn = document.querySelector('button[type="submit"], input[type="submit"]');
        btn.scrollIntoView({ block: 'center' });
        const rect = btn.getBoundingClientRect();
        return { x: Math.round(rect.left + rect.width / 2),
          y: Math.round(rect.top + rect.height / 2) };
      })();`)
    : null;
  if (buttonPoint) clickAt(win.webContents, buttonPoint);
  await new Promise(r => setTimeout(r, 100));

  const result = await win.webContents.executeJavaScript(`(function(){
    const out = window.__chromiumEventCheck;
    const name = document.getElementById('name');
    out.text_value = name ? name.value : '';
    if (out.text_focused === undefined) out.text_focused = false;
    out.pass = out.text_input_found &&
      out.text_focused &&
      out.text_focus_events > 0 &&
      out.text_focus_trusted === true &&
      out.text_beforeinput_events > 0 &&
      out.text_beforeinput_trusted === true &&
      out.text_input_events > 0 &&
      out.text_input_trusted === true &&
      out.text_value === 'Hello Simple' &&
      out.button_found &&
      out.button_clicks > 0 &&
      out.button_click_trusted === true &&
      out.submit_events > 0 &&
      out.submit_trusted === true &&
      out.submitter_matches_button === true &&
      out.submit_default_prevented_before_cancel === false &&
      out.submit_canceled === true;
    return out;
  })();`);
  await new Promise(resolve => {
    process.stdout.write('EVENT_CHECK ' + JSON.stringify(result) + '\n', resolve);
  });
  win.destroy();
  app.exit(result.pass ? 0 : 1);
});
