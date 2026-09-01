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

function pixelsDiffer(before, after) {
  return !before.toBitmap().equals(after.toBitmap());
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

  await win.webContents.executeJavaScript(`(function(){
    function waitFrames(count, label) {
      return new Promise((resolve, reject) => {
        let seen = 0;
        const timeout = setTimeout(() => reject(new Error(label + '-timeout')), 1000);
        const tick = () => {
          seen += 1;
          if (seen >= count) {
            clearTimeout(timeout);
            resolve();
          } else requestAnimationFrame(tick);
        };
        requestAnimationFrame(tick);
      });
    }
    const rafProbe = document.createElement('div');
    rafProbe.style.cssText = 'position:fixed;left:100px;top:100px;width:4px;height:4px;background:#000;opacity:0.2;z-index:2147483647';
    document.body.appendChild(rafProbe);
    window.__chromiumAnimationCheck = {
      rafProbe, rafBefore: Number(getComputedStyle(rafProbe).opacity), waitFrames
    };
  })();`);
  const rafBeforePixels = await win.webContents.capturePage({ x: 100, y: 100, width: 4, height: 4 });
  await win.webContents.executeJavaScript(`(async function(){
    const state = window.__chromiumAnimationCheck;
    await state.waitFrames(1, 'raf-before-update');
    state.rafProbe.style.opacity = '0.8';
    await state.waitFrames(1, 'raf-after-update');
  })();`);
  const rafAfterPixels = await win.webContents.capturePage({ x: 100, y: 100, width: 4, height: 4 });

  await win.webContents.executeJavaScript(`(async function(){
    const state = window.__chromiumAnimationCheck;

    const style = document.createElement('style');
    style.textContent = '@keyframes chromium-event-check-fade { from { opacity: 0.15; } to { opacity: 0.85; } }';
    document.head.appendChild(style);
    const cssProbe = document.createElement('div');
    cssProbe.style.cssText = 'position:fixed;left:106px;top:100px;width:4px;height:4px;background:#000;animation:chromium-event-check-fade 1000ms linear forwards;z-index:2147483647';
    document.body.appendChild(cssProbe);
    const cssAnimation = cssProbe.getAnimations()[0];
    await Promise.race([
      cssAnimation.ready,
      new Promise((_, reject) => setTimeout(() => reject(new Error('css-animation-ready-timeout')), 1000))
    ]);
    await state.waitFrames(1, 'css-before-capture');
    state.cssProbe = cssProbe;
    state.cssStyle = style;
    state.cssBefore = Number(getComputedStyle(cssProbe).opacity);
  })();`);
  const cssBeforePixels = await win.webContents.capturePage({ x: 106, y: 100, width: 4, height: 4 });
  await win.webContents.executeJavaScript(`window.__chromiumAnimationCheck.waitFrames(8, 'css-after-capture')`);
  const cssAfterPixels = await win.webContents.capturePage({ x: 106, y: 100, width: 4, height: 4 });
  const animation = await win.webContents.executeJavaScript(`(function(){
    const state = window.__chromiumAnimationCheck;
    const rafBefore = state.rafBefore;
    const rafAfter = Number(getComputedStyle(state.rafProbe).opacity);
    const cssBefore = Number(getComputedStyle(state.cssProbe).opacity);
    const cssAnimation = state.cssProbe.getAnimations()[0];
    const cssCurrentTimeMs = cssAnimation && Number(cssAnimation.currentTime);
    const cssAfter = cssBefore;
    state.rafProbe.remove();
    state.cssProbe.remove();
    state.cssStyle.remove();
    delete window.__chromiumAnimationCheck;
    return { raf_before_opacity: rafBefore, raf_after_opacity: rafAfter,
      css_before_opacity: state.cssBefore, css_after_opacity: cssAfter,
      css_current_time_ms: cssCurrentTimeMs };
  })();`);
  animation.raf_pixel_changed = pixelsDiffer(rafBeforePixels, rafAfterPixels);
  animation.css_pixel_changed = pixelsDiffer(cssBeforePixels, cssAfterPixels);
  animation.raf_property_advanced = animation.raf_after_opacity > animation.raf_before_opacity && animation.raf_pixel_changed;
  animation.css_property_advanced = animation.css_after_opacity > animation.css_before_opacity &&
    animation.css_pixel_changed && animation.css_current_time_ms > 0;

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
      out.submit_canceled === true &&
      ${JSON.stringify(animation.raf_property_advanced)} === true &&
      ${JSON.stringify(animation.css_property_advanced)} === true;
    Object.assign(out, ${JSON.stringify(animation)});
    return out;
  })();`);
  await new Promise(resolve => {
    process.stdout.write('EVENT_CHECK ' + JSON.stringify(result) + '\n', resolve);
  });
  win.destroy();
  app.exit(result.pass ? 0 : 1);
}).catch(error => {
  process.stdout.write('EVENT_CHECK ' + JSON.stringify({ pass: false, error: String(error) }) + '\n', () => {
    app.exit(1);
  });
});
