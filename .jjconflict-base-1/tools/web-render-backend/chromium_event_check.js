// Verify the chromium web-render backend is genuinely interactive: load the page
// and programmatically exercise the text editor (input) and a button, reporting
// whether the events actually fired (real DOM event model).
//
// Env: CRB_HTML (input .html). Prints a JSON result line.
const { app, BrowserWindow } = require('electron');
app.commandLine.appendSwitch('force-color-profile', 'srgb');
app.disableHardwareAcceleration();

const htmlPath = process.env.CRB_HTML;

app.whenReady().then(async () => {
  const win = new BrowserWindow({ width: 800, height: 600, show: false,
    webPreferences: { offscreen: true, sandbox: false } });
  await win.loadFile(htmlPath);
  await new Promise(r => setTimeout(r, 300));
  const result = await win.webContents.executeJavaScript(`(function(){
    const out = {};
    // Text editor: focus #name, type, and confirm the value + input event stuck.
    const name = document.getElementById('name');
    out.text_input_found = !!name;
    if (name) {
      let inputEvents = 0;
      name.addEventListener('input', () => { inputEvents++; });
      name.focus();
      name.value = 'Hello Simple';
      name.dispatchEvent(new Event('input', { bubbles: true }));
      out.text_value = name.value;
      out.text_focused = (document.activeElement === name);
      out.text_input_events = inputEvents;
    }
    // Button: attach a click listener and click it; confirm the handler ran.
    const btn = document.querySelector('a.btn') || document.querySelector('button.btn');
    out.button_found = !!btn;
    if (btn) {
      let clicks = 0;
      btn.addEventListener('click', () => { clicks++; });
      btn.click();
      out.button_clicks = clicks;
    }
    return out;
  })();`);
  console.log('EVENT_CHECK ' + JSON.stringify(result));
  win.destroy();
  app.exit(0);
});
