// Chromium render helper for the Simple web-render "chromium" backend.
//
// Renders an HTML file offscreen in real Chromium (Electron) at an exact size
// and writes the raw BGRA framebuffer (NativeImage.toBitmap(), row-major) to
// CRB_OUT. Offscreen + srgb avoids the display-compositor ICC shift, so the
// pixels match what the pure-Simple Engine2D path is compared against.
//
// Env: CRB_HTML (input .html), CRB_OUT (output .bgra), CRB_W, CRB_H.
const { app, BrowserWindow } = require('electron');
const fs = require('fs');

app.commandLine.appendSwitch('force-color-profile', 'srgb');
app.disableHardwareAcceleration();

const htmlPath = process.env.CRB_HTML;
const outPath = process.env.CRB_OUT;
const width = Number(process.env.CRB_W || 480);
const height = Number(process.env.CRB_H || 320);

app.whenReady().then(async () => {
  const win = new BrowserWindow({
    width, height, show: false,
    webPreferences: { offscreen: true, sandbox: false },
    backgroundColor: '#ffffff',
  });
  win.webContents.setFrameRate(30);
  await win.loadFile(htmlPath);
  await new Promise(r => setTimeout(r, 500)); // let layout/paint settle
  const img = await win.webContents.capturePage();
  const bmp = img.toBitmap();            // BGRA, row-major
  const sz = img.getSize();
  fs.writeFileSync(outPath, bmp);
  fs.writeFileSync(outPath + '.meta', sz.width + ' ' + sz.height + ' ' + bmp.length);
  console.log('CRB_OK ' + sz.width + 'x' + sz.height + ' bytes=' + bmp.length);
  win.destroy();
  app.exit(0);
});
