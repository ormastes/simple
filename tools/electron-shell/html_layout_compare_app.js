// Electron runner for Chrome (Blink/Skia) vs Pure-Simple Web HTML Layout Comparison.
//
// Modes:
//   1. Offscreen Chrome batch capture:
//      electron tools/electron-shell/html_layout_compare_app.js --capture-chrome <out_dir> [--pages <pages_dir>]
//   2. Interactive 1440x920 Compare Studio UI:
//      electron tools/electron-shell/html_layout_compare_app.js [--dir <bundle_dir>]

const fs = require("fs");
const path = require("path");
const { app, BrowserWindow } = require("electron");

function argValue(flag, fallback) {
  const idx = process.argv.indexOf(flag);
  if (idx >= 0 && idx + 1 < process.argv.length) {
    return process.argv[idx + 1];
  }
  return fallback;
}

const CAPTURE_DIR = argValue("--capture-chrome", "");
const PAGES_DIR = argValue(
  "--pages",
  path.resolve(__dirname, "../../examples/browser/html_layout_compare/pages")
);
const BUNDLE_DIR = path.resolve(
  argValue("--dir", path.resolve(__dirname, "../../build/html_layout_compare"))
);

if (CAPTURE_DIR && app.dock) {
  app.dock.hide();
}

async function runChromeBatchCapture() {
  const outDir = path.resolve(CAPTURE_DIR, "chrome");
  fs.mkdirSync(outDir, { recursive: true });
  const win = new BrowserWindow({
    width: 520,
    height: 340,
    useContentSize: true,
    show: false,
    frame: false,
    backgroundColor: "#0f172a",
    webPreferences: {
      nodeIntegration: false,
      contextIsolation: true,
    },
  });

  const pages = fs
    .readdirSync(PAGES_DIR)
    .filter((f) => /^v\d+\.html$/i.test(f))
    .sort();
  for (const file of pages) {
    const htmlPath = path.join(PAGES_DIR, file);
    const outPath = path.join(outDir, file.replace(/\.html$/, ".png"));
    const t0 = Date.now();
    await win.loadFile(htmlPath);
    await win.webContents.executeJavaScript(`
      Promise.all(Array.from(document.images).map(img =>
        img.complete ? Promise.resolve() : new Promise(r => { img.onload = r; img.onerror = r; })
      ))
    `);
    await new Promise((r) => setTimeout(r, 90));
    const img = await win.webContents.capturePage();
    const sz = img.getSize();
    fs.writeFileSync(outPath, img.toPNG());
    console.log(`[chrome-batch] ${file} -> ${sz.width}x${sz.height} (${Date.now() - t0}ms)`);
  }
  win.destroy();
  app.quit();
}

function launchCompareViewer() {
  const win = new BrowserWindow({
    width: 1440,
    height: 920,
    title: "Chrome (Blink/Skia) vs Pure-Simple Web — 14 HTML Layout, Text & Image Variations",
    titleBarStyle: "default",
    backgroundColor: "#0b1120",
    show: true,
    webPreferences: {
      contextIsolation: true,
      nodeIntegration: false,
      backgroundThrottling: false,
    },
  });
  win.loadFile(path.join(__dirname, "html_layout_compare_viewer.html"), {
    query: { bundle: BUNDLE_DIR },
  });
  win.webContents.once("did-finish-load", () => {
    console.log(`[html-compare-app] ready (bundle=${BUNDLE_DIR})`);
  });
}

app.whenReady().then(async () => {
  if (CAPTURE_DIR) {
    await runChromeBatchCapture();
  } else {
    launchCompareViewer();
  }
});

app.on("window-all-closed", () => {
  app.quit();
});
