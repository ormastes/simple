const { app, BrowserWindow } = require('electron');
const fs = require('fs');
const path = require('path');

const args = process.argv.slice(1);
const urlIndex = args.findIndex((arg) => /^https?:\/\//.test(arg));
const [url, proofPath, screenshotPath, timeoutText] = urlIndex >= 0 ? args.slice(urlIndex) : [];
const timeoutMs = Number(timeoutText || '15000');

if (!url || !proofPath || !screenshotPath) {
  console.error('usage: electron ios_mdi_probe_electron_self_test.js URL PROOF_JSON SCREENSHOT [TIMEOUT_MS]');
  console.error(`argv=${JSON.stringify(process.argv)}`);
  process.exit(2);
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function waitForProof() {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    if (fs.existsSync(proofPath) && fs.statSync(proofPath).size > 0) {
      return;
    }
    await sleep(100);
  }
  throw new Error(`proof not written within ${timeoutMs}ms: ${proofPath}`);
}

app.whenReady().then(async () => {
  const win = new BrowserWindow({
    width: 390,
    height: 844,
    show: true,
    webPreferences: {
      sandbox: true,
      contextIsolation: true,
      nodeIntegration: false,
    },
  });

  try {
    await win.loadURL(url);
    await waitForProof();
    const image = await win.webContents.capturePage();
    fs.mkdirSync(path.dirname(screenshotPath), { recursive: true });
    fs.writeFileSync(screenshotPath, image.toPNG());
    console.log(`ios_mdi_probe_browser_screenshot=${screenshotPath}`);
    app.exit(0);
  } catch (error) {
    console.error(error && error.stack ? error.stack : String(error));
    app.exit(1);
  }
});
