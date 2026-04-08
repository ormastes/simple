// Electron Screenshot Tool — Headless page capture for pixel comparison
//
// Renders an HTML file in a hidden BrowserWindow and exports a PNG screenshot.
// Used by the Simple browser engine test suite for reference image generation.
//
// Usage:
//   npx electron screenshot.js <html_file> <output.png> [width] [height]
//   npx electron screenshot.js test.html output.png 800 600
//
// Dependencies: electron (already in node_modules)

const { app, BrowserWindow } = require('electron');
const fs = require('fs');
const path = require('path');

const args = process.argv.slice(2);

// Filter out Electron's internal flags (like --inspect, --no-sandbox, etc.)
const userArgs = args.filter(a => !a.startsWith('--') && !a.startsWith('-'));

const htmlInput = userArgs[0];
const outputPath = userArgs[1] || 'screenshot.png';
const width = parseInt(userArgs[2] || '800', 10);
const height = parseInt(userArgs[3] || '600', 10);

if (!htmlInput) {
    console.error('Usage: npx electron screenshot.js <html_file> <output.png> [width] [height]');
    process.exit(1);
}

// Disable GPU for headless operation
app.disableHardwareAcceleration();

app.whenReady().then(async () => {
    const win = new BrowserWindow({
        width: width,
        height: height,
        show: false,
        webPreferences: {
            nodeIntegration: false,
            contextIsolation: true,
            offscreen: true
        }
    });

    // Determine if input is a file path or inline HTML
    let loadUrl;
    if (fs.existsSync(htmlInput)) {
        loadUrl = 'file://' + path.resolve(htmlInput);
    } else {
        // Treat as inline HTML — write to temp file
        const tmpPath = path.join(require('os').tmpdir(), 'electron_screenshot_' + Date.now() + '.html');
        const wrapped = `<!DOCTYPE html>
<html>
<head><meta charset="utf-8"><style>*{margin:0;padding:0;box-sizing:border-box}</style></head>
<body style="margin:0;padding:0">${htmlInput}</body>
</html>`;
        fs.writeFileSync(tmpPath, wrapped, 'utf8');
        loadUrl = 'file://' + tmpPath;
    }

    try {
        await win.loadURL(loadUrl);

        // Wait a brief moment for rendering to complete
        await new Promise(resolve => setTimeout(resolve, 200));

        const image = await win.webContents.capturePage();
        const pngBuffer = image.toPNG();

        fs.writeFileSync(outputPath, pngBuffer);
        console.log(`Screenshot saved: ${outputPath} (${width}x${height})`);
    } catch (err) {
        console.error('Screenshot failed:', err.message);
        process.exit(1);
    } finally {
        win.destroy();
        app.quit();
    }
});

app.on('window-all-closed', () => {
    app.quit();
});
