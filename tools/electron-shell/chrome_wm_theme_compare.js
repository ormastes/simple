#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const { spawnSync } = require('child_process');
const { loadThemePackage } = require('./theme_package');

const projectRoot = path.resolve(__dirname, '..', '..');
const outArg = process.argv.indexOf('--out');
const outDir = path.resolve(projectRoot, outArg >= 0 ? process.argv[outArg + 1] : 'build/wm_theme_compare');
const width = 800;
const height = 520;

function skip(reason) {
    console.log(`SKIP: ${reason}`);
    process.exit(0);
}

function commandExists(command) {
    const pathValue = process.env.PATH || '';
    for (const dir of pathValue.split(path.delimiter).filter(Boolean)) {
        const candidate = path.join(dir, command);
        if (fs.existsSync(candidate)) return candidate;
    }
    return '';
}

function chromeExecutable() {
    if (process.env.CHROME_BIN && fs.existsSync(process.env.CHROME_BIN)) return process.env.CHROME_BIN;
    const candidates = process.platform === 'darwin'
        ? ['/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', '/Applications/Chromium.app/Contents/MacOS/Chromium']
        : ['google-chrome', 'chromium', 'chromium-browser'];
    for (const candidate of candidates) {
        if (candidate.includes(path.sep) && fs.existsSync(candidate)) return candidate;
        const found = commandExists(candidate);
        if (found) return found;
    }
    return '';
}

function run(cmd, args, opts = {}) {
    const result = spawnSync(cmd, args, {
        cwd: projectRoot,
        encoding: 'utf8',
        stdio: opts.stdio || 'pipe',
        env: { ...process.env, ...(opts.env || {}) }
    });
    if (result.error) throw result.error;
    if (result.status !== 0) {
        throw new Error(`${cmd} ${args.join(' ')} failed\n${result.stdout || ''}${result.stderr || ''}`);
    }
    return result;
}

function writeFixtureHtml(filePath) {
    const theme = loadThemePackage(process.env.SIMPLE_THEME || '');
    const structuralCss = `
* { margin: 0; padding: 0; box-sizing: border-box; }
body {
  width: ${width}px;
  height: ${height}px;
  overflow: hidden;
  background: var(--app-background-image, var(--app-bg, #131315));
  color: var(--ui-fg, #e4e2e4);
  font-family: var(--font-main, sans-serif);
}
html {
  width: ${width}px;
  height: ${height}px;
  background: var(--app-background-image, var(--app-bg, #131315));
}
#wm-desktop { position: absolute; inset: 0; }
#fixture-backdrop {
  position: absolute;
  left: 0;
  top: 0;
  width: ${width}px;
  height: ${height}px;
  background: var(--app-background-image, var(--app-bg, #131315));
}
.wm-window {
  position: absolute;
  left: 96px;
  top: 70px;
  width: 608px;
  height: 356px;
  display: flex;
  flex-direction: column;
  overflow: hidden;
  background: var(--app-surface, rgba(31,31,33,0.80));
  border: 1px solid var(--app-border, rgba(139,144,160,0.20));
  border-radius: var(--radius-md, 12px);
  box-shadow: var(--app-shadow, 0 20px 50px rgba(0,0,0,0.40));
}
.wm-titlebar {
  height: 38px;
  flex: 0 0 auto;
  background: var(--glass-surface, rgba(19,19,21,0.75));
  border-bottom: 1px solid var(--app-border, rgba(139,144,160,0.20));
}
.wm-body { flex: 1; padding: 24px; background: color-mix(in srgb, var(--app-surface, rgba(31,31,33,0.80)) 78%, transparent); }
.fixture-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 18px; height: 100%; }
.fixture-solid { min-height: 92px; }
`;
    const runtimeCss = `
.runtime-marker { outline: 2px solid color-mix(in srgb, var(--ui-accent) 60%, transparent); }
`;
    const html = `<!doctype html>
<html data-theme="${theme.id}" data-requested-theme="${theme.requestedId}">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=${width}, initial-scale=1">
<style id="structural">${structuralCss}</style>
<style id="simple-ui-host-theme">${theme.css}</style>
<style id="simple-ui-runtime-style">${runtimeCss}</style>
</head>
<body>
<div id="fixture-backdrop"></div>
<div id="wm-desktop">
  <section class="wm-window focused runtime-marker">
    <div class="wm-titlebar"></div>
    <div class="wm-body">
      <div class="fixture-grid">
        <div class="widget-panel fixture-solid"></div>
        <div class="widget-button fixture-solid" aria-label="button"></div>
        <div class="widget-input fixture-solid" aria-label="input"></div>
        <div class="widget-statusbar fixture-solid"></div>
      </div>
    </div>
  </section>
</div>
</body>
</html>`;
    fs.writeFileSync(filePath, html, 'utf8');
}

function captureChromePpm(htmlPath, pngPath, ppmPath) {
    let playwright = null;
    try {
        playwright = require('playwright');
    } catch {
        playwright = null;
    }
    if (playwright) {
        const script = `
const { chromium } = require('playwright');
(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage({ viewport: { width: ${width}, height: ${height}, deviceScaleFactor: 1 } });
  await page.goto(${JSON.stringify(`file://${htmlPath}`)});
  await page.screenshot({ path: ${JSON.stringify(pngPath)} });
  await browser.close();
})().catch((err) => { console.error(err.stack || err.message || err); process.exit(1); });
`;
        run(process.execPath, ['-e', script]);
    } else {
        const chrome = chromeExecutable();
        if (!chrome) skip('Playwright is not installed and Chrome/Chromium was not found');
        run(chrome, [
            '--headless=new',
            '--disable-gpu',
            '--hide-scrollbars',
            '--force-device-scale-factor=1',
            `--window-size=${width},${height + 160}`,
            `--screenshot=${pngPath}`,
            `file://${htmlPath}`
        ]);
    }
    const png = decodePng(fs.readFileSync(pngPath));
    writePpm(ppmPath, width, height, cropRgb(png, width, height));
}

function captureElectronPpm(htmlPath, ppmPath) {
    let electronPath = '';
    try {
        electronPath = require('electron');
    } catch {
        skip('Electron package is not installed; run npm --prefix tools/electron-shell ci first');
    }
    const args = process.platform === 'linux'
        ? ['--no-sandbox', path.join(__dirname, 'screenshot.js'), htmlPath, ppmPath, String(width), String(height)]
        : [path.join(__dirname, 'screenshot.js'), htmlPath, ppmPath, String(width), String(height)];
    run(electronPath, args, {
        env: {
            ELECTRON_DISABLE_SANDBOX: process.platform === 'linux' ? '1' : (process.env.ELECTRON_DISABLE_SANDBOX || '')
        }
    });
}

function readToken(buffer, offset) {
    while (offset < buffer.length) {
        const ch = buffer[offset];
        if (ch === 35) {
            while (offset < buffer.length && buffer[offset] !== 10) offset += 1;
        } else if (ch <= 32) {
            offset += 1;
        } else {
            break;
        }
    }
    const start = offset;
    while (offset < buffer.length && buffer[offset] > 32) offset += 1;
    return { token: buffer.slice(start, offset).toString('ascii'), offset };
}

function paethPredictor(a, b, c) {
    const p = a + b - c;
    const pa = Math.abs(p - a);
    const pb = Math.abs(p - b);
    const pc = Math.abs(p - c);
    if (pa <= pb && pa <= pc) return a;
    if (pb <= pc) return b;
    return c;
}

function decodePng(buffer) {
    const signature = '89504e470d0a1a0a';
    if (buffer.slice(0, 8).toString('hex') !== signature) {
        throw new Error('Chrome screenshot is not a PNG');
    }
    let offset = 8;
    let widthValue = 0;
    let heightValue = 0;
    let colorType = 0;
    let bitDepth = 0;
    const idat = [];
    while (offset < buffer.length) {
        const length = buffer.readUInt32BE(offset); offset += 4;
        const type = buffer.slice(offset, offset + 4).toString('ascii'); offset += 4;
        const data = buffer.slice(offset, offset + length); offset += length;
        offset += 4;
        if (type === 'IHDR') {
            widthValue = data.readUInt32BE(0);
            heightValue = data.readUInt32BE(4);
            bitDepth = data[8];
            colorType = data[9];
            if (data[12] !== 0) throw new Error('interlaced PNG screenshots are not supported');
        } else if (type === 'IDAT') {
            idat.push(data);
        } else if (type === 'IEND') {
            break;
        }
    }
    if (bitDepth !== 8 || (colorType !== 2 && colorType !== 6)) {
        throw new Error(`unsupported PNG format bitDepth=${bitDepth} colorType=${colorType}`);
    }
    const channels = colorType === 6 ? 4 : 3;
    const stride = widthValue * channels;
    const inflated = zlib.inflateSync(Buffer.concat(idat));
    const raw = Buffer.alloc(stride * heightValue);
    let src = 0;
    for (let y = 0; y < heightValue; y++) {
        const filter = inflated[src++];
        const rowOffset = y * stride;
        const prevOffset = rowOffset - stride;
        for (let x = 0; x < stride; x++) {
            const left = x >= channels ? raw[rowOffset + x - channels] : 0;
            const up = y > 0 ? raw[prevOffset + x] : 0;
            const upLeft = y > 0 && x >= channels ? raw[prevOffset + x - channels] : 0;
            const value = inflated[src++];
            if (filter === 0) raw[rowOffset + x] = value;
            else if (filter === 1) raw[rowOffset + x] = (value + left) & 255;
            else if (filter === 2) raw[rowOffset + x] = (value + up) & 255;
            else if (filter === 3) raw[rowOffset + x] = (value + Math.floor((left + up) / 2)) & 255;
            else if (filter === 4) raw[rowOffset + x] = (value + paethPredictor(left, up, upLeft)) & 255;
            else throw new Error(`unsupported PNG filter ${filter}`);
        }
    }
    const rgb = Buffer.alloc(widthValue * heightValue * 3);
    for (let i = 0, j = 0; i < raw.length; i += channels, j += 3) {
        rgb[j] = raw[i];
        rgb[j + 1] = raw[i + 1];
        rgb[j + 2] = raw[i + 2];
    }
    return { width: widthValue, height: heightValue, rgb };
}

function cropRgb(image, targetWidth, targetHeight) {
    if (image.width < targetWidth || image.height < targetHeight) {
        throw new Error(`Chrome screenshot too small: ${image.width}x${image.height}`);
    }
    if (image.width === targetWidth && image.height === targetHeight) return image.rgb;
    const out = Buffer.alloc(targetWidth * targetHeight * 3);
    for (let y = 0; y < targetHeight; y++) {
        image.rgb.copy(out, y * targetWidth * 3, y * image.width * 3, y * image.width * 3 + targetWidth * 3);
    }
    return out;
}

function decodePpm(filePath) {
    const buffer = fs.readFileSync(filePath);
    let offset = 0;
    const magic = readToken(buffer, offset); offset = magic.offset;
    const w = readToken(buffer, offset); offset = w.offset;
    const h = readToken(buffer, offset); offset = h.offset;
    const max = readToken(buffer, offset); offset = max.offset;
    if (buffer[offset] === 13 && buffer[offset + 1] === 10) {
        offset += 2;
    } else if (buffer[offset] <= 32) {
        offset += 1;
    }
    const widthValue = Number(w.token);
    const heightValue = Number(h.token);
    if (magic.token === 'P6') {
        return { width: widthValue, height: heightValue, data: buffer.slice(offset, offset + widthValue * heightValue * 3) };
    }
    if (magic.token === 'P3') {
        const values = buffer.slice(offset).toString('ascii').trim().split(/\s+/).map(Number);
        const data = Buffer.alloc(widthValue * heightValue * 3);
        for (let i = 0; i < data.length; i++) data[i] = Math.round(values[i] * 255 / Number(max.token || 255));
        return { width: widthValue, height: heightValue, data };
    }
    throw new Error(`unsupported PPM format ${magic.token}`);
}

function writePpm(filePath, widthValue, heightValue, data) {
    fs.writeFileSync(filePath, Buffer.concat([
        Buffer.from(`P6\n${widthValue} ${heightValue}\n255\n`, 'ascii'),
        data
    ]));
}

function writeSummary(filePath, summary) {
    fs.writeFileSync(filePath, JSON.stringify(summary, null, 2) + '\n', 'utf8');
}

function comparePpm(referencePath, actualPath, heatmapPath) {
    const a = decodePpm(referencePath);
    const b = decodePpm(actualPath);
    if (a.width !== b.width || a.height !== b.height) {
        throw new Error(`dimension mismatch chrome=${a.width}x${a.height} electron=${b.width}x${b.height}`);
    }
    const heat = Buffer.alloc(a.data.length);
    let diffPixels = 0;
    let maxChannelDiff = 0;
    for (let i = 0; i < a.data.length; i += 3) {
        const dr = Math.abs(a.data[i] - b.data[i]);
        const dg = Math.abs(a.data[i + 1] - b.data[i + 1]);
        const db = Math.abs(a.data[i + 2] - b.data[i + 2]);
        const max = Math.max(dr, dg, db);
        maxChannelDiff = Math.max(maxChannelDiff, max);
        if (max > 18) {
            diffPixels += 1;
            heat[i] = 255; heat[i + 1] = 32; heat[i + 2] = 32;
        } else {
            heat[i] = 0; heat[i + 1] = 160; heat[i + 2] = 80;
        }
    }
    writePpm(heatmapPath, a.width, a.height, heat);
    const total = a.width * a.height;
    return { diffPixels, total, maxChannelDiff, diffRatio: diffPixels / total };
}

function main() {
    fs.mkdirSync(outDir, { recursive: true });
    const htmlPath = path.join(outDir, 'fixture.html');
    const chromePngPath = path.join(outDir, 'chrome_reference.png');
    const chromePpmPath = path.join(outDir, 'chrome_reference.ppm');
    const electronPpmPath = path.join(outDir, 'electron_wm.ppm');
    const heatmapPath = path.join(outDir, 'diff_heatmap.ppm');
    const summaryPath = path.join(outDir, 'summary.json');
    writeFixtureHtml(htmlPath);
    captureChromePpm(htmlPath, chromePngPath, chromePpmPath);
    captureElectronPpm(htmlPath, electronPpmPath);
    const result = comparePpm(chromePpmPath, electronPpmPath, heatmapPath);
    const summary = {
        requestedTheme: process.env.SIMPLE_THEME || '',
        width,
        height,
        diffPixels: result.diffPixels,
        totalPixels: result.total,
        diffRatio: result.diffRatio,
        maxChannelDiff: result.maxChannelDiff,
        chromeReferencePpm: path.relative(projectRoot, chromePpmPath),
        electronPpm: path.relative(projectRoot, electronPpmPath),
        heatmapPpm: path.relative(projectRoot, heatmapPath)
    };
    writeSummary(summaryPath, summary);
    console.log(`Chrome/Electron WM theme compare: diff_pixels=${result.diffPixels}/${result.total} max_channel_diff=${result.maxChannelDiff}`);
    console.log(`Artifacts: ${path.relative(projectRoot, chromePpmPath)}, ${path.relative(projectRoot, electronPpmPath)}, ${path.relative(projectRoot, heatmapPath)}, ${path.relative(projectRoot, summaryPath)}`);
    if (result.diffRatio > 0.03) {
        throw new Error(`theme visual diff exceeded tolerance: ${(result.diffRatio * 100).toFixed(2)}%`);
    }
}

try {
    main();
} catch (err) {
    console.error(`Chrome/Electron WM theme compare failed: ${err.stack || err.message || err}`);
    process.exit(1);
}
