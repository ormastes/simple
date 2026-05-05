#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const baselineDir = path.join(root, 'test', 'baselines', 'famous_site_corpus');

function usage() {
  console.error('Usage: node tools/electron-shell/summarize_famous_site_text_compositing.js [--limit=N]');
  process.exit(2);
}

function argValue(name, fallback) {
  const prefix = `${name}=`;
  const arg = process.argv.slice(2).find(item => item.startsWith(prefix));
  return arg ? arg.slice(prefix.length) : fallback;
}

function isWs(byte) {
  return byte === 9 || byte === 10 || byte === 13 || byte === 32;
}

function readPpm(filePath) {
  const bytes = fs.readFileSync(filePath);
  let pos = 0;
  function token() {
    while (pos < bytes.length && isWs(bytes[pos])) pos += 1;
    if (bytes[pos] === 35) {
      while (pos < bytes.length && bytes[pos] !== 10) pos += 1;
      return token();
    }
    let out = '';
    while (pos < bytes.length && !isWs(bytes[pos])) {
      out += String.fromCharCode(bytes[pos]);
      pos += 1;
    }
    return out;
  }

  const magic = token();
  const width = Number(token());
  const height = Number(token());
  const max = Number(token());
  if ((magic !== 'P6' && magic !== 'P3') || !width || !height || max !== 255) {
    throw new Error(`Unsupported PPM header in ${filePath}`);
  }
  const data = Buffer.alloc(width * height * 3);
  if (magic === 'P6') {
    if (pos < bytes.length && isWs(bytes[pos])) pos += 1;
    bytes.copy(data, 0, pos, pos + data.length);
  } else {
    for (let i = 0; i < data.length; i += 1) data[i] = Number(token());
  }
  return { width, height, data };
}

function regionFromDomRect(rect) {
  return {
    x: Math.floor(rect.x),
    y: Math.floor(rect.y),
    width: Math.ceil(rect.width),
    height: Math.ceil(rect.height),
  };
}

function pixelKey(img, x, y) {
  const p = (y * img.width + x) * 3;
  return `${img.data[p]},${img.data[p + 1]},${img.data[p + 2]}`;
}

function dominantColor(img, region) {
  const counts = new Map();
  let bestKey = '255,255,255';
  let bestCount = -1;
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const key = pixelKey(img, x, y);
      const next = (counts.get(key) || 0) + 1;
      counts.set(key, next);
      if (next > bestCount) {
        bestCount = next;
        bestKey = key;
      }
    }
  }
  return bestKey;
}

function clipLineToDiv(line, div) {
  const divBottom = div.y + div.height;
  const bottom = Math.min(line.y + line.height, divBottom);
  return {
    x: line.x,
    y: line.y,
    width: line.width,
    height: Math.max(0, bottom - line.y),
  };
}

function countRegion(expected, actual, region, expectedBg, actualBg) {
  let expectedInk = 0;
  let actualInk = 0;
  let differentPixels = 0;
  let sad = 0;
  let expectedChromaticInk = 0;
  let actualGrayInk = 0;
  const channelSignedDiff = { r: 0, g: 0, b: 0 };
  const channelAbsoluteDiff = { r: 0, g: 0, b: 0 };
  const endY = Math.min(expected.height, region.y + region.height);
  const endX = Math.min(expected.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * expected.width + x) * 3;
      const er = expected.data[p];
      const eg = expected.data[p + 1];
      const eb = expected.data[p + 2];
      const ar = actual.data[p];
      const ag = actual.data[p + 1];
      const ab = actual.data[p + 2];
      const expectedKey = `${er},${eg},${eb}`;
      const actualKey = `${ar},${ag},${ab}`;
      if (expectedKey !== expectedBg) {
        expectedInk += 1;
        if (er !== eg || eg !== eb) expectedChromaticInk += 1;
      }
      if (actualKey !== actualBg) {
        actualInk += 1;
        if (ar === ag && ag === ab && ar < 255) actualGrayInk += 1;
      }
      const dr = Math.abs(er - ar);
      const dg = Math.abs(eg - ag);
      const db = Math.abs(eb - ab);
      channelSignedDiff.r += er - ar;
      channelSignedDiff.g += eg - ag;
      channelSignedDiff.b += eb - ab;
      channelAbsoluteDiff.r += dr;
      channelAbsoluteDiff.g += dg;
      channelAbsoluteDiff.b += db;
      if (dr + dg + db > 0) differentPixels += 1;
      sad += dr + dg + db;
    }
  }
  return {
    expectedInk,
    actualInk,
    missingInk: Math.max(0, expectedInk - actualInk),
    actualPct10000: expectedInk > 0 ? Math.floor((actualInk * 10000) / expectedInk) : 10000,
    differentPixels,
    sad,
    expectedChromaticInk,
    actualGrayInk,
    channelSignedDiff,
    channelAbsoluteDiff,
  };
}

function reportName(reportPath) {
  if (!fs.existsSync(reportPath)) return '';
  const text = fs.readFileSync(reportPath, 'utf8');
  const match = text.match(/name:\s+"([^"]+)"/);
  return match ? match[1] : '';
}

function summarizeSample(id) {
  const dir = path.join(baselineDir, id);
  const chromePath = path.join(dir, 'chrome.ppm');
  const simplePath = path.join(dir, 'simple.ppm');
  const metricsPath = path.join(dir, 'chrome_metrics.json');
  if (!fs.existsSync(chromePath) || !fs.existsSync(simplePath) || !fs.existsSync(metricsPath)) return null;

  const expected = readPpm(chromePath);
  const actual = readPpm(simplePath);
  const metricsDoc = JSON.parse(fs.readFileSync(metricsPath, 'utf8'));
  const metrics = metricsDoc.metrics || {};
  if (!metrics.div || !metrics.div.rect || !Array.isArray(metrics.textClientRects)) return null;

  const div = regionFromDomRect(metrics.div.rect);
  const expectedBg = dominantColor(expected, div);
  const actualBg = dominantColor(actual, div);
  const total = {
    expectedInk: 0,
    actualInk: 0,
    missingInk: 0,
    differentPixels: 0,
    sad: 0,
    expectedChromaticInk: 0,
    actualGrayInk: 0,
    channelSignedDiff: { r: 0, g: 0, b: 0 },
    channelAbsoluteDiff: { r: 0, g: 0, b: 0 },
  };

  for (const rect of metrics.textClientRects) {
    const line = clipLineToDiv(regionFromDomRect(rect), div);
    if (line.height <= 0 || line.width <= 0) continue;
    const current = countRegion(expected, actual, line, expectedBg, actualBg);
    total.expectedInk += current.expectedInk;
    total.actualInk += current.actualInk;
    total.missingInk += current.missingInk;
    total.differentPixels += current.differentPixels;
    total.sad += current.sad;
    total.expectedChromaticInk += current.expectedChromaticInk;
    total.actualGrayInk += current.actualGrayInk;
    total.channelSignedDiff.r += current.channelSignedDiff.r;
    total.channelSignedDiff.g += current.channelSignedDiff.g;
    total.channelSignedDiff.b += current.channelSignedDiff.b;
    total.channelAbsoluteDiff.r += current.channelAbsoluteDiff.r;
    total.channelAbsoluteDiff.g += current.channelAbsoluteDiff.g;
    total.channelAbsoluteDiff.b += current.channelAbsoluteDiff.b;
  }

  return {
    sample: id,
    name: reportName(path.join(dir, 'report.sdn')),
    expectedBackground: expectedBg,
    actualBackground: actualBg,
    expectedInk: total.expectedInk,
    actualInk: total.actualInk,
    missingInk: total.missingInk,
    actualPct10000: total.expectedInk > 0 ? Math.floor((total.actualInk * 10000) / total.expectedInk) : 10000,
    differentPixels: total.differentPixels,
    sad: total.sad,
    expectedChromaticInk: total.expectedChromaticInk,
    actualGrayInk: total.actualGrayInk,
    channelSignedDiff: total.channelSignedDiff,
    channelAbsoluteDiff: total.channelAbsoluteDiff,
  };
}

for (const arg of process.argv.slice(2)) {
  if (arg === '-h' || arg === '--help') usage();
  if (!arg.startsWith('--limit=')) usage();
}

const limit = Number(argValue('--limit', '10'));
const reports = fs.existsSync(baselineDir)
  ? fs.readdirSync(baselineDir).map(summarizeSample).filter(Boolean)
  : [];

const worstByInk = [...reports].sort((a, b) =>
  a.actualPct10000 - b.actualPct10000 ||
  b.missingInk - a.missingInk ||
  a.sample.localeCompare(b.sample)
).slice(0, limit);

const worstByDiff = [...reports].sort((a, b) =>
  b.differentPixels - a.differentPixels ||
  b.sad - a.sad ||
  a.sample.localeCompare(b.sample)
).slice(0, limit);

console.log(JSON.stringify({
  reportCount: reports.length,
  worstByInk,
  worstByDiff,
}, null, 2));
