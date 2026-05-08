#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const baselineDir = path.join(root, 'test', 'baselines', 'famous_site_corpus');

function usage() {
  console.error('Usage: node tools/electron-shell/summarize_famous_site_text_color_histogram.js [--samples=a,b] [--limit=N] [--top=N]');
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
    while (pos < bytes.length && !isWs(bytes[pos])) out += String.fromCharCode(bytes[pos++]);
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
      const count = (counts.get(key) || 0) + 1;
      counts.set(key, count);
      if (count > bestCount) {
        bestCount = count;
        bestKey = key;
      }
    }
  }
  return bestKey;
}

function clipLineToDiv(line, div) {
  const bottom = Math.min(line.y + line.height, div.y + div.height);
  return {
    x: line.x,
    y: line.y,
    width: line.width,
    height: Math.max(0, bottom - line.y),
  };
}

function addColor(hist, key) {
  hist.set(key, (hist.get(key) || 0) + 1);
}

function topColors(hist, topN) {
  return [...hist.entries()]
    .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]))
    .slice(0, topN)
    .map(([rgb, count]) => ({ rgb, count }));
}

function summarizeSample(id, topN) {
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
  const expectedHist = new Map();
  const actualHist = new Map();
  let expectedInk = 0;
  let actualInk = 0;
  let differentPixels = 0;

  for (const rect of metrics.textClientRects) {
    const line = clipLineToDiv(regionFromDomRect(rect), div);
    const endY = Math.min(expected.height, line.y + line.height);
    const endX = Math.min(expected.width, line.x + line.width);
    for (let y = Math.max(0, line.y); y < endY; y += 1) {
      for (let x = Math.max(0, line.x); x < endX; x += 1) {
        const expectedKey = pixelKey(expected, x, y);
        const actualKey = pixelKey(actual, x, y);
        if (expectedKey !== expectedBg) {
          expectedInk += 1;
          addColor(expectedHist, expectedKey);
        }
        if (actualKey !== actualBg) {
          actualInk += 1;
          addColor(actualHist, actualKey);
        }
        if (expectedKey !== actualKey) differentPixels += 1;
      }
    }
  }

  return {
    sample: id,
    expectedBackground: expectedBg,
    actualBackground: actualBg,
    expectedInk,
    actualInk,
    differentPixels,
    expectedUniqueInkColors: expectedHist.size,
    actualUniqueInkColors: actualHist.size,
    expectedTopColors: topColors(expectedHist, topN),
    actualTopColors: topColors(actualHist, topN),
  };
}

for (const arg of process.argv.slice(2)) {
  if (arg === '-h' || arg === '--help') usage();
  if (!arg.startsWith('--limit=') && !arg.startsWith('--samples=') && !arg.startsWith('--top=')) usage();
}

const limit = Number(argValue('--limit', '10'));
const topN = Number(argValue('--top', '8'));
const sampleArg = argValue('--samples', 'site_0_google,site_15_twitch,site_44_the_new_york_times');
const ids = sampleArg === 'all'
  ? fs.readdirSync(baselineDir).filter(id => fs.statSync(path.join(baselineDir, id)).isDirectory()).sort()
  : sampleArg.split(',').filter(Boolean);
const reports = ids.map(id => summarizeSample(id, topN)).filter(Boolean);

console.log(JSON.stringify({
  reportCount: reports.length,
  reports: reports.slice(0, limit),
}, null, 2));
