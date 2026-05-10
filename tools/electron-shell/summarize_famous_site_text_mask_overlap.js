#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const baselineDir = path.join(root, 'test', 'baselines', 'famous_site_corpus');

function usage() {
  console.error('Usage: node tools/electron-shell/summarize_famous_site_text_mask_overlap.js [--samples=a,b] [--limit=N]');
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

function countOverlap(expected, actual, region, expectedBg, actualBg) {
  let expectedInk = 0;
  let actualInk = 0;
  let overlapInk = 0;
  let falsePositiveInk = 0;
  let missingInk = 0;
  const endY = Math.min(expected.height, region.y + region.height);
  const endX = Math.min(expected.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const expectedIsInk = pixelKey(expected, x, y) !== expectedBg;
      const actualIsInk = pixelKey(actual, x, y) !== actualBg;
      if (expectedIsInk) expectedInk += 1;
      if (actualIsInk) actualInk += 1;
      if (expectedIsInk && actualIsInk) overlapInk += 1;
      if (!expectedIsInk && actualIsInk) falsePositiveInk += 1;
      if (expectedIsInk && !actualIsInk) missingInk += 1;
    }
  }
  return { expectedInk, actualInk, overlapInk, falsePositiveInk, missingInk };
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
    overlapInk: 0,
    falsePositiveInk: 0,
    missingInk: 0,
  };

  for (const rect of metrics.textClientRects) {
    const line = clipLineToDiv(regionFromDomRect(rect), div);
    if (line.width <= 0 || line.height <= 0) continue;
    const current = countOverlap(expected, actual, line, expectedBg, actualBg);
    total.expectedInk += current.expectedInk;
    total.actualInk += current.actualInk;
    total.overlapInk += current.overlapInk;
    total.falsePositiveInk += current.falsePositiveInk;
    total.missingInk += current.missingInk;
  }

  return {
    sample: id,
    name: reportName(path.join(dir, 'report.sdn')),
    expectedBackground: expectedBg,
    actualBackground: actualBg,
    expectedInk: total.expectedInk,
    actualInk: total.actualInk,
    overlapInk: total.overlapInk,
    falsePositiveInk: total.falsePositiveInk,
    missingInk: total.missingInk,
    precisionPct10000: total.actualInk > 0 ? Math.floor((total.overlapInk * 10000) / total.actualInk) : 10000,
    recallPct10000: total.expectedInk > 0 ? Math.floor((total.overlapInk * 10000) / total.expectedInk) : 10000,
  };
}

for (const arg of process.argv.slice(2)) {
  if (arg === '-h' || arg === '--help') usage();
  if (!arg.startsWith('--limit=') && !arg.startsWith('--samples=')) usage();
}

const limit = Number(argValue('--limit', '10'));
const sampleArg = argValue('--samples', '');
const ids = sampleArg
  ? sampleArg.split(',').filter(Boolean)
  : fs.readdirSync(baselineDir).filter(id => fs.statSync(path.join(baselineDir, id)).isDirectory()).sort();
const reports = ids.map(summarizeSample).filter(Boolean);

const worstByRecall = [...reports].sort((a, b) =>
  a.recallPct10000 - b.recallPct10000 ||
  b.missingInk - a.missingInk ||
  a.sample.localeCompare(b.sample)
).slice(0, limit);

const worstByFalsePositive = [...reports].sort((a, b) =>
  b.falsePositiveInk - a.falsePositiveInk ||
  a.precisionPct10000 - b.precisionPct10000 ||
  a.sample.localeCompare(b.sample)
).slice(0, limit);

console.log(JSON.stringify({
  reportCount: reports.length,
  worstByRecall,
  worstByFalsePositive,
}, null, 2));
