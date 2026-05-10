#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const baselineDir = path.join(root, 'test', 'baselines', 'famous_site_corpus');

function usage() {
  console.error('Usage: node tools/electron-shell/summarize_famous_site_corpus_coverage.js [--limit=N]');
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

function emptyBox() {
  return { pixels: 0 };
}

function nonWhiteBox(img, region) {
  const box = emptyBox();
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * img.width + x) * 3;
      if (img.data[p] !== 255 || img.data[p + 1] !== 255 || img.data[p + 2] !== 255) {
        box.pixels += 1;
      }
    }
  }
  return box;
}

function dominantColor(img, region) {
  const counts = new Map();
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  let bestKey = '255,255,255';
  let bestCount = -1;
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * img.width + x) * 3;
      const key = `${img.data[p]},${img.data[p + 1]},${img.data[p + 2]}`;
      const next = (counts.get(key) || 0) + 1;
      counts.set(key, next);
      if (next > bestCount) {
        bestCount = next;
        bestKey = key;
      }
    }
  }
  return { key: bestKey, pixels: Math.max(0, bestCount) };
}

function dominantInkBox(img, region) {
  const bg = dominantColor(img, region);
  const box = emptyBox();
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * img.width + x) * 3;
      const key = `${img.data[p]},${img.data[p + 1]},${img.data[p + 2]}`;
      if (key !== bg.key) box.pixels += 1;
    }
  }
  return box;
}

function coverageFromCounts(expectedPixels, actualPixels) {
  return {
    expectedPixels,
    actualPixels,
    missingPixels: Math.max(0, expectedPixels - actualPixels),
    actualPct10000: expectedPixels > 0 ? Math.floor((actualPixels * 10000) / expectedPixels) : 10000,
  };
}

function coverage(expected, actual, region) {
  return coverageFromCounts(nonWhiteBox(expected, region).pixels, nonWhiteBox(actual, region).pixels);
}

function inkCoverage(expected, actual, region) {
  return coverageFromCounts(dominantInkBox(expected, region).pixels, dominantInkBox(actual, region).pixels);
}

function regionFromDomRect(rect) {
  return {
    x: Math.floor(rect.x),
    y: Math.floor(rect.y),
    width: Math.ceil(rect.width),
    height: Math.ceil(rect.height),
  };
}

function famousSiteRegions(img, metricsDoc) {
  const metrics = metricsDoc && metricsDoc.metrics ? metricsDoc.metrics : null;
  if (!metrics || !metrics.div || !metrics.div.rect || !Array.isArray(metrics.textClientRects)) {
    return {
      divBox: { x: 8, y: 8, width: 120, height: 40 },
      overflowText: { x: 0, y: 48, width: img.width, height: 32 },
    };
  }
  const divBox = regionFromDomRect(metrics.div.rect);
  let maxBottom = divBox.y + divBox.height;
  for (const rect of metrics.textClientRects) {
    maxBottom = Math.max(maxBottom, Math.ceil(rect.bottom) + 1);
  }
  const overflowY = divBox.y + divBox.height;
  return {
    divBox,
    overflowText: { x: 0, y: overflowY, width: img.width, height: Math.max(0, maxBottom - overflowY) },
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
  const metrics = JSON.parse(fs.readFileSync(metricsPath, 'utf8'));
  const regions = famousSiteRegions(expected, metrics);
  return {
    sample: id,
    name: reportName(path.join(dir, 'report.sdn')),
    divBox: coverage(expected, actual, regions.divBox),
    divInk: inkCoverage(expected, actual, regions.divBox),
    overflowText: coverage(expected, actual, regions.overflowText),
    overflowInk: inkCoverage(expected, actual, regions.overflowText),
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

const worstOverflow = [...reports].sort((a, b) =>
  a.overflowText.actualPct10000 - b.overflowText.actualPct10000 ||
  b.overflowText.missingPixels - a.overflowText.missingPixels ||
  a.sample.localeCompare(b.sample)
).slice(0, limit);

const worstDiv = [...reports].sort((a, b) =>
  a.divBox.actualPct10000 - b.divBox.actualPct10000 ||
  b.divBox.missingPixels - a.divBox.missingPixels ||
  a.sample.localeCompare(b.sample)
).slice(0, limit);

const worstDivInk = [...reports].sort((a, b) =>
  a.divInk.actualPct10000 - b.divInk.actualPct10000 ||
  b.divInk.missingPixels - a.divInk.missingPixels ||
  a.sample.localeCompare(b.sample)
).slice(0, limit);

console.log(JSON.stringify({
  reportCount: reports.length,
  worstOverflow,
  worstDiv,
  worstDivInk,
}, null, 2));
