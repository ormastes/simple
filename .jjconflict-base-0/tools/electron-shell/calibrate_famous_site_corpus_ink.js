#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const baselineDir = path.join(root, 'test', 'baselines', 'famous_site_corpus');

function usage() {
  console.error('Usage: node tools/electron-shell/calibrate_famous_site_corpus_ink.js [--samples=a,b] [--thresholds=224,208,192] [--alphas=64,96] [--limit=N]');
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
  return bestKey.split(',').map(Number);
}

function inkPixels(img, region) {
  const bg = dominantColor(img, region);
  let count = 0;
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * img.width + x) * 3;
      if (img.data[p] !== bg[0] || img.data[p + 1] !== bg[1] || img.data[p + 2] !== bg[2]) count += 1;
    }
  }
  return count;
}

function compare(expected, actual) {
  let differentPixels = 0;
  let sad = 0;
  for (let i = 0; i < expected.data.length; i += 3) {
    const dr = Math.abs(expected.data[i] - actual.data[i]);
    const dg = Math.abs(expected.data[i + 1] - actual.data[i + 1]);
    const db = Math.abs(expected.data[i + 2] - actual.data[i + 2]);
    if (dr + dg + db > 0) differentPixels += 1;
    sad += dr + dg + db;
  }
  return { differentPixels, sad };
}

function simulateCore(expected, simple, metrics, threshold, alpha) {
  const out = Buffer.from(simple.data);
  const div = regionFromDomRect(metrics.metrics.div.rect);
  const divBottom = div.y + div.height;
  const textRects = metrics.metrics.textClientRects || [];
  const bg = dominantColor(expected, div);
  for (const rect of textRects) {
    const line = regionFromDomRect(rect);
    const endY = Math.min(expected.height, line.y + Math.max(0, Math.min(line.height, divBottom - line.y)));
    const endX = Math.min(expected.width, line.x + line.width);
    for (let y = Math.max(0, line.y); y < endY; y += 1) {
      for (let x = Math.max(0, line.x); x < endX; x += 1) {
        const p = (y * expected.width + x) * 3;
        const er = expected.data[p];
        const eg = expected.data[p + 1];
        const eb = expected.data[p + 2];
        const bgDistance = Math.abs(er - bg[0]) + Math.abs(eg - bg[1]) + Math.abs(eb - bg[2]);
        if (bgDistance >= threshold) {
          out[p] = Math.floor((bg[0] * (255 - alpha)) / 255);
          out[p + 1] = Math.floor((bg[1] * (255 - alpha)) / 255);
          out[p + 2] = Math.floor((bg[2] * (255 - alpha)) / 255);
        }
      }
    }
  }
  return { width: simple.width, height: simple.height, data: out };
}

function sampleIds() {
  return fs.readdirSync(baselineDir).filter(id =>
    fs.existsSync(path.join(baselineDir, id, 'chrome.ppm')) &&
    fs.existsSync(path.join(baselineDir, id, 'simple.ppm')) &&
    fs.existsSync(path.join(baselineDir, id, 'chrome_metrics.json'))
  ).sort();
}

for (const arg of process.argv.slice(2)) {
  if (arg === '-h' || arg === '--help') usage();
  if (!arg.startsWith('--samples=') && !arg.startsWith('--thresholds=') && !arg.startsWith('--alphas=') && !arg.startsWith('--limit=')) usage();
}

const samplesArg = argValue('--samples', 'site_0_google,site_44_the_new_york_times,site_60_tripadvisor');
const selected = samplesArg === 'all' ? sampleIds() : samplesArg.split(',').filter(Boolean);
const thresholds = argValue('--thresholds', '224,208,192,160').split(',').filter(Boolean).map(Number);
const alphas = argValue('--alphas', '32,64,96,128').split(',').filter(Boolean).map(Number);
const limit = Number(argValue('--limit', '10'));

const cases = selected.map(id => {
  const dir = path.join(baselineDir, id);
  const expected = readPpm(path.join(dir, 'chrome.ppm'));
  const simple = readPpm(path.join(dir, 'simple.ppm'));
  const metrics = JSON.parse(fs.readFileSync(path.join(dir, 'chrome_metrics.json'), 'utf8'));
  const div = regionFromDomRect(metrics.metrics.div.rect);
  return { id, expected, simple, metrics, div, base: compare(expected, simple), expectedInk: inkPixels(expected, div), baseInk: inkPixels(simple, div) };
});

const results = [];
for (const threshold of thresholds) {
  for (const alpha of alphas) {
    let differentPixels = 0;
    let sad = 0;
    let expectedInk = 0;
    let actualInk = 0;
    for (const item of cases) {
      const simulated = simulateCore(item.expected, item.simple, item.metrics, threshold, alpha);
      const cmp = compare(item.expected, simulated);
      differentPixels += cmp.differentPixels;
      sad += cmp.sad;
      expectedInk += item.expectedInk;
      actualInk += inkPixels(simulated, item.div);
    }
    results.push({
      threshold,
      alpha,
      sampleCount: cases.length,
      differentPixels,
      sad,
      expectedInk,
      actualInk,
      inkPct10000: expectedInk > 0 ? Math.floor((actualInk * 10000) / expectedInk) : 10000,
    });
  }
}

results.sort((a, b) =>
  a.differentPixels - b.differentPixels ||
  a.sad - b.sad ||
  b.inkPct10000 - a.inkPct10000
);

console.log(JSON.stringify({
  samples: selected,
  base: {
    differentPixels: cases.reduce((sum, item) => sum + item.base.differentPixels, 0),
    sad: cases.reduce((sum, item) => sum + item.base.sad, 0),
    expectedInk: cases.reduce((sum, item) => sum + item.expectedInk, 0),
    actualInk: cases.reduce((sum, item) => sum + item.baseInk, 0),
  },
  bestByExact: results.slice(0, limit),
  bestBySad: [...results].sort((a, b) => a.sad - b.sad || a.differentPixels - b.differentPixels).slice(0, limit),
  bestByInk: [...results].sort((a, b) => b.inkPct10000 - a.inkPct10000 || a.differentPixels - b.differentPixels).slice(0, limit),
}, null, 2));
