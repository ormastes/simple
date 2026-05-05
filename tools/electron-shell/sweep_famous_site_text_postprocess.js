#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const baselineDir = path.join(root, 'test', 'baselines', 'famous_site_corpus');

function usage() {
  console.error('Usage: node tools/electron-shell/sweep_famous_site_text_postprocess.js [--samples=a,b] [--factors=1,1.25,1.5,2] [--expansion-alphas=16,32,48,64] [--shifts=-1:0,0:-1] [--limit=N]');
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
  let bestKey = '255,255,255';
  let bestCount = -1;
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * img.width + x) * 3;
      const key = `${img.data[p]},${img.data[p + 1]},${img.data[p + 2]}`;
      const count = (counts.get(key) || 0) + 1;
      counts.set(key, count);
      if (count > bestCount) {
        bestCount = count;
        bestKey = key;
      }
    }
  }
  return bestKey.split(',').map(Number);
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

function clampByte(value) {
  if (value < 0) return 0;
  if (value > 255) return 255;
  return Math.round(value);
}

function strengthenTowardBlack(out, idx, bg, factor) {
  for (let ch = 0; ch < 3; ch += 1) {
    const current = out[idx + ch];
    if (current !== bg[ch]) {
      const ink = bg[ch] - current;
      out[idx + ch] = clampByte(bg[ch] - ink * factor);
    }
  }
}

function strengthenTowardBlackRgb(out, idx, bg, factors) {
  for (let ch = 0; ch < 3; ch += 1) {
    const current = out[idx + ch];
    if (current !== bg[ch]) {
      const ink = bg[ch] - current;
      out[idx + ch] = clampByte(bg[ch] - ink * factors[ch]);
    }
  }
}

function simulate(sample, factor) {
  const out = Buffer.from(sample.actual.data);
  const divBottom = sample.div.y + sample.div.height;
  for (const rect of sample.textRects) {
    const line = regionFromDomRect(rect);
    const endY = Math.min(sample.actual.height, line.y + line.height);
    const endX = Math.min(sample.actual.width, line.x + line.width);
    for (let y = Math.max(0, line.y); y < endY; y += 1) {
      const bg = y < divBottom ? sample.actualDivBg : [255, 255, 255];
      for (let x = Math.max(0, line.x); x < endX; x += 1) {
        const p = (y * sample.actual.width + x) * 3;
        if (out[p] !== bg[0] || out[p + 1] !== bg[1] || out[p + 2] !== bg[2]) {
          strengthenTowardBlack(out, p, bg, factor);
        }
      }
    }
  }
  return { width: sample.actual.width, height: sample.actual.height, data: out };
}

function simulateRgb(sample, factors) {
  const out = Buffer.from(sample.actual.data);
  const divBottom = sample.div.y + sample.div.height;
  for (const rect of sample.textRects) {
    const line = regionFromDomRect(rect);
    const endY = Math.min(sample.actual.height, line.y + line.height);
    const endX = Math.min(sample.actual.width, line.x + line.width);
    for (let y = Math.max(0, line.y); y < endY; y += 1) {
      const bg = y < divBottom ? sample.actualDivBg : [255, 255, 255];
      for (let x = Math.max(0, line.x); x < endX; x += 1) {
        const p = (y * sample.actual.width + x) * 3;
        if (out[p] !== bg[0] || out[p + 1] !== bg[1] || out[p + 2] !== bg[2]) {
          strengthenTowardBlackRgb(out, p, bg, factors);
        }
      }
    }
  }
  return { width: sample.actual.width, height: sample.actual.height, data: out };
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
  if (!arg.startsWith('--samples=') && !arg.startsWith('--factors=') && !arg.startsWith('--expansion-alphas=') && !arg.startsWith('--shifts=') && !arg.startsWith('--limit=')) usage();
}

const selected = argValue('--samples', 'site_15_twitch,site_102_docker_hub').split(',').filter(Boolean);
const ids = selected[0] === 'all' ? sampleIds() : selected;
const factors = argValue('--factors', '1,1.125,1.25,1.5,2').split(',').filter(Boolean).map(Number);
const expansionAlphas = argValue('--expansion-alphas', '16,32,48,64').split(',').filter(Boolean).map(Number);
const shifts = argValue('--shifts', '-1:-1,0:-1,1:-1,-1:0,0:0,1:0,-1:1,0:1,1:1')
  .split(',')
  .filter(Boolean)
  .map(item => {
    const parts = item.split(':').map(Number);
    if (parts.length !== 2 || Number.isNaN(parts[0]) || Number.isNaN(parts[1])) usage();
    return { dx: parts[0], dy: parts[1] };
  });
const limit = Number(argValue('--limit', '10'));

const samples = ids.map(id => {
  const dir = path.join(baselineDir, id);
  const expected = readPpm(path.join(dir, 'chrome.ppm'));
  const actual = readPpm(path.join(dir, 'simple.ppm'));
  const metrics = JSON.parse(fs.readFileSync(path.join(dir, 'chrome_metrics.json'), 'utf8')).metrics;
  const div = regionFromDomRect(metrics.div.rect);
  return {
    id,
    expected,
    actual,
    div,
    textRects: metrics.textClientRects || [],
    actualDivBg: dominantColor(actual, div),
    base: compare(expected, actual),
  };
});

const candidates = factors.map(factor => {
  let differentPixels = 0;
  let sad = 0;
  for (const sample of samples) {
    const cmp = compare(sample.expected, simulate(sample, factor));
    differentPixels += cmp.differentPixels;
    sad += cmp.sad;
  }
  return { factor, sampleCount: samples.length, differentPixels, sad };
});

const rgbCandidates = [];
for (const rFactor of factors) {
  for (const gFactor of factors) {
    for (const bFactor of factors) {
      let differentPixels = 0;
      let sad = 0;
      for (const sample of samples) {
        const cmp = compare(sample.expected, simulateRgb(sample, [rFactor, gFactor, bFactor]));
        differentPixels += cmp.differentPixels;
        sad += cmp.sad;
      }
      rgbCandidates.push({ rFactor, gFactor, bFactor, sampleCount: samples.length, differentPixels, sad });
    }
  }
}

function rowBgFor(sample, y) {
  return y < sample.div.y + sample.div.height ? sample.actualDivBg : [255, 255, 255];
}

function isInkAt(sample, x, y) {
  if (x < 0 || y < 0 || x >= sample.actual.width || y >= sample.actual.height) return false;
  const p = (y * sample.actual.width + x) * 3;
  const bg = rowBgFor(sample, y);
  return sample.actual.data[p] !== bg[0] || sample.actual.data[p + 1] !== bg[1] || sample.actual.data[p + 2] !== bg[2];
}

function isAdjacentToInk(sample, x, y) {
  return isInkAt(sample, x - 1, y) ||
    isInkAt(sample, x + 1, y) ||
    isInkAt(sample, x, y - 1) ||
    isInkAt(sample, x, y + 1);
}

function simulateExpansion(sample, alpha) {
  const out = Buffer.from(sample.actual.data);
  for (const rect of sample.textRects) {
    const line = regionFromDomRect(rect);
    const endY = Math.min(sample.actual.height, line.y + line.height);
    const endX = Math.min(sample.actual.width, line.x + line.width);
    for (let y = Math.max(0, line.y); y < endY; y += 1) {
      const bg = rowBgFor(sample, y);
      for (let x = Math.max(0, line.x); x < endX; x += 1) {
        const p = (y * sample.actual.width + x) * 3;
        const isBg = sample.actual.data[p] === bg[0] && sample.actual.data[p + 1] === bg[1] && sample.actual.data[p + 2] === bg[2];
        if (isBg && isAdjacentToInk(sample, x, y)) {
          const inv = 255 - alpha;
          out[p] = Math.floor((bg[0] * inv) / 255);
          out[p + 1] = Math.floor((bg[1] * inv) / 255);
          out[p + 2] = Math.floor((bg[2] * inv) / 255);
        }
      }
    }
  }
  return { width: sample.actual.width, height: sample.actual.height, data: out };
}

const expansionCandidates = expansionAlphas.map(alpha => {
  let differentPixels = 0;
  let sad = 0;
  for (const sample of samples) {
    const cmp = compare(sample.expected, simulateExpansion(sample, alpha));
    differentPixels += cmp.differentPixels;
    sad += cmp.sad;
  }
  return { alpha, sampleCount: samples.length, differentPixels, sad };
});

function shiftScopeAllows(scope, sample, y) {
  const inDiv = y < sample.div.y + sample.div.height;
  return scope === 'all' || (scope === 'div' && inDiv) || (scope === 'overflow' && !inDiv);
}

function simulateShift(sample, dx, dy, scope = 'all') {
  const out = Buffer.from(sample.actual.data);
  const writes = [];
  for (const rect of sample.textRects) {
    const line = regionFromDomRect(rect);
    const endY = Math.min(sample.actual.height, line.y + line.height);
    const endX = Math.min(sample.actual.width, line.x + line.width);
    for (let y = Math.max(0, line.y); y < endY; y += 1) {
      if (!shiftScopeAllows(scope, sample, y)) continue;
      const bg = rowBgFor(sample, y);
      for (let x = Math.max(0, line.x); x < endX; x += 1) {
        const p = (y * sample.actual.width + x) * 3;
        const isInk = sample.actual.data[p] !== bg[0] || sample.actual.data[p + 1] !== bg[1] || sample.actual.data[p + 2] !== bg[2];
        if (isInk) {
          out[p] = bg[0];
          out[p + 1] = bg[1];
          out[p + 2] = bg[2];
          writes.push({ x: x + dx, y: y + dy, r: sample.actual.data[p], g: sample.actual.data[p + 1], b: sample.actual.data[p + 2] });
        }
      }
    }
  }
  for (const write of writes) {
    if (write.x >= 0 && write.y >= 0 && write.x < sample.actual.width && write.y < sample.actual.height) {
      const p = (write.y * sample.actual.width + write.x) * 3;
      out[p] = write.r;
      out[p + 1] = write.g;
      out[p + 2] = write.b;
    }
  }
  return { width: sample.actual.width, height: sample.actual.height, data: out };
}

const shiftCandidates = shifts.map(shift => {
  let differentPixels = 0;
  let sad = 0;
  for (const sample of samples) {
    const cmp = compare(sample.expected, simulateShift(sample, shift.dx, shift.dy));
    differentPixels += cmp.differentPixels;
    sad += cmp.sad;
  }
  return { dx: shift.dx, dy: shift.dy, sampleCount: samples.length, differentPixels, sad };
});

const scopedShiftCandidates = [];
for (const scope of ['div', 'overflow']) {
  for (const shift of shifts) {
    let differentPixels = 0;
    let sad = 0;
    for (const sample of samples) {
      const cmp = compare(sample.expected, simulateShift(sample, shift.dx, shift.dy, scope));
      differentPixels += cmp.differentPixels;
      sad += cmp.sad;
    }
    scopedShiftCandidates.push({ scope, dx: shift.dx, dy: shift.dy, sampleCount: samples.length, differentPixels, sad });
  }
}

console.log(JSON.stringify({
  samples: ids,
  base: {
    differentPixels: samples.reduce((sum, sample) => sum + sample.base.differentPixels, 0),
    sad: samples.reduce((sum, sample) => sum + sample.base.sad, 0),
  },
  bestByExact: [...candidates].sort((a, b) => a.differentPixels - b.differentPixels || a.sad - b.sad).slice(0, limit),
  bestBySad: [...candidates].sort((a, b) => a.sad - b.sad || a.differentPixels - b.differentPixels).slice(0, limit),
  bestByRgbExact: [...rgbCandidates].sort((a, b) => a.differentPixels - b.differentPixels || a.sad - b.sad).slice(0, limit),
  bestByRgbSad: [...rgbCandidates].sort((a, b) => a.sad - b.sad || a.differentPixels - b.differentPixels).slice(0, limit),
  bestByExpansionExact: [...expansionCandidates].sort((a, b) => a.differentPixels - b.differentPixels || a.sad - b.sad).slice(0, limit),
  bestByExpansionSad: [...expansionCandidates].sort((a, b) => a.sad - b.sad || a.differentPixels - b.differentPixels).slice(0, limit),
  bestByShiftExact: [...shiftCandidates].sort((a, b) => a.differentPixels - b.differentPixels || a.sad - b.sad).slice(0, limit),
  bestByShiftSad: [...shiftCandidates].sort((a, b) => a.sad - b.sad || a.differentPixels - b.differentPixels).slice(0, limit),
  bestByScopedShiftExact: [...scopedShiftCandidates].sort((a, b) => a.differentPixels - b.differentPixels || a.sad - b.sad).slice(0, limit),
  bestByScopedShiftSad: [...scopedShiftCandidates].sort((a, b) => a.sad - b.sad || a.differentPixels - b.differentPixels).slice(0, limit),
}, null, 2));
