#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const corpusDir = path.join(root, "test", "09_baselines", "famous_site_corpus");
const defaultSamples = ["site_0_google", "site_15_twitch", "site_102_docker_hub"];
const limitArg = process.argv.find((arg) => arg.startsWith("--limit="));
const limit = limitArg ? Number.parseInt(limitArg.slice("--limit=".length), 10) : defaultSamples.length;
const sampleArg = process.argv.find((arg) => arg.startsWith("--samples="));

function requestedSamples() {
  const samples = sampleArg
    ? sampleArg.slice("--samples=".length).split(",").map((sample) => sample.trim()).filter(Boolean)
    : defaultSamples;
  const n = Number.isFinite(limit) && limit > 0 ? limit : samples.length;
  return samples.slice(0, n);
}

function parsePpm(filePath) {
  if (!fs.existsSync(filePath)) return null;
  const bytes = fs.readFileSync(filePath);
  const tokens = [];
  let index = 0;
  while (index < bytes.length && tokens.length < 4) {
    while (index < bytes.length && /\s/.test(String.fromCharCode(bytes[index]))) index += 1;
    if (bytes[index] === 35) {
      while (index < bytes.length && bytes[index] !== 10) index += 1;
      continue;
    }
    let token = "";
    while (index < bytes.length && !/\s/.test(String.fromCharCode(bytes[index]))) {
      token += String.fromCharCode(bytes[index]);
      index += 1;
    }
    if (token.length > 0) tokens.push(token);
  }
  while (index < bytes.length && /\s/.test(String.fromCharCode(bytes[index]))) index += 1;
  const width = Number.parseInt(tokens[1], 10);
  const height = Number.parseInt(tokens[2], 10);
  const dataStart = index;
  if (!Number.isFinite(width) || !Number.isFinite(height)) return null;
  if (tokens[0] === "P6" && tokens[3] === "255") {
    return { width, height, data: Uint8Array.from(bytes.slice(dataStart, dataStart + width * height * 3)) };
  }
  if (tokens[0] === "P3" && tokens[3] === "255") {
    const body = bytes.slice(dataStart).toString("ascii").replace(/#[^\n\r]*/g, " ");
    const values = body.trim().split(/\s+/).map((v) => Number.parseInt(v, 10));
    return { width, height, data: Uint8Array.from(values.slice(0, width * height * 3)) };
  }
  return null;
}

function parseRgb(value) {
  const match = String(value || "").match(/rgb\(\s*([0-9]+)\s*,\s*([0-9]+)\s*,\s*([0-9]+)\s*\)/);
  return match ? [Number(match[1]), Number(match[2]), Number(match[3])] : [255, 255, 255];
}

function offsetOf(image, x, y) {
  return (y * image.width + x) * 3;
}

function pixelAt(image, x, y) {
  const offset = offsetOf(image, x, y);
  return [image.data[offset], image.data[offset + 1], image.data[offset + 2]];
}

function sameRgb(a, b) {
  return a[0] === b[0] && a[1] === b[1] && a[2] === b[2];
}

function clampByte(value) {
  return Math.max(0, Math.min(255, Math.round(value)));
}

function scaleRgb(rgb, factors) {
  return [
    clampByte(rgb[0] * factors[0]),
    clampByte(rgb[1] * factors[1]),
    clampByte(rgb[2] * factors[2])
  ];
}

function blend(foreground, background, alpha) {
  const inverse = 255 - alpha;
  return [
    Math.round((foreground[0] * alpha + background[0] * inverse) / 255),
    Math.round((foreground[1] * alpha + background[1] * inverse) / 255),
    Math.round((foreground[2] * alpha + background[2] * inverse) / 255)
  ];
}

function writePixel(data, image, x, y, rgb) {
  const offset = offsetOf(image, x, y);
  data[offset] = rgb[0];
  data[offset + 1] = rgb[1];
  data[offset + 2] = rgb[2];
}

function rectRegion(rect) {
  return {
    left: Math.floor(rect.left ?? rect.x),
    top: Math.floor(rect.top ?? rect.y),
    right: Math.ceil(rect.right ?? ((rect.x ?? 0) + (rect.width ?? 0))),
    bottom: Math.ceil(rect.bottom ?? ((rect.y ?? 0) + (rect.height ?? 0)))
  };
}

function clampRegion(region, width, height) {
  return {
    left: Math.max(0, Math.min(width, region.left)),
    top: Math.max(0, Math.min(height, region.top)),
    right: Math.max(0, Math.min(width, region.right)),
    bottom: Math.max(0, Math.min(height, region.bottom))
  };
}

function intersectRegion(a, b) {
  return {
    left: Math.max(a.left, b.left),
    top: Math.max(a.top, b.top),
    right: Math.min(a.right, b.right),
    bottom: Math.min(a.bottom, b.bottom)
  };
}

function containsAnyRegion(regions, x, y) {
  return regions.some((region) => x >= region.left && x < region.right && y >= region.top && y < region.bottom);
}

function scoreImage(chrome, data) {
  let differentPixels = 0;
  let sad = 0;
  for (let index = 0; index < chrome.data.length; index += 3) {
    const dr = Math.abs(chrome.data[index] - data[index]);
    const dg = Math.abs(chrome.data[index + 1] - data[index + 1]);
    const db = Math.abs(chrome.data[index + 2] - data[index + 2]);
    if (dr !== 0 || dg !== 0 || db !== 0) differentPixels += 1;
    sad += dr + dg + db;
  }
  return { differentPixels, sad };
}

function loadSample(sample) {
  const dir = path.join(corpusDir, sample);
  const metricsPath = path.join(dir, "chrome_metrics.json");
  const chromePath = path.join(dir, "chrome.ppm");
  const productionPath = path.join(dir, "simple.production.ppm");
  const simplePath = fs.existsSync(productionPath) ? productionPath : path.join(dir, "simple.ppm");
  if (!fs.existsSync(metricsPath)) return null;
  const metrics = JSON.parse(fs.readFileSync(metricsPath, "utf8")).metrics;
  const chrome = parsePpm(chromePath);
  const simple = parsePpm(simplePath);
  if (!metrics || !metrics.div || !chrome || !simple || chrome.width !== simple.width || chrome.height !== simple.height) return null;

  const background = parseRgb(metrics.div.backgroundColor);
  const foreground = parseRgb(metrics.div.color);
  const div = clampRegion(rectRegion(metrics.div.rect), chrome.width, chrome.height);
  const textRects = (metrics.textClientRects || metrics.textLines || [])
    .map((entry) => intersectRegion(clampRegion(rectRegion(entry.rect ?? entry), chrome.width, chrome.height), div))
    .filter((region) => region.right > region.left && region.bottom > region.top);
  const textPixels = [];
  const textPixelKeys = new Set();
  for (const region of textRects) {
    for (let y = region.top; y < region.bottom; y += 1) {
      for (let x = region.left; x < region.right; x += 1) {
        const key = `${x},${y}`;
        if (textPixelKeys.has(key)) continue;
        const actual = pixelAt(simple, x, y);
        if (!sameRgb(actual, background)) {
          textPixelKeys.add(key);
          textPixels.push({ x, y, actual });
        }
      }
    }
  }

  return {
    sample,
    artifact: path.basename(simplePath),
    chrome,
    simple,
    background,
    foreground,
    div,
    textRects,
    textPixels,
    base: scoreImage(chrome, simple.data)
  };
}

function applyFactor(row, factors) {
  const data = Uint8Array.from(row.simple.data);
  for (const pixel of row.textPixels) {
    writePixel(data, row.simple, pixel.x, pixel.y, scaleRgb(pixel.actual, factors));
  }
  return data;
}

function applyExpansion(row, alpha) {
  const data = Uint8Array.from(row.simple.data);
  const fill = blend(row.foreground, row.background, alpha);
  const seen = new Set();
  for (const pixel of row.textPixels) {
    for (const [dx, dy] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
      const x = pixel.x + dx;
      const y = pixel.y + dy;
      if (x < 0 || y < 0 || x >= row.simple.width || y >= row.simple.height) continue;
      if (!containsAnyRegion(row.textRects, x, y)) continue;
      const key = `${x},${y}`;
      if (seen.has(key)) continue;
      seen.add(key);
      if (sameRgb(pixelAt({ width: row.simple.width, data }, x, y), row.background)) {
        writePixel(data, row.simple, x, y, fill);
      }
    }
  }
  return data;
}

function applyShift(row, dx, dy, scope) {
  const data = Uint8Array.from(row.simple.data);
  for (const pixel of row.textPixels) writePixel(data, row.simple, pixel.x, pixel.y, row.background);
  for (const pixel of row.textPixels) {
    const x = pixel.x + dx;
    const y = pixel.y + dy;
    if (x < 0 || y < 0 || x >= row.simple.width || y >= row.simple.height) continue;
    if (scope === "div" && !(x >= row.div.left && x < row.div.right && y >= row.div.top && y < row.div.bottom)) continue;
    if (scope === "text" && !containsAnyRegion(row.textRects, x, y)) continue;
    writePixel(data, row.simple, x, y, pixel.actual);
  }
  return data;
}

function emptyScore() {
  return { differentPixels: 0, sad: 0 };
}

function scoreCandidate(rows, descriptor, apply) {
  const score = emptyScore();
  let changedPixels = 0;
  for (const row of rows) {
    const data = apply(row);
    const rowScore = scoreImage(row.chrome, data);
    score.differentPixels += rowScore.differentPixels;
    score.sad += rowScore.sad;
    for (let index = 0; index < data.length; index += 3) {
      if (data[index] !== row.simple.data[index] || data[index + 1] !== row.simple.data[index + 1] || data[index + 2] !== row.simple.data[index + 2]) {
        changedPixels += 1;
      }
    }
  }
  return { ...descriptor, ...score, changedPixels };
}

function bestByExact(scores) {
  return [...scores].sort((a, b) => a.differentPixels - b.differentPixels || a.sad - b.sad || a.changedPixels - b.changedPixels)[0] ?? {};
}

function bestBySad(scores) {
  return [...scores].sort((a, b) => a.sad - b.sad || a.differentPixels - b.differentPixels || a.changedPixels - b.changedPixels)[0] ?? {};
}

const rows = requestedSamples().map(loadSample).filter(Boolean);
const base = rows.reduce((total, row) => {
  total.differentPixels += row.base.differentPixels;
  total.sad += row.base.sad;
  total.textPixels += row.textPixels.length;
  return total;
}, { differentPixels: 0, sad: 0, textPixels: 0 });

const factorScores = [0.5, 0.75, 1, 1.5, 2, 3].map((factor) =>
  scoreCandidate(rows, { factor }, (row) => applyFactor(row, [factor, factor, factor])));
const rgbScores = [0.5, 1, 2, 3].flatMap((rFactor) =>
  [0.5, 1, 2, 3].flatMap((gFactor) =>
    [0.5, 1, 2, 3].map((bFactor) =>
      scoreCandidate(rows, { rFactor, gFactor, bFactor }, (row) => applyFactor(row, [rFactor, gFactor, bFactor])))));
const expansionScores = [16, 32, 64, 96].map((alpha) =>
  scoreCandidate(rows, { alpha }, (row) => applyExpansion(row, alpha)));
const shiftScores = [-1, 0, 1].flatMap((dy) =>
  [-1, 0, 1].map((dx) =>
    scoreCandidate(rows, { dx, dy }, (row) => applyShift(row, dx, dy, "all"))));
const scopedShiftScores = ["div", "text"].flatMap((scope) =>
  [-1, 0, 1].flatMap((dy) =>
    [-1, 0, 1].map((dx) =>
      scoreCandidate(rows, { scope, dx, dy }, (row) => applyShift(row, dx, dy, scope)))));

console.log(JSON.stringify({
  samples: rows.map((row) => row.sample),
  artifacts: Object.fromEntries(rows.map((row) => [row.sample, row.artifact])),
  base,
  bestByExact: bestByExact(factorScores),
  bestBySad: bestBySad(factorScores),
  bestByRgbExact: bestByExact(rgbScores),
  bestByRgbSad: bestBySad(rgbScores),
  bestByExpansionExact: bestByExact(expansionScores),
  bestByExpansionSad: bestBySad(expansionScores),
  bestByShiftExact: bestByExact(shiftScores),
  bestByShiftSad: bestBySad(shiftScores),
  bestByScopedShiftExact: bestByExact(scopedShiftScores),
  bestByScopedShiftSad: bestBySad(scopedShiftScores),
  candidates: {
    factors: factorScores,
    rgbCount: rgbScores.length,
    expansions: expansionScores,
    shifts: shiftScores,
    scopedShifts: scopedShiftScores
  },
  factorCandidates: factorScores,
  expansionCandidates: expansionScores
}, null, 2));
