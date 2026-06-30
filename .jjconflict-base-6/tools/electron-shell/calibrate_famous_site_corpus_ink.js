#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const corpusDir = path.join(root, "test", "09_baselines", "famous_site_corpus");
const defaultSamples = ["site_0_google", "site_44_the_new_york_times", "site_60_tripadvisor"];
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
  const headerEnd = bytes.indexOf(Buffer.from("\n255\n"));
  if (headerEnd < 0) return null;
  const header = bytes.slice(0, headerEnd).toString("ascii").trim().split(/\s+/);
  const width = Number.parseInt(header[1], 10);
  const height = Number.parseInt(header[2], 10);
  const dataStart = headerEnd + 5;
  if (!Number.isFinite(width) || !Number.isFinite(height)) return null;
  if (header[0] === "P6") {
    return { width, height, data: bytes.slice(dataStart, dataStart + width * height * 3) };
  }
  if (header[0] === "P3") {
    const values = bytes.slice(dataStart).toString("ascii").trim().split(/\s+/).map((v) => Number.parseInt(v, 10));
    return { width, height, data: Uint8Array.from(values.slice(0, width * height * 3)) };
  }
  return null;
}

function parseRgb(value) {
  const match = String(value || "").match(/rgb\(\s*([0-9]+)\s*,\s*([0-9]+)\s*,\s*([0-9]+)\s*\)/);
  return match ? [Number(match[1]), Number(match[2]), Number(match[3])] : [255, 255, 255];
}

function pixelAt(image, x, y) {
  const offset = (y * image.width + x) * 3;
  return [image.data[offset], image.data[offset + 1], image.data[offset + 2]];
}

function sameRgb(a, b) {
  return a[0] === b[0] && a[1] === b[1] && a[2] === b[2];
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

function blend(foreground, background, alpha) {
  const inverse = 255 - alpha;
  return [
    Math.round((foreground[0] * alpha + background[0] * inverse) / 255),
    Math.round((foreground[1] * alpha + background[1] * inverse) / 255),
    Math.round((foreground[2] * alpha + background[2] * inverse) / 255)
  ];
}

function emptyTotals() {
  return { differentPixels: 0, sad: 0, expectedInk: 0, actualInk: 0, missingInk: 0 };
}

function addTotals(total, row) {
  total.differentPixels += row.differentPixels;
  total.sad += row.sad;
  total.expectedInk += row.expectedInk;
  total.actualInk += row.actualInk;
  total.missingInk += row.missingInk;
}

function summarizeSample(sample) {
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

  const div = clampRegion(rectRegion(metrics.div.rect), chrome.width, chrome.height);
  const background = parseRgb(metrics.div.backgroundColor);
  const foreground = parseRgb(metrics.div.color);
  const base = emptyTotals();
  const expectedInkPixels = [];
  const actualBackgroundInkPixels = [];

  for (let y = 0; y < chrome.height; y += 1) {
    for (let x = 0; x < chrome.width; x += 1) {
      const expected = pixelAt(chrome, x, y);
      const actual = pixelAt(simple, x, y);
      const dr = Math.abs(expected[0] - actual[0]);
      const dg = Math.abs(expected[1] - actual[1]);
      const db = Math.abs(expected[2] - actual[2]);
      if (dr !== 0 || dg !== 0 || db !== 0) base.differentPixels += 1;
      base.sad += dr + dg + db;

      if (x >= div.left && x < div.right && y >= div.top && y < div.bottom) {
        const expectedInk = !sameRgb(expected, background);
        const actualInk = !sameRgb(actual, background);
        if (expectedInk) {
          base.expectedInk += 1;
          expectedInkPixels.push({ x, y, expected, actual });
          if (!actualInk) actualBackgroundInkPixels.push({ x, y, expected });
        }
        if (actualInk) base.actualInk += 1;
      }
    }
  }
  base.missingInk = Math.max(0, base.expectedInk - base.actualInk);

  return {
    sample,
    artifact: path.basename(simplePath),
    background,
    foreground,
    base,
    expectedInkPixels,
    actualBackgroundInkPixels
  };
}

function scoreCandidate(sampleRows, candidate) {
  const totals = emptyTotals();
  for (const row of sampleRows) {
    addTotals(totals, row.base);
    const simulatedInk = blend(row.foreground, row.background, candidate.alpha);
    for (const pixel of row.actualBackgroundInkPixels) {
      const oldDr = Math.abs(pixel.expected[0] - row.background[0]);
      const oldDg = Math.abs(pixel.expected[1] - row.background[1]);
      const oldDb = Math.abs(pixel.expected[2] - row.background[2]);
      const newDr = Math.abs(pixel.expected[0] - simulatedInk[0]);
      const newDg = Math.abs(pixel.expected[1] - simulatedInk[1]);
      const newDb = Math.abs(pixel.expected[2] - simulatedInk[2]);
      const oldSad = oldDr + oldDg + oldDb;
      const newSad = newDr + newDg + newDb;
      totals.sad += newSad - oldSad;
      if (newSad === 0) totals.differentPixels -= 1;
    }
    totals.actualInk += row.actualBackgroundInkPixels.length;
  }
  totals.missingInk = Math.max(0, totals.expectedInk - totals.actualInk);
  return {
    alpha: candidate.alpha,
    differentPixels: totals.differentPixels,
    sad: totals.sad,
    expectedInk: totals.expectedInk,
    actualInk: totals.actualInk,
    missingInk: totals.missingInk,
    actualPct10000: totals.expectedInk > 0 ? Math.floor((totals.actualInk * 10000) / totals.expectedInk) : 0
  };
}

const sampleNames = requestedSamples();
const sampleRows = sampleNames.map(summarizeSample).filter(Boolean);
const base = emptyTotals();
for (const row of sampleRows) addTotals(base, row.base);
base.actualPct10000 = base.expectedInk > 0 ? Math.floor((base.actualInk * 10000) / base.expectedInk) : 0;

const candidates = [32, 64, 96, 128, 160, 192, 224, 255].map((alpha) => ({ alpha }));
const scores = candidates.map((candidate) => scoreCandidate(sampleRows, candidate));
const byExact = [...scores].sort((a, b) => a.differentPixels - b.differentPixels || a.sad - b.sad || a.alpha - b.alpha);
const bySad = [...scores].sort((a, b) => a.sad - b.sad || a.differentPixels - b.differentPixels || a.alpha - b.alpha);
const byInk = [...scores].sort((a, b) => b.actualPct10000 - a.actualPct10000 || a.missingInk - b.missingInk || a.sad - b.sad || a.alpha - b.alpha);

console.log(JSON.stringify({
  samples: sampleRows.map((row) => row.sample),
  artifacts: Object.fromEntries(sampleRows.map((row) => [row.sample, row.artifact])),
  base,
  bestByExact: byExact[0] ?? {},
  bestBySad: bySad[0] ?? {},
  bestByInk: byInk[0] ?? {},
  candidates: scores
}, null, 2));
