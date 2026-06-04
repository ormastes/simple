#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const corpusDir = path.join(root, "test", "baselines", "famous_site_corpus");
const limitArg = process.argv.find((arg) => arg.startsWith("--limit="));
const limit = limitArg ? Number.parseInt(limitArg.slice("--limit=".length), 10) : 5;

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

function pixelAt(image, x, y) {
  const offset = (y * image.width + x) * 3;
  return [image.data[offset], image.data[offset + 1], image.data[offset + 2]];
}

function sameRgb(a, b) {
  return a[0] === b[0] && a[1] === b[1] && a[2] === b[2];
}

function nonWhite(p) {
  return p[0] !== 255 || p[1] !== 255 || p[2] !== 255;
}

function parseRgb(value) {
  const match = String(value || "").match(/rgb\(\s*([0-9]+)\s*,\s*([0-9]+)\s*,\s*([0-9]+)\s*\)/);
  return match ? [Number(match[1]), Number(match[2]), Number(match[3])] : [255, 255, 255];
}

function rectRegion(rect) {
  return {
    left: Math.floor(rect.left ?? rect.x),
    top: Math.floor(rect.top ?? rect.y),
    right: Math.ceil(rect.right ?? ((rect.x ?? 0) + (rect.width ?? 0))),
    bottom: Math.ceil(rect.bottom ?? ((rect.y ?? 0) + (rect.height ?? 0)))
  };
}

function unionOverflowTextRegion(metrics) {
  const div = rectRegion(metrics.div.rect);
  const rects = metrics.textClientRects || [];
  const region = { left: Infinity, top: Infinity, right: 0, bottom: 0 };
  for (const rect of rects) {
    const r = rectRegion(rect);
    r.top = Math.max(r.top, div.bottom);
    if (r.bottom <= r.top) continue;
    region.left = Math.min(region.left, r.left);
    region.top = Math.min(region.top, r.top);
    region.right = Math.max(region.right, r.right);
    region.bottom = Math.max(region.bottom, r.bottom);
  }
  return region.right > region.left && region.bottom > region.top ? region : null;
}

function clampRegion(region, width, height) {
  return {
    left: Math.max(0, Math.min(width, region.left)),
    top: Math.max(0, Math.min(height, region.top)),
    right: Math.max(0, Math.min(width, region.right)),
    bottom: Math.max(0, Math.min(height, region.bottom))
  };
}

function countOverflowCoverage(expected, actual, region) {
  if (!region) return { expectedPixels: 0, actualPixels: 0, missingPixels: 0, actualPct10000: 0 };
  const r = clampRegion(region, expected.width, expected.height);
  let expectedPixels = 0;
  let actualPixels = 0;
  for (let y = r.top; y < r.bottom; y += 1) {
    for (let x = r.left; x < r.right; x += 1) {
      if (nonWhite(pixelAt(expected, x, y))) expectedPixels += 1;
      if (nonWhite(pixelAt(actual, x, y))) actualPixels += 1;
    }
  }
  return {
    expectedPixels,
    actualPixels,
    missingPixels: expectedPixels - actualPixels,
    actualPct10000: expectedPixels > 0 ? Math.floor((actualPixels * 10000) / expectedPixels) : 0
  };
}

function countDivInkCoverage(expected, actual, metrics) {
  const div = clampRegion(rectRegion(metrics.div.rect), expected.width, expected.height);
  const background = parseRgb(metrics.div.backgroundColor);
  let expectedPixels = 0;
  let actualPixels = 0;
  let differentPixels = 0;
  for (let y = div.top; y < div.bottom; y += 1) {
    for (let x = div.left; x < div.right; x += 1) {
      const e = pixelAt(expected, x, y);
      const a = pixelAt(actual, x, y);
      if (!sameRgb(e, background)) expectedPixels += 1;
      if (!sameRgb(a, background)) actualPixels += 1;
      if (!sameRgb(e, a)) differentPixels += 1;
    }
  }
  return {
    expectedPixels,
    actualPixels,
    missingPixels: expectedPixels - actualPixels,
    actualPct10000: expectedPixels > 0 ? Math.floor((actualPixels * 10000) / expectedPixels) : 0,
    differentPixels,
    expectedBackground: background.join(",")
  };
}

function sampleDirs() {
  if (!fs.existsSync(corpusDir)) return [];
  return fs.readdirSync(corpusDir, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => path.join(corpusDir, entry.name))
    .sort();
}

const rows = [];
let productionArtifactCount = 0;
for (const dir of sampleDirs()) {
  const sample = path.basename(dir);
  const metricsPath = path.join(dir, "chrome_metrics.json");
  const chromePath = path.join(dir, "chrome.ppm");
  const productionPath = path.join(dir, "simple.production.ppm");
  const simplePath = fs.existsSync(productionPath) ? productionPath : path.join(dir, "simple.ppm");
  if (simplePath === productionPath) productionArtifactCount += 1;
  if (!fs.existsSync(metricsPath)) continue;
  const metrics = JSON.parse(fs.readFileSync(metricsPath, "utf8")).metrics;
  const chrome = parsePpm(chromePath);
  const simple = parsePpm(simplePath);
  if (!metrics || !metrics.div || !chrome || !simple || chrome.width !== simple.width || chrome.height !== simple.height) continue;
  const overflow = countOverflowCoverage(chrome, simple, unionOverflowTextRegion(metrics));
  const divInk = countDivInkCoverage(chrome, simple, metrics);
  rows.push({
    sample,
    artifact: path.basename(simplePath),
    overflow,
    divInk,
    div: { differentPixels: divInk.differentPixels }
  });
}

function sortedBy(rows, selector) {
  return [...rows].sort((a, b) => selector(b) - selector(a) || a.sample.localeCompare(b.sample));
}

const n = Number.isFinite(limit) && limit > 0 ? limit : 5;
console.log(JSON.stringify({
  reportCount: rows.length,
  analyzedCount: rows.length,
  productionArtifactCount,
  worstOverflow: sortedBy(rows, (row) => row.overflow.missingPixels).slice(0, n).map((row) => ({
    sample: row.sample,
    artifact: row.artifact,
    ...row.overflow
  })),
  worstDivInk: sortedBy(rows, (row) => row.divInk.missingPixels).slice(0, n).map((row) => ({
    sample: row.sample,
    artifact: row.artifact,
    expectedBackground: row.divInk.expectedBackground,
    expectedPixels: row.divInk.expectedPixels,
    actualPixels: row.divInk.actualPixels,
    missingPixels: row.divInk.missingPixels,
    actualPct10000: row.divInk.actualPct10000
  })),
  worstDiv: sortedBy(rows, (row) => row.div.differentPixels).slice(0, n).map((row) => ({
    sample: row.sample,
    artifact: row.artifact,
    differentPixels: row.div.differentPixels
  }))
}, null, 2));
