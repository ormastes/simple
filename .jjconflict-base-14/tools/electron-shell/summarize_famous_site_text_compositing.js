#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const corpusDir = path.join(root, "test", "09_baselines", "famous_site_corpus");
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

function clampRegion(region, width, height) {
  return {
    left: Math.max(0, Math.min(width, region.left)),
    top: Math.max(0, Math.min(height, region.top)),
    right: Math.max(0, Math.min(width, region.right)),
    bottom: Math.max(0, Math.min(height, region.bottom))
  };
}

function isChromatic(rgb) {
  return rgb[0] !== rgb[1] || rgb[1] !== rgb[2];
}

function sampleDirs() {
  if (!fs.existsSync(corpusDir)) return [];
  return fs.readdirSync(corpusDir, { withFileTypes: true })
    .filter((entry) => entry.isDirectory() && entry.name.startsWith("site_"))
    .map((entry) => path.join(corpusDir, entry.name))
    .sort();
}

function summarizeSample(dir) {
  const sample = path.basename(dir);
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
  const channelAbsoluteDiff = { r: 0, g: 0, b: 0 };
  const channelSignedDiff = { r: 0, g: 0, b: 0 };
  let expectedInk = 0;
  let actualInk = 0;
  let expectedChromaticInk = 0;
  let differentPixels = 0;
  let sad = 0;
  for (let y = div.top; y < div.bottom; y += 1) {
    for (let x = div.left; x < div.right; x += 1) {
      const expected = pixelAt(chrome, x, y);
      const actual = pixelAt(simple, x, y);
      if (!sameRgb(expected, background)) {
        expectedInk += 1;
        if (isChromatic(expected)) expectedChromaticInk += 1;
      }
      if (!sameRgb(actual, background)) actualInk += 1;
      const dr = Math.abs(expected[0] - actual[0]);
      const dg = Math.abs(expected[1] - actual[1]);
      const db = Math.abs(expected[2] - actual[2]);
      if (dr !== 0 || dg !== 0 || db !== 0) differentPixels += 1;
      sad += dr + dg + db;
      channelAbsoluteDiff.r += dr;
      channelAbsoluteDiff.g += dg;
      channelAbsoluteDiff.b += db;
      channelSignedDiff.r += expected[0] - actual[0];
      channelSignedDiff.g += expected[1] - actual[1];
      channelSignedDiff.b += expected[2] - actual[2];
    }
  }
  return {
    sample,
    artifact: path.basename(simplePath),
    expectedBackground: background.join(","),
    expectedInk,
    actualInk,
    missingInk: expectedInk - actualInk,
    actualPct10000: expectedInk > 0 ? Math.floor((actualInk * 10000) / expectedInk) : 0,
    expectedChromaticInk,
    differentPixels,
    sad,
    channelSignedDiff,
    channelAbsoluteDiff
  };
}

const rows = sampleDirs().map(summarizeSample).filter(Boolean);
const n = Number.isFinite(limit) && limit > 0 ? limit : 5;
const byInk = [...rows].sort((a, b) => b.missingInk - a.missingInk || a.sample.localeCompare(b.sample));
const byDiff = [...rows].sort((a, b) => b.differentPixels - a.differentPixels || b.sad - a.sad || a.sample.localeCompare(b.sample));

console.log(JSON.stringify({
  reportCount: rows.length,
  productionArtifactCount: rows.filter((row) => row.artifact === "simple.production.ppm").length,
  worstByInk: byInk.slice(0, n),
  worstByDiff: byDiff.slice(0, n)
}, null, 2));
