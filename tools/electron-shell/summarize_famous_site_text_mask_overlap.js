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
  let expectedInk = 0;
  let actualInk = 0;
  let overlapInk = 0;
  let falsePositiveInk = 0;
  for (let y = div.top; y < div.bottom; y += 1) {
    for (let x = div.left; x < div.right; x += 1) {
      const expected = !sameRgb(pixelAt(chrome, x, y), background);
      const actual = !sameRgb(pixelAt(simple, x, y), background);
      if (expected) expectedInk += 1;
      if (actual) actualInk += 1;
      if (expected && actual) overlapInk += 1;
      if (!expected && actual) falsePositiveInk += 1;
    }
  }
  const missingInk = expectedInk - overlapInk;
  return {
    sample,
    artifact: path.basename(simplePath),
    expectedBackground: background.join(","),
    expectedInk,
    actualInk,
    overlapInk,
    falsePositiveInk,
    missingInk,
    precisionPct10000: actualInk > 0 ? Math.floor((overlapInk * 10000) / actualInk) : 0,
    recallPct10000: expectedInk > 0 ? Math.floor((overlapInk * 10000) / expectedInk) : 0
  };
}

const rows = sampleDirs().map(summarizeSample).filter(Boolean);
const n = Number.isFinite(limit) && limit > 0 ? limit : 5;
const byRecall = [...rows].sort((a, b) => a.recallPct10000 - b.recallPct10000 || b.missingInk - a.missingInk || a.sample.localeCompare(b.sample));
const byFalsePositive = [...rows].sort((a, b) => b.falsePositiveInk - a.falsePositiveInk || a.sample.localeCompare(b.sample));

console.log(JSON.stringify({
  reportCount: rows.length,
  productionArtifactCount: rows.filter((row) => row.artifact === "simple.production.ppm").length,
  worstByRecall: byRecall.slice(0, n),
  worstByFalsePositive: byFalsePositive.slice(0, n)
}, null, 2));
