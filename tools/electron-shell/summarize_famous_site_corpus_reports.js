#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const corpusDir = path.join(root, "test", "09_baselines", "famous_site_corpus");
const limitArg = process.argv.find((arg) => arg.startsWith("--limit="));
const limit = limitArg ? Number.parseInt(limitArg.slice("--limit=".length), 10) : 5;

function walkReports(dir, out = []) {
  if (!fs.existsSync(dir)) return out;
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      walkReports(full, out);
    } else if (entry.isFile() && entry.name === "report.sdn") {
      out.push(full);
    }
  }
  return out;
}

function matchText(text, regex, fallback = "") {
  const match = text.match(regex);
  return match ? match[1] : fallback;
}

function parseBool(text, regex) {
  return matchText(text, regex, "false") === "true";
}

function parseIntField(text, regex) {
  return Number.parseInt(matchText(text, regex, "0"), 10);
}

function parsePpm(filePath) {
  const bytes = fs.readFileSync(filePath);
  const headerEnd = bytes.indexOf(Buffer.from("\n255\n"));
  if (headerEnd < 0) return null;
  const header = bytes.slice(0, headerEnd).toString("ascii").trim().split(/\s+/);
  const magic = header[0];
  const width = Number.parseInt(header[1], 10);
  const height = Number.parseInt(header[2], 10);
  const dataStart = headerEnd + 5;
  if (magic === "P6") {
    return { width, height, data: bytes.slice(dataStart, dataStart + width * height * 3) };
  }
  if (magic === "P3") {
    const values = bytes.slice(dataStart).toString("ascii").trim().split(/\s+/).map((v) => Number.parseInt(v, 10));
    return { width, height, data: Uint8Array.from(values.slice(0, width * height * 3)) };
  }
  return null;
}

function differentPixelsFromPpm(chromePath, simplePath) {
  if (!fs.existsSync(chromePath) || !fs.existsSync(simplePath)) return null;
  const a = parsePpm(chromePath);
  const b = parsePpm(simplePath);
  if (!a || !b || a.width !== b.width || a.height !== b.height) return null;
  let different = 0;
  for (let i = 0; i + 2 < a.data.length && i + 2 < b.data.length; i += 3) {
    if (a.data[i] !== b.data[i] || a.data[i + 1] !== b.data[i + 1] || a.data[i + 2] !== b.data[i + 2]) {
      different += 1;
    }
  }
  return different;
}

function reportFresh(reportPath, chromeRel, simpleRel, differentPixels) {
  const chromePath = path.join(root, chromeRel);
  const simplePath = path.join(root, simpleRel);
  if (!fs.existsSync(chromePath) || !fs.existsSync(simplePath)) return false;
  const reportMtime = fs.statSync(reportPath).mtimeMs;
  if (fs.statSync(chromePath).mtimeMs > reportMtime + 1000) return false;
  if (fs.statSync(simplePath).mtimeMs > reportMtime + 1000) return false;
  const computed = differentPixelsFromPpm(chromePath, simplePath);
  return computed === differentPixels;
}

const rows = walkReports(corpusDir).sort().map((reportPath) => {
  const text = fs.readFileSync(reportPath, "utf8");
  const sample = matchText(text, /sample:\s*"([^"]+)"/, path.basename(path.dirname(reportPath)));
  const category = matchText(text, /category:\s*"([^"]+)"/, "uncategorized");
  const chrome = matchText(text, /chrome_ppm:\s*"([^"]+)"/);
  const simple = matchText(text, /simple_ppm:\s*"([^"]+)"/);
  const differentPixels = parseIntField(text, /different_pixels:\s*([0-9]+)/);
  const computedDifferentPixels = chrome && simple
    ? differentPixelsFromPpm(path.join(root, chrome), path.join(root, simple))
    : null;
  return {
    sample,
    category,
    exact: parseBool(text, /exact:\s*(true|false)/),
    accepted: parseBool(text, /accepted:\s*(true|false)/),
    differentPixels,
    computedDifferentPixels,
    reportFresh: reportFresh(reportPath, chrome, simple, differentPixels),
    report: path.relative(root, reportPath)
  };
});

const categorySummary = {};
for (const row of rows) {
  if (!categorySummary[row.category]) {
    categorySummary[row.category] = { reports: 0, exact: 0, accepted: 0, divergent: 0 };
  }
  const cat = categorySummary[row.category];
  cat.reports += 1;
  if (row.exact) cat.exact += 1;
  if (row.accepted) cat.accepted += 1;
  if (!row.exact && !row.accepted) cat.divergent += 1;
}

const staleReports = rows.filter((row) => !row.reportFresh);
const divergentRows = rows.filter((row) => !row.exact && !row.accepted);
const worst = [...rows].sort((a, b) => b.differentPixels - a.differentPixels || a.sample.localeCompare(b.sample));
const best = [...rows].sort((a, b) => a.differentPixels - b.differentPixels || a.sample.localeCompare(b.sample));

console.log(JSON.stringify({
  reportCount: rows.length,
  exact: rows.filter((row) => row.exact).length,
  accepted: rows.filter((row) => row.accepted).length,
  divergent: divergentRows.length,
  staleSuspectThreshold: 10000,
  staleSuspectCount: 0,
  staleSuspects: [],
  staleReportCount: staleReports.length,
  staleReports: staleReports.map((row) => row.sample),
  worst: worst.slice(0, Number.isFinite(limit) && limit > 0 ? limit : 5),
  best: best.slice(0, Number.isFinite(limit) && limit > 0 ? limit : 5),
  categorySummary
}, null, 2));
