#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const corpusDir = path.join(root, "test", "09_baselines", "famous_site_corpus");

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
  const value = matchText(text, regex, "0");
  return Number.parseInt(value, 10);
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

function differentPixelsFromPpm(chromePath, simplePath) {
  const chrome = parsePpm(chromePath);
  const simple = parsePpm(simplePath);
  if (!chrome || !simple || chrome.width !== simple.width || chrome.height !== simple.height) return null;
  let different = 0;
  for (let i = 0; i + 2 < chrome.data.length && i + 2 < simple.data.length; i += 3) {
    if (chrome.data[i] !== simple.data[i] || chrome.data[i + 1] !== simple.data[i + 1] || chrome.data[i + 2] !== simple.data[i + 2]) {
      different += 1;
    }
  }
  return different;
}

function reportFresh(reportPath, text) {
  const chrome = matchText(text, /chrome_ppm:\s*"([^"]+)"/);
  const simple = matchText(text, /simple_ppm:\s*"([^"]+)"/);
  const differentPixels = parseIntField(text, /different_pixels:\s*([0-9]+)/);
  if (!chrome || !simple) return { fresh: false, computedDifferentPixels: null };
  const reportMtime = fs.statSync(reportPath).mtimeMs;
  for (const rel of [chrome, simple]) {
    const ppmPath = path.join(root, rel);
    if (!fs.existsSync(ppmPath)) return { fresh: false, computedDifferentPixels: null };
    if (fs.statSync(ppmPath).mtimeMs > reportMtime + 1000) return { fresh: false, computedDifferentPixels: null };
  }
  const computedDifferentPixels = differentPixelsFromPpm(path.join(root, chrome), path.join(root, simple));
  return {
    fresh: computedDifferentPixels === differentPixels,
    computedDifferentPixels
  };
}

const reports = walkReports(corpusDir).sort();
const failures = [];
let exact = 0;
let accepted = 0;
let divergent = 0;
let staleReportCount = 0;
let checkedPixelReportCount = 0;
let computedMismatchCount = 0;

for (const reportPath of reports) {
  const text = fs.readFileSync(reportPath, "utf8");
  const sample = matchText(text, /sample:\s*"([^"]+)"/, path.basename(path.dirname(reportPath)));
  const isExact = parseBool(text, /exact:\s*(true|false)/);
  const isAccepted = parseBool(text, /accepted:\s*(true|false)/);
  const differentPixels = parseIntField(text, /different_pixels:\s*([0-9]+)/);
  const freshness = reportFresh(reportPath, text);
  const fresh = freshness.fresh;
  if (isExact) exact += 1;
  if (isAccepted) accepted += 1;
  if (!isExact && !isAccepted) divergent += 1;
  if (!fresh) staleReportCount += 1;
  if (freshness.computedDifferentPixels !== null) checkedPixelReportCount += 1;
  if (freshness.computedDifferentPixels !== null && freshness.computedDifferentPixels !== differentPixels) {
    computedMismatchCount += 1;
  }
  if (!isExact || !isAccepted || !fresh) {
    failures.push({
      sample,
      exact: isExact,
      accepted: isAccepted,
      differentPixels,
      computedDifferentPixels: freshness.computedDifferentPixels,
      reportFresh: fresh,
      report: path.relative(root, reportPath)
    });
  }
}

failures.sort((a, b) => b.differentPixels - a.differentPixels || a.sample.localeCompare(b.sample));

const result = {
  status: reports.length > 0 && exact === reports.length && accepted === reports.length && divergent === 0 && staleReportCount === 0 ? "PASS" : "FAIL",
  reportCount: reports.length,
  exact,
  accepted,
  divergent,
  staleReportCount,
  checkedPixelReportCount,
  computedMismatchCount,
  failures: failures.slice(0, 20)
};

console.log(JSON.stringify(result, null, 2));
process.exit(result.status === "PASS" ? 0 : 1);
