#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const corpusDir = path.join(root, "test", "baselines", "famous_site_corpus");

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

function reportFresh(reportPath, text) {
  const chrome = matchText(text, /chrome_ppm:\s*"([^"]+)"/);
  const simple = matchText(text, /simple_ppm:\s*"([^"]+)"/);
  if (!chrome || !simple) return false;
  const reportMtime = fs.statSync(reportPath).mtimeMs;
  for (const rel of [chrome, simple]) {
    const ppmPath = path.join(root, rel);
    if (!fs.existsSync(ppmPath)) return false;
    if (fs.statSync(ppmPath).mtimeMs > reportMtime + 1000) return false;
  }
  return true;
}

const reports = walkReports(corpusDir).sort();
const failures = [];
let exact = 0;
let accepted = 0;
let divergent = 0;
let staleReportCount = 0;

for (const reportPath of reports) {
  const text = fs.readFileSync(reportPath, "utf8");
  const sample = matchText(text, /sample:\s*"([^"]+)"/, path.basename(path.dirname(reportPath)));
  const isExact = parseBool(text, /exact:\s*(true|false)/);
  const isAccepted = parseBool(text, /accepted:\s*(true|false)/);
  const differentPixels = parseIntField(text, /different_pixels:\s*([0-9]+)/);
  const fresh = reportFresh(reportPath, text);
  if (isExact) exact += 1;
  if (isAccepted) accepted += 1;
  if (!isExact && !isAccepted) divergent += 1;
  if (!fresh) staleReportCount += 1;
  if (!isExact || !isAccepted || !fresh) {
    failures.push({
      sample,
      exact: isExact,
      accepted: isAccepted,
      differentPixels,
      reportFresh: fresh,
      report: path.relative(root, reportPath)
    });
  }
}

failures.sort((a, b) => b.differentPixels - a.differentPixels || a.sample.localeCompare(b.sample));

const result = {
  status: reports.length > 0 && divergent === 0 && staleReportCount === 0 ? "PASS" : "FAIL",
  reportCount: reports.length,
  exact,
  accepted,
  divergent,
  staleReportCount,
  failures: failures.slice(0, 20)
};

console.log(JSON.stringify(result, null, 2));
process.exit(result.status === "PASS" ? 0 : 1);
