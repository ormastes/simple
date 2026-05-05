#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const baselineDir = path.join(root, 'test', 'baselines', 'famous_site_corpus');

function usage() {
  console.error('Usage: node tools/electron-shell/summarize_famous_site_corpus_reports.js [--limit=N]');
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
    while (pos < bytes.length && !isWs(bytes[pos])) {
      out += String.fromCharCode(bytes[pos]);
      pos += 1;
    }
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

function differentPixels(expected, actual) {
  if (expected.width !== actual.width || expected.height !== actual.height) return null;
  let count = 0;
  for (let i = 0; i < expected.data.length; i += 3) {
    if (
      expected.data[i] !== actual.data[i] ||
      expected.data[i + 1] !== actual.data[i + 1] ||
      expected.data[i + 2] !== actual.data[i + 2]
    ) {
      count += 1;
    }
  }
  return count;
}

function parseReport(filePath) {
  const text = fs.readFileSync(filePath, 'utf8');
  function capture(re, fallback = '') {
    const match = text.match(re);
    return match ? match[1] : fallback;
  }
  return {
    sample: capture(/sample:\s+"([^"]+)"/),
    name: capture(/name:\s+"([^"]+)"/),
    category: capture(/category:\s+"([^"]+)"/),
    exact: capture(/exact:\s+(true|false)/) === 'true',
    accepted: capture(/accepted:\s+(true|false)/) === 'true',
    differentPixels: Number(capture(/different_pixels:\s+([0-9]+)/, '0')),
    matchPct10000: Number(capture(/match_pct_10000:\s+([0-9]+)/, '0')),
    perceptualPct10000: Number(capture(/perceptual_pct_10000:\s+([0-9]+)/, '0')),
    maxChannelDiff: Number(capture(/max_channel_diff:\s+([0-9]+)/, '0')),
  };
}

function reportWithFreshness(id) {
  const dir = path.join(baselineDir, id);
  const reportPath = path.join(dir, 'report.sdn');
  const report = parseReport(reportPath);
  const chromePath = path.join(dir, 'chrome.ppm');
  const simplePath = path.join(dir, 'simple.ppm');
  if (!fs.existsSync(chromePath) || !fs.existsSync(simplePath)) return report;

  const computedDifferentPixels = differentPixels(readPpm(chromePath), readPpm(simplePath));
  return {
    ...report,
    computedDifferentPixels,
    reportFresh: computedDifferentPixels === report.differentPixels,
  };
}

function loadReports() {
  if (!fs.existsSync(baselineDir)) return [];
  return fs.readdirSync(baselineDir)
    .filter(id => fs.existsSync(path.join(baselineDir, id, 'report.sdn')))
    .map(reportWithFreshness)
    .sort((a, b) => b.differentPixels - a.differentPixels || a.sample.localeCompare(b.sample));
}

function categorySummary(reports) {
  const out = {};
  for (const report of reports) {
    if (!out[report.category]) {
      out[report.category] = { count: 0, accepted: 0, differentPixels: 0 };
    }
    out[report.category].count += 1;
    if (report.accepted) out[report.category].accepted += 1;
    out[report.category].differentPixels += report.differentPixels;
  }
  return Object.fromEntries(Object.entries(out).sort((a, b) => a[0].localeCompare(b[0])));
}

function staleSuspects(reports) {
  // Current refreshed famous-site samples are in the 2.4k-2.9k range. Reports
  // above 10k are older full-viewport/color captures and should be refreshed
  // before being used as precise renderer target rankings.
  return reports.filter(report => report.differentPixels > 10000);
}

function staleReportSuspects(reports) {
  return reports.filter(report => report.reportFresh === false);
}

for (const arg of process.argv.slice(2)) {
  if (arg === '-h' || arg === '--help') usage();
  if (!arg.startsWith('--limit=')) usage();
}

const limit = Number(argValue('--limit', '10'));
const reports = loadReports();
const accepted = reports.filter(report => report.accepted).length;
const exact = reports.filter(report => report.exact).length;
const divergent = reports.length - accepted;
const worst = reports.slice(0, limit);
const best = [...reports].sort((a, b) => a.differentPixels - b.differentPixels || a.sample.localeCompare(b.sample)).slice(0, limit);
const stale = staleSuspects(reports);
const staleReports = staleReportSuspects(reports);

console.log(JSON.stringify({
  reportCount: reports.length,
  exact,
  accepted,
  divergent,
  staleSuspectThreshold: 10000,
  staleSuspectCount: stale.length,
  staleSuspects: stale.slice(0, limit),
  staleReportCount: staleReports.length,
  staleReports: staleReports.slice(0, limit),
  worst,
  best,
  categorySummary: categorySummary(reports),
}, null, 2));
