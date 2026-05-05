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

function loadReports() {
  if (!fs.existsSync(baselineDir)) return [];
  return fs.readdirSync(baselineDir)
    .map(id => path.join(baselineDir, id, 'report.sdn'))
    .filter(filePath => fs.existsSync(filePath))
    .map(parseReport)
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

console.log(JSON.stringify({
  reportCount: reports.length,
  exact,
  accepted,
  divergent,
  staleSuspectThreshold: 10000,
  staleSuspectCount: stale.length,
  staleSuspects: stale.slice(0, limit),
  worst,
  best,
  categorySummary: categorySummary(reports),
}, null, 2));
