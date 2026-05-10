#!/usr/bin/env node

const { execFileSync } = require('child_process');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const summaryTool = path.join(root, 'tools', 'electron-shell', 'summarize_famous_site_corpus_reports.js');
const fs = require('fs');

function usage() {
  console.error('Usage: node tools/electron-shell/verify_famous_site_corpus_completion.js [--expected-count=N] [--expected-font-count=N]');
  process.exit(2);
}

function argValue(name, fallback) {
  const prefix = `${name}=`;
  const arg = process.argv.slice(2).find(item => item.startsWith(prefix));
  return arg ? arg.slice(prefix.length) : fallback;
}

for (const arg of process.argv.slice(2)) {
  if (arg === '-h' || arg === '--help') usage();
  if (!arg.startsWith('--expected-count=') && !arg.startsWith('--expected-font-count=')) usage();
}

const expectedCount = Number(argValue('--expected-count', '132'));
const expectedFontCount = Number(argValue('--expected-font-count', '24'));
const summaryText = execFileSync(process.execPath, [summaryTool, '--limit=5'], {
  cwd: root,
  encoding: 'utf8',
});
const summary = JSON.parse(summaryText);
const failures = [];

function unescapeSdn(value) {
  return value.replace(/\\"/g, '"').replace(/\\\\/g, '\\');
}

function parseManifestSamples() {
  const manifestPath = path.join(root, 'test', 'fixtures', 'famous_site_corpus', 'manifest.sdn');
  const text = fs.readFileSync(manifestPath, 'utf8');
  const samples = [];
  const re = /id:\s+"((?:\\"|[^"])*)".*?font_family:\s+"((?:\\"|[^"])*)".*?chrome_metrics:\s+"((?:\\"|[^"])*)"/g;
  let match;
  while ((match = re.exec(text)) !== null) {
    samples.push({
      id: unescapeSdn(match[1]),
      fontFamily: unescapeSdn(match[2]),
      metricsPath: unescapeSdn(match[3]),
    });
  }
  return samples;
}

function metricAnchor(fontFamily) {
  return fontFamily.split(',')[0].replace(/"/g, '').trim();
}

function fontCoverage(samples) {
  const distinct = new Set(samples.map(sample => sample.fontFamily));
  const missing = [];
  for (const sample of samples) {
    const metricsPath = path.join(root, sample.metricsPath);
    if (!fs.existsSync(metricsPath)) {
      missing.push({ sample: sample.id, fontFamily: sample.fontFamily, reason: 'missing metrics' });
      continue;
    }
    const metrics = fs.readFileSync(metricsPath, 'utf8');
    const anchor = metricAnchor(sample.fontFamily);
    if (!metrics.includes(anchor)) {
      missing.push({ sample: sample.id, fontFamily: sample.fontFamily, anchor, reason: 'font anchor absent from Chrome metrics' });
    }
  }
  return {
    sampleCount: samples.length,
    distinctFontCount: distinct.size,
    distinctFonts: [...distinct].sort(),
    missingMetricFonts: missing,
  };
}

const manifestSamples = parseManifestSamples();
const fontSummary = fontCoverage(manifestSamples);

if (summary.reportCount !== expectedCount) {
  failures.push(`reportCount ${summary.reportCount} != ${expectedCount}`);
}
if (fontSummary.sampleCount !== expectedCount) {
  failures.push(`font manifest sampleCount ${fontSummary.sampleCount} != ${expectedCount}`);
}
if (fontSummary.distinctFontCount !== expectedFontCount) {
  failures.push(`distinctFontCount ${fontSummary.distinctFontCount} != ${expectedFontCount}`);
}
if (fontSummary.missingMetricFonts.length !== 0) {
  failures.push(`missingMetricFonts ${fontSummary.missingMetricFonts.length} != 0`);
}
if (summary.staleSuspectCount !== 0) {
  failures.push(`staleSuspectCount ${summary.staleSuspectCount} != 0`);
}
if (summary.staleReportCount !== 0) {
  failures.push(`staleReportCount ${summary.staleReportCount} != 0`);
}
if (summary.exact !== summary.reportCount) {
  failures.push(`exact ${summary.exact} != reportCount ${summary.reportCount}`);
}
if (summary.accepted !== summary.reportCount) {
  failures.push(`accepted ${summary.accepted} != reportCount ${summary.reportCount}`);
}
if (summary.divergent !== 0) {
  failures.push(`divergent ${summary.divergent} != 0`);
}

const result = {
  status: failures.length === 0 ? 'PASS' : 'FAIL',
  reportCount: summary.reportCount,
  exact: summary.exact,
  accepted: summary.accepted,
  divergent: summary.divergent,
  staleSuspectCount: summary.staleSuspectCount,
  staleReportCount: summary.staleReportCount,
  fontCoverage: {
    sampleCount: fontSummary.sampleCount,
    distinctFontCount: fontSummary.distinctFontCount,
    missingMetricFonts: fontSummary.missingMetricFonts.slice(0, 10),
  },
  worst: summary.worst,
  failures,
};

console.log(JSON.stringify(result, null, 2));
process.exit(failures.length === 0 ? 0 : 1);
