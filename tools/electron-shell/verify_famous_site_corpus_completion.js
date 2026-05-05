#!/usr/bin/env node

const { execFileSync } = require('child_process');
const path = require('path');

const root = path.resolve(__dirname, '..', '..');
const summaryTool = path.join(root, 'tools', 'electron-shell', 'summarize_famous_site_corpus_reports.js');

function usage() {
  console.error('Usage: node tools/electron-shell/verify_famous_site_corpus_completion.js [--expected-count=N]');
  process.exit(2);
}

function argValue(name, fallback) {
  const prefix = `${name}=`;
  const arg = process.argv.slice(2).find(item => item.startsWith(prefix));
  return arg ? arg.slice(prefix.length) : fallback;
}

for (const arg of process.argv.slice(2)) {
  if (arg === '-h' || arg === '--help') usage();
  if (!arg.startsWith('--expected-count=')) usage();
}

const expectedCount = Number(argValue('--expected-count', '132'));
const summaryText = execFileSync(process.execPath, [summaryTool, '--limit=5'], {
  cwd: root,
  encoding: 'utf8',
});
const summary = JSON.parse(summaryText);
const failures = [];

if (summary.reportCount !== expectedCount) {
  failures.push(`reportCount ${summary.reportCount} != ${expectedCount}`);
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
  worst: summary.worst,
  failures,
};

console.log(JSON.stringify(result, null, 2));
process.exit(failures.length === 0 ? 0 : 1);
