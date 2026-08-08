// Aggregates per-fixture diff reports into one summary + a markdown table.
// Fail-closed: zero reports, or zero total compared nodes, exits non-zero.
'use strict';
const fs = require('fs');
const path = require('path');

const dir = process.argv[2];
if (!dir || !fs.existsSync(dir)) { console.error('SUMMARY_ERROR missing outdir'); process.exit(1); }
const files = fs.readdirSync(dir).filter((f) => f.endsWith('.diff.json')).sort();
if (files.length === 0) { console.error('SUMMARY_ERROR no diff reports in ' + dir); process.exit(1); }

let totDom = 0, totStyleNodes = 0, totStyleProps = 0, totDomF = 0, totStyleF = 0;
const rows = [];
const propCounts = {};
const examples = {};
for (const f of files) {
  const r = JSON.parse(fs.readFileSync(path.join(dir, f), 'utf8'));
  totDom += r.domComparedNodes; totStyleNodes += r.styleComparedNodes;
  totStyleProps += r.styleComparedProps;
  totDomF += r.domFindings.length + r.onlyInChrome.length + r.onlyInSimple.length;
  totStyleF += r.styleFindings.length;
  rows.push([r.fixture, r.domComparedNodes, r.onlyInChrome.length, r.onlyInSimple.length,
             r.domFindings.length, r.styleComparedProps, r.styleFindings.length]);
  for (const sf of r.styleFindings) {
    propCounts[sf.prop] = (propCounts[sf.prop] || 0) + 1;
    if (!examples[sf.prop]) examples[sf.prop] = `${r.fixture} ${sf.path} chrome=${sf.chrome} simple=${sf.simple} (raw c=${sf.chromeRaw} s=${sf.simpleRaw})`;
  }
}
if (totDom === 0 || totStyleProps === 0) {
  console.error('SUMMARY_ERROR vacuous: comparedDomNodes=' + totDom + ' comparedStyleProps=' + totStyleProps);
  process.exit(1);
}

let md = '# Chrome 151 vs Simple — component I/O differential\n\n';
md += `Fixtures: ${files.length} | DOM nodes compared: ${totDom} | style props compared: ${totStyleProps}\n\n`;
md += '| fixture | domNodes | onlyChrome | onlySimple | domFindings | styleProps | styleFindings |\n|---|---|---|---|---|---|---|\n';
for (const r of rows) md += '| ' + r.join(' | ') + ' |\n';
md += '\n## Divergences by property\n\n| property | count | example |\n|---|---|---|\n';
for (const p of Object.keys(propCounts).sort((a, b) => propCounts[b] - propCounts[a]))
  md += `| ${p} | ${propCounts[p]} | ${examples[p]} |\n`;
fs.writeFileSync(path.join(dir, 'SUMMARY.md'), md);

console.log('SUMMARY fixtures=' + files.length + ' domNodesCompared=' + totDom +
  ' styleNodesCompared=' + totStyleNodes + ' stylePropsCompared=' + totStyleProps +
  ' domFindings=' + totDomF + ' styleFindings=' + totStyleF);
console.log('SUMMARY_REPORT ' + path.join(dir, 'SUMMARY.md'));
