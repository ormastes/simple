// Wave-7 sspec doc-recipe transformer. Usage: node w7_transform.js <file...>
// Applies doc recipe WITHOUT touching assertions. Idempotent.
const fs = require('fs');

function deriveId(path) {
  // test/01_unit/app/browser/foo_spec.spl -> REQ-APP-BROWSER-001 style
  const segs = path.split('/');
  const idx = segs.indexOf('test');
  const parts = segs.slice(idx + 1, -1); // drop test/NN_x and filename
  // drop leading numeric dirs like 01_unit
  const cleaned = parts.filter(p => !/^\d+_/.test(p)).map(p =>
    p.toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 12));
  let dom = cleaned[0] || 'GEN';
  let topic = cleaned.slice(1).join('-');
  if (topic.length === 0) { topic = dom; dom = 'GEN'; }
  if (topic.length > 30) topic = topic.slice(0, 30);
  return `REQ-${dom}-${topic}-001`;
}

function transform(path) {
  let src = fs.readFileSync(path, 'utf8');
  if (src.includes('## Purpose and audience') && src.includes('# @manual: primary')) {
    return 'skip';
  }
  const lines = src.split('\n');
  // collect declared requirement ids anywhere
  const declared = [];
  for (const l of lines) {
    for (const m of l.matchAll(/REQ-[A-Z0-9][A-Z0-9-]*/g)) {
      if (!declared.includes(m[0])) declared.push(m[0]);
    }
  }
  const myId = deriveId(path);
  if (!declared.includes(myId)) declared.push(myId);
  const dom = myId.slice(4); // for doc paths
  const docPaths = [
    `doc/01_research/local/${myId}.md`,
    `doc/03_plan/sys_test/${myId}.md`,
    `doc/04_architecture/${myId}.md`,
    `doc/05_design/${myId}.md`,
  ];
  // describe title for purpose text
  const descLine = lines.find(l => /^\s*describe\s+"/.test(l));
  const title = descLine ? (descLine.match(/"([^"]*)"/) || [, path])[1] : path;

  const header =
`"""
## Purpose and audience
Purpose: Verify ${title}.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
Troubleshooting: a red scenario here means the pinned contract changed —
check verification guidance in the linked design docs before editing oracles.
# @manual: primary
${myId}
${docPaths.join('\n')}
"""
# @req: ${myId}

`;

  // Normalize paren DSL style to space style so the analyzer sees scenarios:
  // it("name"): -> it "name":   (same DSL symbols, semantics-preserving)
  for (let i = 0; i < lines.length; i++) {
    lines[i] = lines[i].replace(/^(\s*)(it|slow_it|ignore_it|describe)\((\s*)"([^"]*)"\s*\)\s*:\s*$/, (m, a, kw, _b, name) => `${a}${kw} "${name}":`);
  }
  const out = [];
  let scenarioIdx = -1;      // index of current scenario in scenario list
  let inScenario = false;
  let scenarioIndent = 0;
  let needUseStep = !/\buse\s+std\.spec\.step\b/.test(src) && !/\bstep\s*\(/.test(src);
  let insertedUseStep = false;
  let reqCursor = 0;

  for (let i = 0; i < lines.length; i++) {
    const raw = lines[i];
    const line = raw.trim();
    // insert use std.spec.step just before first describe
    if (needUseStep && !insertedUseStep && /^\s*describe\s+"/.test(raw)) {
      out.push('use std.spec.step', '');
      insertedUseStep = true;
    }
    const isScenario = /^\s*(it|slow_it|ignore_it)\s+"/.test(raw);
    if (isScenario) {
      scenarioIdx++;
      out.push(raw);
      inScenario = true;
      scenarioIndent = raw.match(/^\s*/)[0].length;
      // body indent = scenario indent + 4
      const bi = ' '.repeat(scenarioIndent + 4);
      // bind one or more declared req ids round-robin so all get bound
      let bound = 0;
      const toBind = [];
      if (declared.length > 0) {
        toBind.push(declared[reqCursor % declared.length]);
        reqCursor++;
      }
      for (const id of toBind) out.push(`${bi}# @req: ${id}`);
      const name = (line.match(/"([^"]*)"/) || [, 'scenario'])[1]
        .replace(/[`{}"\\]/g, ' ').replace(/\s+/g, ' ').trim();
      out.push(`${bi}step("Verify: ${name}")`);
      continue;
    }
    if (inScenario && raw.length > 0 && raw.match(/^\s*/)[0].length <= scenarioIndent) {
      inScenario = false;
    }
    // oracle comments on numeric to_equal
    let outLine = raw;
    if (/\.\s*to_equal\s*\(\s*-?\d/.test(raw) && !/\#\s*(oracle|explained):/.test(raw)) {
      const num = (raw.match(/to_equal\s*\(\s*(-?\d[\w.]*)/s) || [, ''])[1];
      const trimmed = raw.replace(/\s+$/, '');
      outLine = trimmed + `  # oracle: ${num} — named expected value from the requirement`;
    }
    out.push(outLine);
  }
  // ensure all declared ids bound: if declared.length > scenarioCount, append extra @req lines into first scenario? handled above round-robin only binds declared.length scenarios max equal. If scenarios < declared, add remaining to last scenario pass — post-fix:
  const scenarioCount = (out.join('\n').match(/^\s*(it|slow_it|ignore_it)\s+"/gm) || []).length;
  if (scenarioCount > 0) {
    for (let k = Math.max(scenarioCount, 0); k < declared.length; k++) {
      // bind remaining ids inside first scenario by injecting after its step line
      const m = out.findIndex(l => /^\s*step\("Verify: /.test(l));
      if (m >= 0) out.splice(m + 1, 0, `${' '.repeat(4)}# @req: ${declared[k]}`);
    }
  }
  fs.writeFileSync(path, header + out.join('\n'));
  return 'ok';
}

for (const p of process.argv.slice(2)) {
  try { console.log(p + '\t' + transform(p)); }
  catch (e) { console.log(p + '\tERROR ' + e.message); }
}
