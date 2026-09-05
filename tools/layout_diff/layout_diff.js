#!/usr/bin/env node
// Numeric differ for the Chrome<->Simple component-level layout differential.
//
// Consumes  out/chrome/<fixture>.chrome.json  and  out/simple/<fixture>.simple.json
// and emits  out/report.json + a worst-first text table on stdout.
//
// Fail-closed contract:
//   * a fixture present on one side only  -> FIXTURE_MISSING  (failure)
//   * a node that cannot be paired        -> UNPAIRED_*       (failure, never skipped)
//   * zero compared nodes overall         -> exit 3           (vacuous run)
//
// See CONTRACT.md for the normalization rules this implements.

const fs = require('fs');
const path = require('path');

// Chrome reports geometry in css px already converted out of LayoutUnit
// (1/64 px == 0.015625). Simple's layout is integer-css-px throughout
// (LayoutResult.bx/by/bw/bh are [i32]). So the smallest divergence Simple can
// possibly express is 1 px, and any Chrome value is at worst 0.5 px away from
// its own correct rounding. EPS_GEOM = 0.5 is therefore the tightest threshold
// that does not manufacture failures out of pure integer quantization, and it
// is 32x coarser than Chrome's own LayoutUnit granularity - deliberately, since
// Simple cannot represent subpixel positions at all.
const EPS_GEOM = 0.5;

const ELEMENT_SKIP = new Set(['head', 'meta', 'style', 'script', 'title', 'link', 'base']);

function normTag(t) {
  if (!t) return '?';
  const l = t.toLowerCase();
  if (l === '#document') return '#root';
  return l;
}

// ---------------------------------------------------------------- node keys
// Pairing strategy (identical on both sides):
//   1. An element carrying an `id` attribute keys as `#<id>`. Fixtures give
//      every interesting element an id, so this is the primary pairing.
//   2. Anything else keys as <parentKey>/<tag>[<ordinal>], where ordinal counts
//      preceding *retained* siblings with the same normalized tag. This covers
//      anonymous/implicit boxes and text nodes.
//   3. Nodes not retained on a side (head/style/script subtrees, whitespace-only
//      text) are dropped from BOTH trees before keys are computed, so ordinals
//      line up.
// Any key present on exactly one side is a reported failure, not a skip.
function assignKeys(nodes) {
  const byParent = new Map();
  for (const n of nodes) {
    if (!byParent.has(n.parentKeyId)) byParent.set(n.parentKeyId, []);
    byParent.get(n.parentKeyId).push(n);
  }
  const counters = new Map();
  const keyOf = new Map();
  // nodes arrive in document order, so a single pass suffices
  for (const n of nodes) {
    let parentKey = n.parentKeyId === null ? '' : keyOf.get(n.parentKeyId);
    if (parentKey === undefined) parentKey = '';
    let key;
    if (n.id) {
      key = '#' + n.id;
    } else {
      const ck = parentKey + '|' + n.tag;
      const ord = counters.get(ck) || 0;
      counters.set(ck, ord + 1);
      key = parentKey + '/' + n.tag + '[' + ord + ']';
    }
    keyOf.set(n.selfId, key);
    n.key = key;
  }
  return nodes;
}

// Chrome emits ONE textBox per inline fragment, and a single visual line can
// carry several fragments (a collapsed whitespace run, a bidi/font run, a
// source newline). Simple emits one entry per LINE. Normalize Chrome to lines
// by grouping fragments that share a y, then concatenating in x order — that
// puts both engines in the same unit before any break position is compared.
function groupTextBoxesIntoLines(boxes) {
  const byY = new Map();
  for (const b of boxes) {
    const k = Math.round(b.y * 4) / 4; // quarter-px bucket: same-line fragments
    if (!byY.has(k)) byY.set(k, []);
    byY.get(k).push(b);
  }
  const lines = [];
  for (const [y, group] of [...byY.entries()].sort((a, b) => a[0] - b[0])) {
    group.sort((p, q) => p.x - q.x);
    lines.push({
      y,
      x: Math.min(...group.map((g) => g.x)),
      w: Math.max(...group.map((g) => g.x + g.w)) - Math.min(...group.map((g) => g.x)),
      h: Math.max(...group.map((g) => g.h)),
      start: group[0].start,
      length: group.reduce((a, g) => a + g.length, 0),
      text: group.map((g) => g.text).join(' '),
      fragments: group.length,
    });
  }
  return lines;
}

function loadChrome(file) {
  const j = JSON.parse(fs.readFileSync(file, 'utf8'));
  const inLayout = new Map();
  for (const n of j.nodes) inLayout.set(n.domIndex, n);

  const kept = [];
  for (const n of j.nodes) {
    const tag = normTag(n.nodeName);
    if (ELEMENT_SKIP.has(tag)) continue;
    if (tag === '#text' && (!n.text || n.text.trim() === '')) continue;
    // nearest retained ancestor
    let p = n.parentDom;
    let parentKeyId = null;
    while (p !== undefined && p !== null && p >= 0) {
      const pn = inLayout.get(p);
      if (pn) {
        const pt = normTag(pn.nodeName);
        if (!ELEMENT_SKIP.has(pt)) { parentKeyId = pn.domIndex; break; }
        p = pn.parentDom;
      } else break;
    }
    kept.push({
      selfId: n.domIndex, parentKeyId, tag, id: n.id || '',
      x: n.x, y: n.y, w: n.w, h: n.h,
      text: n.text, lines: groupTextBoxesIntoLines(n.lines || []),
    });
  }
  return { meta: j, nodes: assignKeys(kept) };
}

function loadSimple(file) {
  const raw = fs.readFileSync(file, 'utf8');
  const b = raw.indexOf('<<<LAYOUT_DUMP_JSON_BEGIN>>>');
  const e = raw.indexOf('<<<LAYOUT_DUMP_JSON_END>>>');
  if (b < 0 || e < 0) throw new Error('sentinels missing in ' + file);
  const j = JSON.parse(raw.slice(b + '<<<LAYOUT_DUMP_JSON_BEGIN>>>'.length, e));
  const byIndex = new Map();
  for (const n of j.nodes) byIndex.set(n.index, n);

  // Drop head/style/... subtrees entirely.
  const dropped = new Set();
  for (const n of j.nodes) {
    if (ELEMENT_SKIP.has(normTag(n.tag))) dropped.add(n.index);
    else if (n.parent >= 0 && dropped.has(n.parent)) dropped.add(n.index);
  }

  const kept = [];
  for (const n of j.nodes) {
    if (dropped.has(n.index)) continue;
    const tag = normTag(n.tag);
    if (tag === '#text' && (!n.text || n.text.trim() === '')) continue;
    let p = n.parent;
    let parentKeyId = null;
    while (p !== undefined && p !== null && p >= 0) {
      if (!dropped.has(p)) { parentKeyId = p; break; }
      p = byIndex.get(p) ? byIndex.get(p).parent : -1;
    }
    kept.push({
      selfId: n.index, parentKeyId, tag, id: n.id || '',
      x: n.x, y: n.y, w: n.w, h: n.h,
      text: n.text,
      // Simple's wrap_starts/wrap_ends are BYTE offsets into the UTF-8 text
      // (the CJK fixture yields 0..15 / 15..60 for a 20-character string),
      // whereas Chrome's textBoxes start/length are UTF-16 code-unit offsets.
      // Both are resolved to actual substrings here so the comparison is on
      // text, not on incompatible index spaces.
      lines: (n.lines || []).map((l) => ({
        start: l.start, length: l.end - l.start,
        text: Buffer.from(n.text || '', 'utf8').slice(l.start, l.end).toString('utf8'),
      })),
    });
  }
  return { meta: j, nodes: assignKeys(kept) };
}

// Whitespace normalization for line-text comparison: CSS white-space:normal
// collapses runs of whitespace and strips the ends of each line, and the two
// engines disagree about whether the collapsed run is retained in the recorded
// substring. Comparing normalized line text isolates the BREAK POSITIONS,
// which is what the shaper/line-breaker oracle is actually about.
function normLine(s) { return (s || '').replace(/\s+/g, ' ').trim(); }

function diffFixture(name, chrome, simple) {
  const findings = [];
  const cMap = new Map(chrome.nodes.map((n) => [n.key, n]));
  const sMap = new Map(simple.nodes.map((n) => [n.key, n]));
  let compared = 0, lineNodesCompared = 0;

  for (const [k, c] of cMap) {
    if (!sMap.has(k)) {
      findings.push({ fixture: name, key: k, kind: 'UNPAIRED_CHROME_ONLY', delta: Infinity,
        detail: `chrome ${c.tag} @(${c.x},${c.y},${c.w},${c.h}) has no Simple counterpart` });
    }
  }
  for (const [k, s] of sMap) {
    if (!cMap.has(k)) {
      findings.push({ fixture: name, key: k, kind: 'UNPAIRED_SIMPLE_ONLY', delta: Infinity,
        detail: `simple ${s.tag} @(${s.x},${s.y},${s.w},${s.h}) has no Chrome counterpart` });
    }
  }

  for (const [k, c] of cMap) {
    const s = sMap.get(k);
    if (!s) continue;
    compared++;
    // Chrome's #document layout node reports the VIEWPORT rect, not a box
    // produced by layout; Simple's #root reports the document's own extent.
    // Comparing them would be a category error, so #root is paired (its absence
    // is still a failure) but its geometry is recorded as INFO only.
    if (c.tag === '#root') {
      findings.push({ fixture: name, key: k, kind: 'INFO_ROOT_EXTENT', delta: 0,
        detail: `#root: chrome viewport h=${c.h} vs simple document h=${s.h}` });
      continue;
    }
    for (const f of ['x', 'y', 'w', 'h']) {
      const d = s[f] - c[f];
      if (Math.abs(d) > EPS_GEOM) {
        findings.push({ fixture: name, key: k, kind: 'GEOM_' + f.toUpperCase(),
          delta: Math.abs(d), chrome: c[f], simple: s[f], signed: d,
          detail: `${c.tag} ${f}: chrome=${c[f]} simple=${s[f]} delta=${d > 0 ? '+' : ''}${+d.toFixed(4)}` });
      }
    }
    if (c.tag === '#text') {
      lineNodesCompared++;
      const cl = c.lines, sl = s.lines;
      if (cl.length !== sl.length) {
        findings.push({ fixture: name, key: k, kind: 'LINE_COUNT',
          delta: 1000 + Math.abs(cl.length - sl.length),
          chrome: cl.length, simple: sl.length,
          detail: `line count: chrome=${cl.length} simple=${sl.length}` });
      }
      const n = Math.min(cl.length, sl.length);
      for (let i = 0; i < n; i++) {
        const ct = normLine(cl[i].text), st = normLine(sl[i].text);
        if (ct !== st) {
          findings.push({ fixture: name, key: k, kind: 'LINE_BREAK', delta: 900,
            detail: `line ${i}: chrome=${JSON.stringify(ct)} simple=${JSON.stringify(st)}` });
        }
        const dy = (sl[i].y !== undefined && cl[i].y !== undefined) ? null : null;
      }
      // line y positions: only Chrome carries them (Simple has no per-line rect)
      if (cl.length > 1 && sl.length > 1) {
        const cAdv = cl[1].y - cl[0].y;
        findings.push({ fixture: name, key: k, kind: 'INFO_LINE_ADVANCE', delta: 0,
          detail: `chrome line advance=${cAdv}px (Simple emits no per-line rect: line-height not comparable)` });
      }
    }
  }
  return { findings, compared, lineNodesCompared };
}

function main() {
  const root = path.resolve(__dirname, 'out');
  const cDir = path.join(root, 'chrome'), sDir = path.join(root, 'simple');
  if (!fs.existsSync(cDir)) { console.error('FATAL: no chrome output dir — extraction never ran'); process.exit(3); }
  if (!fs.existsSync(sDir)) { console.error('FATAL: no simple output dir — extraction never ran'); process.exit(3); }

  const cFiles = new Map(fs.readdirSync(cDir).filter(f => f.endsWith('.chrome.json'))
    .map(f => [f.replace('.chrome.json', ''), path.join(cDir, f)]));
  const sFiles = new Map(fs.readdirSync(sDir).filter(f => f.endsWith('.simple.json'))
    .map(f => [f.replace('.simple.json', ''), path.join(sDir, f)]));

  const all = [];
  let compared = 0, lineNodes = 0, fixtures = 0;
  const names = new Set([...cFiles.keys(), ...sFiles.keys()]);
  for (const name of [...names].sort()) {
    if (!cFiles.has(name) || !sFiles.has(name)) {
      all.push({ fixture: name, key: '-', kind: 'FIXTURE_MISSING', delta: Infinity,
        detail: `present only in ${cFiles.has(name) ? 'chrome' : 'simple'}` });
      continue;
    }
    fixtures++;
    const r = diffFixture(name, loadChrome(cFiles.get(name)), loadSimple(sFiles.get(name)));
    all.push(...r.findings);
    compared += r.compared; lineNodes += r.lineNodesCompared;
  }

  const real = all.filter(f => !f.kind.startsWith('INFO_'));
  real.sort((a, b) => b.delta - a.delta || a.fixture.localeCompare(b.fixture));

  const report = {
    generated: new Date().toISOString(),
    eps_geom: EPS_GEOM,
    fixtures_compared: fixtures,
    nodes_compared: compared,
    text_nodes_compared: lineNodes,
    findings_total: real.length,
    findings: real,
    info: all.filter(f => f.kind.startsWith('INFO_')),
  };
  fs.writeFileSync(path.join(root, 'report.json'), JSON.stringify(report, null, 1));

  // Flat key=value summary so the SSpec can assert without a JSON parser.
  const kinds = {};
  for (const f of real) kinds[f.kind] = (kinds[f.kind] || 0) + 1;
  const cleanFixtures = [...names].filter(n => !real.some(f => f.fixture === n)).sort();
  const lines = [
    `fixtures_compared=${fixtures}`,
    `nodes_compared=${compared}`,
    `text_nodes_compared=${lineNodes}`,
    `findings_total=${real.length}`,
    `unpaired=${real.filter(f => f.kind.startsWith('UNPAIRED')).length}`,
    `fixtures_missing=${real.filter(f => f.kind === 'FIXTURE_MISSING').length}`,
    `clean_fixtures=${cleanFixtures.join(',')}`,
    `clean_fixture_count=${cleanFixtures.length}`,
    `max_geom_delta=${Math.max(0, ...real.filter(f => f.kind.startsWith('GEOM_')).map(f => f.delta))}`,
  ];
  for (const k of Object.keys(kinds).sort()) lines.push(`kind_${k}=${kinds[k]}`);
  fs.writeFileSync(path.join(root, 'summary.txt'), lines.join('\n') + '\n');

  console.log(`fixtures=${fixtures} nodes_compared=${compared} text_nodes=${lineNodes} findings=${real.length} eps=${EPS_GEOM}`);
  console.log('--- worst first ---');
  for (const f of real) {
    const d = f.delta === Infinity ? 'INF' : String(+f.delta.toFixed(3));
    console.log(`${d.padStart(8)}  ${f.kind.padEnd(22)} ${f.fixture.padEnd(26)} ${f.key.padEnd(30)} ${f.detail}`);
  }

  if (compared === 0) {
    console.error('FATAL: 0 nodes compared — vacuous run, treating as failure');
    process.exit(3);
  }
  process.exit(real.length === 0 ? 0 : 1);
}

main();
