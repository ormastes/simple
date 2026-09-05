#!/usr/bin/env node
// Chrome<->Simple PAINT-stage differ (stage 5).
//
// Reads the two extractor outputs from out/chrome/*.chrome.json and
// out/simple/*.simple.json, lifts both engines' native display lists into the
// canonical paint-op model (CONTRACT.md), and reports per-op divergences.
//
// This is a per-component INPUT/OUTPUT comparison, not a pixel comparison:
//   input  = the same HTML fixture + viewport
//   output = the ordered list of paint operations the engine recorded
//
// Fail-closed rules (a zero-difference report is a red flag, not a pass):
//   * a fixture where either side yielded 0 ops is BLOCKED, never PASS
//   * the summary always states how many ops were compared on EACH side
//   * every finding carries BOTH the chrome value and the simple value

const fs = require('fs');
const path = require('path');

const OUT = path.resolve(__dirname, 'out');
const CHROME_DIR = path.join(OUT, 'chrome');
const SIMPLE_DIR = path.join(OUT, 'simple');

const EPS = 1; // css px; Skia records antialiased half-pixel insets

function hex(u) {
  if (u === null || u === undefined) return 'none';
  return '#' + (u >>> 0).toString(16).padStart(8, '0').toUpperCase();
}

function readJson(p) {
  try { return JSON.parse(fs.readFileSync(p, 'utf8')); } catch (e) { return null; }
}

// ---------------------------------------------------------------------------
// Canonical lift: Simple side.
//
// Simple's DrawIR records ONE command per DOM component carrying the box plus
// its computed style, where Chrome records one Skia op per painted primitive.
// To compare like with like, a Simple component command is expanded into the
// primitive ops it implies: background fill, then border stroke, then outline.
// If the expansion is wrong the divergence shows up as a missing/extra op,
// which is exactly the signal we want.
// ---------------------------------------------------------------------------
function liftSimple(doc) {
  const ops = [];
  for (const batch of doc.batches || []) {
    for (const c of batch.ops || []) {
      const st = c.style || {};
      const num = (k) => {
        const v = parseInt(st[k], 10);
        return Number.isFinite(v) ? v : 0;
      };
      if (c.kind === 'text') {
        ops.push({
          kind: 'text', x: c.x, y: c.y, w: c.w, h: c.h,
          color: c.color >>> 0, id: c.component_id, text: c.text, from: 'text-cmd',
        });
        continue;
      }
      if (c.kind === 'image') {
        ops.push({ kind: 'image', x: c.x, y: c.y, w: c.w, h: c.h, color: null, id: c.component_id, from: 'image-cmd' });
        continue;
      }
      // rect-ish component command
      const bg = c.color >>> 0;
      const bw = { t: num('border-top-width'), r: num('border-right-width'), b: num('border-bottom-width'), l: num('border-left-width') };
      const radius = num('border-top-left-radius');
      const hasBorder = bw.t > 0 || bw.r > 0 || bw.b > 0 || bw.l > 0;
      if ((bg >>> 24) !== 0) {
        ops.push({
          kind: radius > 0 ? 'fill_rrect' : 'fill_rect',
          x: c.x, y: c.y, w: c.w, h: c.h, color: bg, radius,
          id: c.component_id, from: 'background-color',
        });
      } else {
        ops.push({
          kind: 'nofill', x: c.x, y: c.y, w: c.w, h: c.h, color: bg,
          id: c.component_id, from: 'background-color:transparent',
        });
      }
      if (hasBorder) {
        ops.push({
          kind: 'stroke_rect', x: c.x, y: c.y, w: c.w, h: c.h,
          color: num('border-top-color') >>> 0,
          stroke_width: bw.t || bw.l || bw.r || bw.b,
          border_widths: bw, id: c.component_id, from: 'border-*-width (SYNTHESISED from style, not an emitted op)',
          synthesised: true,
        });
      }
      if (num('outline-width') > 0) {
        ops.push({
          kind: 'stroke_rect', x: c.x, y: c.y, w: c.w, h: c.h,
          color: num('outline-color') >>> 0, stroke_width: num('outline-width'),
          id: c.component_id, from: 'outline-width (SYNTHESISED)', synthesised: true,
        });
      }
    }
  }
  return ops;
}

// ---------------------------------------------------------------------------
// Canonical lift: Chrome side. Flatten every layer's ops in paint order.
// ---------------------------------------------------------------------------
function liftChrome(doc) {
  const ops = [];
  for (const l of doc.layers || []) {
    for (const o of l.ops || []) ops.push({ ...o, layer: l.layer_id });
  }
  return ops;
}

const near = (a, b) => a !== null && b !== null && Math.abs(a - b) <= EPS;
function rectNear(a, b) {
  return near(a.x, b.x) && near(a.y, b.y) && near(a.w, b.w) && near(a.h, b.h);
}

// A Chrome border stroke is recorded on the rect INSET by half the stroke
// width; Simple's synthesised border uses the border-box. Compare on the
// border-box by re-inflating Chrome's stroke rect.
function chromeStrokeBorderBox(o) {
  const h = (o.stroke_width || 0) / 2;
  return { x: Math.round(o.x - h), y: Math.round(o.y - h), w: Math.round(o.w + 2 * h), h: Math.round(o.h + 2 * h) };
}

function diffFixture(name, chromeDoc, simpleDoc) {
  const cOps = liftChrome(chromeDoc);
  const sOps = liftSimple(simpleDoc);
  const findings = [];

  const cFills = cOps.filter((o) => o.kind === 'fill_rect' || o.kind === 'fill_rrect');
  const cStrokes = cOps.filter((o) => o.kind === 'stroke_rect' || o.kind === 'stroke_rrect');
  const cTexts = cOps.filter((o) => o.kind === 'text');
  const cCanvas = cOps.filter((o) => o.kind === 'canvas_fill');

  const sFills = sOps.filter((o) => o.kind === 'fill_rect' || o.kind === 'fill_rrect');
  const sStrokes = sOps.filter((o) => o.kind === 'stroke_rect');
  const sTexts = sOps.filter((o) => o.kind === 'text');
  const sNofill = sOps.filter((o) => o.kind === 'nofill');

  const add = (severity, category, detail, chromeVal, simpleVal) =>
    findings.push({ fixture: name, severity, category, detail, chrome: chromeVal, simple: simpleVal });

  // --- (1) op-count shape -------------------------------------------------
  if (cFills.length !== sFills.length) {
    add('info', 'fill-op-count',
      'number of background fill ops recorded',
      cFills.length + ' fill op(s)', sFills.length + ' fill op(s)');
  }

  // --- (2) background fills: geometry + colour ----------------------------
  const usedC = new Set();
  for (const s of sFills) {
    let hit = -1;
    for (let i = 0; i < cFills.length; i++) {
      if (usedC.has(i)) continue;
      if (rectNear(cFills[i], s)) { hit = i; break; }
    }
    if (hit < 0) {
      // try colour-only match to distinguish "wrong geometry" from "absent"
      const byColor = cFills.find((c, i) => !usedC.has(i) && (c.color >>> 0) === (s.color >>> 0));
      add('major', 'fill-missing',
        'component "' + s.id + '" background fill has no geometry-matching Chrome op',
        byColor ? ('same colour ' + hex(byColor.color) + ' at ' + fmtRect(byColor)) : 'no fill op at ' + fmtRect(s),
        hex(s.color) + ' at ' + fmtRect(s));
      continue;
    }
    usedC.add(hit);
    const c = cFills[hit];
    if ((c.color >>> 0) !== (s.color >>> 0)) {
      add('major', 'fill-color', 'component "' + s.id + '" background fill colour at ' + fmtRect(s),
        hex(c.color), hex(s.color));
    }
    if (c.kind !== s.kind) {
      add('minor', 'fill-shape', 'component "' + s.id + '" fill primitive at ' + fmtRect(s),
        c.kind, s.kind);
    }
  }
  for (let i = 0; i < cFills.length; i++) {
    if (usedC.has(i)) continue;
    const c = cFills[i];
    // A Chrome fill Simple never recorded. Was it the viewport base fill?
    add('major', 'fill-extra',
      'Chrome recorded a fill op Simple has no counterpart for',
      hex(c.color) + ' at ' + fmtRect(c),
      'no fill op with that geometry (' + sNofill.length + ' transparent component(s) recorded instead)');
  }

  // --- (3) borders --------------------------------------------------------
  const usedS = new Set();
  for (const c of cStrokes) {
    const box = chromeStrokeBorderBox(c);
    let hit = -1;
    for (let i = 0; i < sStrokes.length; i++) {
      if (usedS.has(i)) continue;
      if (rectNear(sStrokes[i], box)) { hit = i; break; }
    }
    if (hit < 0) {
      add('major', 'border-missing',
        'Chrome painted a border stroke with no Simple counterpart',
        hex(c.color) + ' width=' + c.stroke_width + ' border-box ' + fmtRect(box),
        'none');
      continue;
    }
    usedS.add(hit);
    const s = sStrokes[hit];
    if ((c.color >>> 0) !== (s.color >>> 0)) {
      add('major', 'border-color', 'border stroke colour on "' + s.id + '"', hex(c.color), hex(s.color));
    }
    if ((c.stroke_width || 0) !== (s.stroke_width || 0)) {
      add('major', 'border-width', 'border stroke width on "' + s.id + '"',
        String(c.stroke_width), String(s.stroke_width));
    }
    if (s.synthesised) {
      add('major', 'border-not-an-op',
        'component "' + s.id + '" border exists only as computed-style properties in Simple\'s DrawIR; Chrome records it as its own paint op',
        'drawRect style=Stroke width=' + c.stroke_width + ' colour=' + hex(c.color),
        'no border command; border-*-width=' + JSON.stringify(s.border_widths) + ' colour=' + hex(s.color) + ' carried on the rect command instead');
    }
  }
  for (let i = 0; i < sStrokes.length; i++) {
    if (usedS.has(i)) continue;
    const s = sStrokes[i];
    add('major', 'border-extra', 'Simple implies a border stroke Chrome did not paint',
      'none', hex(s.color) + ' width=' + s.stroke_width + ' at ' + fmtRect(s));
  }

  // --- (4) text runs ------------------------------------------------------
  if (cTexts.length !== sTexts.length) {
    add('major', 'text-run-count', 'number of text paint ops',
      cTexts.length + ' drawTextBlob', sTexts.length + ' text command(s)');
  }
  const n = Math.min(cTexts.length, sTexts.length);
  for (let i = 0; i < n; i++) {
    const c = cTexts[i], s = sTexts[i];
    if ((c.color >>> 0) !== (s.color >>> 0)) {
      add('major', 'text-color', 'text run #' + i + ' ("' + (s.text || '') + '") fill colour', hex(c.color), hex(s.color));
    }
    if (!near(c.x, s.x)) {
      add('major', 'text-origin-x', 'text run #' + i + ' ("' + (s.text || '') + '") x origin',
        String(c.x), String(s.x));
    }
    // Chrome's y is the BASELINE; Simple's y is the run's top. Report both raw
    // so the reader can judge the implied ascent rather than asserting one.
    const implied = c.y - s.y;
    if (implied < 0 || implied > 24) {
      add('minor', 'text-baseline', 'text run #' + i + ' vertical origin (chrome=baseline, simple=top; implied ascent ' + implied + 'px)',
        'baseline y=' + c.y, 'top y=' + s.y);
    }
  }

  // --- (5) canvas base ----------------------------------------------------
  if (cCanvas.length > 0 && sFills.length > 0) {
    const cBase = cFills.find((o) => o.w >= (chromeDoc.viewport.w - 1)) || null;
    const sBase = sFills.find((o) => o.id === 'html-canvas') || null;
    if (cBase && sBase && (cBase.color >>> 0) !== (sBase.color >>> 0)) {
      add('major', 'canvas-base-color', 'viewport base fill colour', hex(cBase.color), hex(sBase.color));
    }
  }

  return {
    fixture: name,
    chrome_ops: cOps.length, simple_ops: sOps.length,
    chrome_fills: cFills.length, simple_fills: sFills.length,
    chrome_strokes: cStrokes.length, simple_strokes: sStrokes.length,
    chrome_texts: cTexts.length, simple_texts: sTexts.length,
    findings,
  };
}

function fmtRect(o) { return '(' + o.x + ',' + o.y + ' ' + o.w + 'x' + o.h + ')'; }

function main() {
  if (!fs.existsSync(CHROME_DIR) || !fs.existsSync(SIMPLE_DIR)) {
    console.error('paint-diff verdict: ERROR — nothing was compared (missing ' + CHROME_DIR + ' or ' + SIMPLE_DIR + ')');
    process.exit(2);
  }
  const chromeFiles = fs.readdirSync(CHROME_DIR).filter((f) => f.endsWith('.chrome.json')).sort();
  const results = [];
  const blocked = [];

  for (const cf of chromeFiles) {
    const name = cf.replace(/\.chrome\.json$/, '');
    const cDoc = readJson(path.join(CHROME_DIR, cf));
    const sDoc = readJson(path.join(SIMPLE_DIR, name + '.simple.json'));
    if (!cDoc) { blocked.push(name + ': chrome extraction unreadable'); continue; }
    if (!sDoc) { blocked.push(name + ': simple extraction missing/unreadable'); continue; }
    const r = diffFixture(name, cDoc, sDoc);
    if (r.chrome_ops === 0) { blocked.push(name + ': chrome produced 0 paint ops'); continue; }
    if (r.simple_ops === 0) { blocked.push(name + ': simple produced 0 paint ops'); continue; }
    results.push(r);
  }

  const totC = results.reduce((a, r) => a + r.chrome_ops, 0);
  const totS = results.reduce((a, r) => a + r.simple_ops, 0);
  const allFindings = results.flatMap((r) => r.findings);

  const report = {
    stage: 'paint / display list',
    chrome_source: 'LayerTree.snapshotCommandLog (recorded SkPicture)',
    simple_source: 'simple_web_layout_render_html_draw_ir -> DrawIrComposition',
    fixtures_compared: results.length,
    fixtures_blocked: blocked,
    chrome_paint_ops: totC,
    simple_paint_ops: totS,
    chrome_fill_ops: results.reduce((a, r) => a + r.chrome_fills, 0),
    simple_fill_ops: results.reduce((a, r) => a + r.simple_fills, 0),
    chrome_stroke_ops: results.reduce((a, r) => a + r.chrome_strokes, 0),
    simple_stroke_ops: results.reduce((a, r) => a + r.simple_strokes, 0),
    chrome_text_ops: results.reduce((a, r) => a + r.chrome_texts, 0),
    simple_text_ops: results.reduce((a, r) => a + r.simple_texts, 0),
    finding_count: allFindings.length,
    by_category: allFindings.reduce((m, f) => { m[f.category] = (m[f.category] || 0) + 1; return m; }, {}),
    per_fixture: results.map((r) => ({
      fixture: r.fixture, chrome_ops: r.chrome_ops, simple_ops: r.simple_ops, findings: r.findings.length,
    })),
    findings: allFindings,
  };
  fs.writeFileSync(path.join(OUT, 'paint_report.json'), JSON.stringify(report, null, 1));

  // Flat key=value summary, so the system spec can gate on it without a JSON
  // parser. Absent keys read as -1 on the spec side and FAIL rather than pass.
  const clean = results.filter((r) => r.findings.length === 0).map((r) => r.fixture);
  const summary = [
    'stage=paint',
    'fixtures_compared=' + results.length,
    'fixtures_blocked=' + blocked.length,
    'chrome_ops_compared=' + totC,
    'simple_ops_compared=' + totS,
    'chrome_fill_ops=' + report.chrome_fill_ops,
    'simple_fill_ops=' + report.simple_fill_ops,
    'chrome_stroke_ops=' + report.chrome_stroke_ops,
    'simple_stroke_ops=' + report.simple_stroke_ops,
    'chrome_text_ops=' + report.chrome_text_ops,
    'simple_text_ops=' + report.simple_text_ops,
    'findings_total=' + allFindings.length,
    'clean_fixtures=' + clean.join(','),
  ].join('\n') + '\n';
  fs.writeFileSync(path.join(OUT, 'summary.txt'), summary);

  console.log('');
  console.log('=== paint-stage differential ===');
  console.log('fixtures compared : ' + results.length + (blocked.length ? ('  (BLOCKED: ' + blocked.length + ')') : ''));
  for (const b of blocked) console.log('  BLOCKED ' + b);
  console.log('chrome paint ops  : ' + totC + '  (fill ' + report.chrome_fill_ops + ', stroke ' + report.chrome_stroke_ops + ', text ' + report.chrome_text_ops + ')');
  console.log('simple paint ops  : ' + totS + '  (fill ' + report.simple_fill_ops + ', stroke ' + report.simple_stroke_ops + ', text ' + report.simple_text_ops + ')');
  console.log('findings          : ' + allFindings.length);
  for (const [k, v] of Object.entries(report.by_category).sort((a, b) => b[1] - a[1])) {
    console.log('  ' + String(v).padStart(4) + '  ' + k);
  }
  console.log('');
  for (const f of allFindings.slice(0, 40)) {
    console.log('[' + f.severity + '] ' + f.fixture + ' / ' + f.category);
    console.log('    ' + f.detail);
    console.log('    chrome: ' + f.chrome);
    console.log('    simple: ' + f.simple);
  }
  if (allFindings.length > 40) console.log('... ' + (allFindings.length - 40) + ' more in out/paint_report.json');
  console.log('');

  // Verdict. A zero-op run is never a pass.
  if (results.length === 0 || totC === 0 || totS === 0) {
    console.log('paint-diff verdict: ERROR — nothing was compared');
    process.exit(2);
  }
  console.log('paint-diff verdict: PASS — ' + results.length + ' fixture(s), '
    + totC + ' chrome op(s) vs ' + totS + ' simple op(s) compared, '
    + allFindings.length + ' divergence(s) recorded');
  process.exit(0);
}

main();
