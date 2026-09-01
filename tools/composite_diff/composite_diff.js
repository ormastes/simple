#!/usr/bin/env node
// Chrome<->Simple COMPOSITING/LAYERIZATION differ (stage 6).
//
// Reads the two extractor outputs from out/chrome/*.chrome.json and
// out/simple/*.simple.json, lifts both engines' native output into the
// canonical compositing model (CONTRACT.md), and reports divergences.
//
// This is a per-component INPUT/OUTPUT comparison, not a pixel comparison:
//   input  = the same HTML fixture + viewport
//   output = the set of independently-composited units the engine decided on,
//            plus the named reason it decided so
//
// Fail-closed rules (a zero-difference report is a red flag, not a pass):
//   * a fixture where either side yielded 0 compositing units is BLOCKED
//   * the summary always states how many units were compared on EACH side
//   * every finding carries BOTH the chrome value and the simple value

const fs = require('fs');
const path = require('path');

const OUT = path.resolve(__dirname, 'out');
const CHROME_DIR = path.join(OUT, 'chrome');
const SIMPLE_DIR = path.join(OUT, 'simple');

const EPS = 1; // css px

// Which CSS property drives each of Chrome's named compositing reasons. Used to
// ask the second, more actionable question: not just "did Simple promote?" but
// "does the property that WOULD drive the promotion even survive into Simple's
// Draw IR?". `null` means the reason is induced by other layers' geometry
// rather than by a property on the element itself.
const REASON_TRIGGER = {
  WillChangeTransform: 'will-change',
  WillChangeOpacity: 'will-change',
  WillChangeFilter: 'will-change',
  WillChangeBackdropFilter: 'will-change',
  '3DTransform': 'transform',
  Transform3DSceneLeaf: 'transform',
  Preserve3DWith3DDescendants: 'transform-style',
  BackfaceVisibilityHidden: 'backface-visibility',
  ActiveOpacityAnimation: 'animation-name',
  ActiveTransformAnimation: 'animation-name',
  ActiveFilterAnimation: 'animation-name',
  ActiveBackdropFilterAnimation: 'animation-name',
  OverflowScrolling: 'overflow-y',
  BackdropFilter: 'backdrop-filter',
  Overlap: null,
  RootScroller: null,
  Viewport: null,
};

function readJson(p) {
  try { return JSON.parse(fs.readFileSync(p, 'utf8')); } catch (e) { return null; }
}

const near = (a, b) => Math.abs(a - b) <= EPS;
function fmtBox(o) { return o.w + 'x' + o.h; }
function fmtRect(o) { return '(' + o.x + ',' + o.y + ' ' + o.w + 'x' + o.h + ')'; }

// ---------------------------------------------------------------------------
// Canonical lift: Simple side.
//
// Simple's compositing unit is the DrawIrBatch -- the granularity at which the
// Draw IR hands work to a backend. Every component command inside a batch is
// composited together with its siblings; there is no per-element promotion.
// ---------------------------------------------------------------------------
function liftSimple(doc) {
  const units = [];
  const components = [];
  for (const b of doc.batches || []) {
    units.push({ id: b.batch_id, backend: b.backend_target, count: (b.components || []).length });
    for (const c of b.components || []) components.push({ ...c, batch: b.batch_id });
  }
  return { units, components };
}

function liftChrome(doc) {
  const all = doc.layers || [];
  return {
    all,
    scaffold: all.filter((l) => l.role !== 'element'),
    elements: all.filter((l) => l.role === 'element'),
  };
}

function diffFixture(name, chromeDoc, simpleDoc) {
  const C = liftChrome(chromeDoc);
  const S = liftSimple(simpleDoc);
  const findings = [];
  const add = (severity, category, detail, chromeVal, simpleVal) =>
    findings.push({ fixture: name, severity, category, detail, chrome: chromeVal, simple: simpleVal });

  // --- (1) compositing-unit count ----------------------------------------
  // Simple's batch count is its layer count. Chrome's element promotions are
  // the layers Simple would need to have produced beyond its single root unit.
  if (C.elements.length > 0 && S.units.length <= 1) {
    add('major', 'no-layerization',
      'Chrome split this document into independently-composited layers; Simple emitted a single undifferentiated unit',
      C.all.length + ' layer(s) total, ' + C.elements.length + ' element promotion(s): '
        + C.elements.map((e) => fmtBox(e) + ' [' + (e.compositing_reasons.join('+') || 'no-reason') + ']').join(', '),
      S.units.length + ' batch(es): ' + S.units.map((u) => u.id + '[' + u.backend + ']x' + u.count).join(', '));
  } else if (C.elements.length === 0 && S.units.length === 1) {
    // Genuine agreement: neither engine promoted anything. Recorded as no
    // finding, which is what keeps this differential from being tautological.
  } else if (C.elements.length !== S.units.length - 1) {
    add('major', 'unit-count',
      'number of independently-composited units',
      C.elements.length + ' element layer(s) above the root scaffolding',
      (S.units.length - 1) + ' batch(es) above the first');
  }

  // --- (2) per-promotion: did Simple produce a counterpart? ---------------
  // Chrome reports every element layer at offset 0,0 -- a promoted layer gets
  // its own transform-node origin, so the offset carries no page position. The
  // match is therefore on layer SIZE, and page position is not compared here
  // (tools/layout_diff already gates box positions).
  const used = new Set();
  for (const l of C.elements) {
    let hit = -1;
    for (let i = 0; i < S.components.length; i++) {
      if (used.has(i)) continue;
      if (near(S.components[i].w, l.w) && near(S.components[i].h, l.h)) { hit = i; break; }
    }
    const reasons = l.compositing_reasons.length ? l.compositing_reasons.join('+') : 'no-reason';
    if (hit < 0) {
      add('major', 'promoted-box-absent',
        'Chrome promoted a ' + fmtBox(l) + ' layer that has no Simple component of that size at all',
        'layer ' + l.layer_id + ' ' + fmtBox(l) + ' draws=' + l.draws_content + ' [' + reasons + ']',
        'no component with size ' + fmtBox(l) + ' in ' + S.components.length + ' component(s)');
      continue;
    }
    used.add(hit);
    const c = S.components[hit];

    // (2a) the promotion itself
    add('major', 'promotion-missing',
      'component "' + c.component_id + '" is its own composited layer in Chrome; in Simple it is an ordinary command inside the shared batch',
      'layer ' + l.layer_id + ' ' + fmtBox(l) + ' draws=' + l.draws_content + ' reasons=[' + reasons + ']',
      'command "' + c.component_id + '" ' + fmtRect(c) + ' in batch "' + c.batch + '" (no independent unit)');

    // (2b) does the triggering property even reach Simple's Draw IR?
    for (const r of l.compositing_reasons) {
      const prop = REASON_TRIGGER[r];
      if (prop === null) continue;      // geometry-induced, no property to check
      if (prop === undefined) {
        add('minor', 'reason-unmapped',
          'Chrome compositing reason "' + r + '" is not mapped to a triggering CSS property in this differ',
          r, 'not checked');
        continue;
      }
      const have = Object.prototype.hasOwnProperty.call(c.triggers, prop);
      if (!have) {
        add('major', 'trigger-property-absent',
          'the property driving Chrome\'s "' + r + '" promotion of "' + c.component_id + '" is not carried in Simple\'s Draw IR at all',
          r + ' (driven by CSS `' + prop + '`)',
          '`' + prop + '` absent; component carries ' + Object.keys(c.triggers).length
            + ' trigger prop(s): ' + (Object.keys(c.triggers).join(', ') || 'none'));
      } else {
        add('major', 'trigger-property-inert',
          'Simple carries the property driving Chrome\'s "' + r + '" promotion of "' + c.component_id + '" but nothing acts on it',
          r + ' (driven by CSS `' + prop + '`)',
          '`' + prop + '` = "' + c.triggers[prop] + '" present in Draw IR, no layerization consumes it');
      }
    }

    // (2c) structural attributes Simple has no representation for
    if (l.transform && l.transform.has_3d) {
      add('major', 'layer-transform-absent',
        'Chrome carries a 3D transform on the layer; Simple\'s Draw IR command has no transform field',
        'layer transform matrix with 3D component: [' + l.transform.matrix.join(',') + ']',
        'no transform on command "' + c.component_id + '"; `transform` absent from computed style');
    }
    if (l.sticky) {
      add('major', 'sticky-constraint-absent',
        'Chrome attaches a sticky-position constraint to the layer; Simple has no sticky constraint concept',
        'stickyBoxRect ' + fmtRect(l.sticky),
        'none on "' + c.component_id + '"');
    }
    if (l.scroll_rects && l.scroll_rects.length > 0) {
      add('minor', 'scroll-rects-absent',
        'Chrome records scroll rects on the layer; Simple records none',
        JSON.stringify(l.scroll_rects), 'none');
    }
  }

  // --- (3) scaffolding sanity --------------------------------------------
  // Chrome's four root layers should be present on every fixture. If they are
  // not, the classifier drifted and every count above is suspect.
  if (C.scaffold.length < 3) {
    add('major', 'scaffold-shape',
      'Chrome root scaffolding layer count is not the expected 4; the layer classifier may be misreading this build',
      C.scaffold.length + ' scaffolding layer(s): ' + C.scaffold.map((s) => s.role).join(', '),
      'n/a (Simple has no scaffolding layers)');
  }

  return {
    fixture: name,
    chrome_layers: C.all.length,
    chrome_element_layers: C.elements.length,
    chrome_scaffold_layers: C.scaffold.length,
    simple_units: S.units.length,
    simple_components: S.components.length,
    findings,
  };
}

function main() {
  if (!fs.existsSync(CHROME_DIR) || !fs.existsSync(SIMPLE_DIR)) {
    console.error('composite-diff verdict: ERROR — nothing was compared (missing '
      + CHROME_DIR + ' or ' + SIMPLE_DIR + ')');
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
    if (r.chrome_layers === 0) { blocked.push(name + ': chrome produced 0 layers'); continue; }
    if (r.simple_units === 0) { blocked.push(name + ': simple produced 0 compositing units'); continue; }
    if (r.simple_components === 0) { blocked.push(name + ': simple produced 0 components'); continue; }
    results.push(r);
  }
  if (chromeFiles.length === 0) blocked.push('no chrome extractions found at all');

  const totCL = results.reduce((a, r) => a + r.chrome_layers, 0);
  const totCE = results.reduce((a, r) => a + r.chrome_element_layers, 0);
  const totSU = results.reduce((a, r) => a + r.simple_units, 0);
  const totSC = results.reduce((a, r) => a + r.simple_components, 0);
  const allFindings = results.flatMap((r) => r.findings);

  // How many distinct promotion reasons the fixture set actually exercised. If
  // this is small the fixture set is not testing compositing, and the whole
  // report is weak evidence regardless of the finding count.
  const reasonsSeen = new Set();
  for (const cf of chromeFiles) {
    const d = readJson(path.join(CHROME_DIR, cf));
    if (!d) continue;
    for (const l of d.layers || []) if (l.role === 'element') for (const r of l.compositing_reasons) reasonsSeen.add(r);
  }

  const report = {
    stage: 'compositing / layerization',
    chrome_source: 'LayerTree.layerTreeDidChange + LayerTree.compositingReasons',
    simple_source: 'simple_web_layout_render_html_draw_ir -> DrawIrComposition batches',
    fixtures_compared: results.length,
    fixtures_blocked: blocked,
    chrome_layers: totCL,
    chrome_element_layers: totCE,
    simple_units: totSU,
    simple_components: totSC,
    distinct_compositing_reasons: [...reasonsSeen].sort(),
    finding_count: allFindings.length,
    by_category: allFindings.reduce((m, f) => { m[f.category] = (m[f.category] || 0) + 1; return m; }, {}),
    per_fixture: results.map((r) => ({
      fixture: r.fixture, chrome_layers: r.chrome_layers,
      chrome_element_layers: r.chrome_element_layers,
      simple_units: r.simple_units, findings: r.findings.length,
    })),
    findings: allFindings,
  };
  fs.writeFileSync(path.join(OUT, 'composite_report.json'), JSON.stringify(report, null, 1));

  // Flat key=value summary so the system spec can gate on it without a JSON
  // parser. Absent keys read as -1 on the spec side and FAIL rather than pass.
  const clean = results.filter((r) => r.findings.length === 0).map((r) => r.fixture);
  const summary = [
    'stage=compositing',
    'fixtures_compared=' + results.length,
    'fixtures_blocked=' + blocked.length,
    'chrome_layers_compared=' + totCL,
    'chrome_element_layers=' + totCE,
    'simple_units_compared=' + totSU,
    'simple_components_compared=' + totSC,
    'distinct_compositing_reasons=' + reasonsSeen.size,
    'findings_total=' + allFindings.length,
    'promotion_missing=' + (report.by_category['promotion-missing'] || 0),
    'trigger_property_absent=' + (report.by_category['trigger-property-absent'] || 0),
    'trigger_property_inert=' + (report.by_category['trigger-property-inert'] || 0),
    'clean_fixtures=' + clean.join(','),
  ].join('\n') + '\n';
  fs.writeFileSync(path.join(OUT, 'summary.txt'), summary);

  console.log('');
  console.log('=== compositing-stage differential ===');
  console.log('fixtures compared    : ' + results.length + (blocked.length ? ('  (BLOCKED: ' + blocked.length + ')') : ''));
  for (const b of blocked) console.log('  BLOCKED ' + b);
  console.log('chrome layers        : ' + totCL + '  (' + totCE + ' element promotions, '
    + (totCL - totCE) + ' root scaffolding)');
  console.log('simple units         : ' + totSU + '  (' + totSC + ' components)');
  console.log('promotion reasons    : ' + reasonsSeen.size + '  [' + [...reasonsSeen].sort().join(', ') + ']');
  console.log('findings             : ' + allFindings.length);
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
  if (allFindings.length > 40) console.log('... ' + (allFindings.length - 40) + ' more in out/composite_report.json');
  console.log('');

  // Verdict. A run that compared nothing is never a pass.
  if (results.length === 0 || totCL === 0 || totSU === 0) {
    console.log('composite-diff verdict: ERROR — nothing was compared');
    process.exit(2);
  }
  // A fixture set in which Chrome promoted nothing cannot test layerization.
  if (totCE === 0) {
    console.log('composite-diff verdict: ERROR — chrome promoted 0 elements; the promotion oracle is vacuous');
    process.exit(2);
  }
  console.log('composite-diff verdict: PASS — ' + results.length + ' fixture(s), '
    + totCL + ' chrome layer(s) (' + totCE + ' promotions) vs ' + totSU
    + ' simple unit(s) (' + totSC + ' components) compared, '
    + allFindings.length + ' divergence(s) recorded');
  process.exit(0);
}

main();
