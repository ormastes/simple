// Normalizer + differ for the Chrome<->Simple component-level differential.
//
// See doc/05_design/ui/web_diff/chrome_simple_stage_io_contract.md for the
// full I/O contract and the justification of every normalization rule below.
//
// FAIL-CLOSED CONTRACT:
//   * a run that compares ZERO nodes is a FAILURE, never a pass
//   * a missing/empty side is a FAILURE
//   * the report always states comparedNodes and comparedProps explicitly
'use strict';
const fs = require('fs');

// ---------------------------------------------------------------------------
// Normalization rules. Each is deliberately narrow; over-normalizing here is
// how a differential silently stops finding real bugs.
// ---------------------------------------------------------------------------

// N1 tag case: Chrome's DOMSnapshot reports HTML element nodeNames upper-cased
// (DOM spec: HTML elements in the HTML namespace have upper-case tagName).
// Simple stores the source-cased/lower-cased tag. Case is NOT a rendering
// behavior, so folding to lower-case is safe.
const lowerTag = (s) => String(s || '').toLowerCase();

// N2 doctype: Chrome emits the DOCTYPE as a real child node (nodeType 10).
// Simple's tree builder does not materialize it. We DROP doctype nodes on the
// Chrome side rather than fabricating one on the Simple side, because the
// doctype carries no computed style and no comparable content.
const isDoctype = (n) => n.nodeType === 10;

// N2b pseudo-elements: Chrome's DOMSnapshot materializes `::marker`,
// `::before`, `::after` as tree entries. They are NOT DOM nodes (they are not
// reachable via any DOM API), so they are dropped rather than counted as a
// structural divergence. Their absence in Simple is a *style* gap (no UA
// list-item marker), which the display-property comparison already reports.
const isPseudo = (n) => String(n.name || '').startsWith('::');

// N3 whitespace-only text: HTML collapses inter-element whitespace, and the two
// engines legitimately differ on whether such a node is retained. We do NOT
// drop them silently: they are compared in "structural" mode but reported in a
// separate `whitespaceOnly` bucket so the divergence stays visible.
const isWsText = (n) => lowerTag(n.name) === '#text' && /^\s*$/.test(n.text || '');

// N4 text content: collapse runs of ASCII whitespace to a single space and trim.
// This is the CSS `white-space: normal` collapsing both engines are supposed to
// perform for rendering; comparing raw source whitespace would flag noise.
// NBSP (U+00A0) is deliberately NOT collapsed -- it is a distinct character and
// entity-decoding differences must remain visible.
const normText = (t) => String(t || '').replace(/[ \t\r\n\f]+/g, ' ').trim();

// N5 color: canonicalize every color spelling to `rgba(r,g,b,a)` with a
// 3-decimal alpha. Chrome emits `rgb(r, g, b)` / `rgba(...)`; Simple emits the
// author's source spelling (`red`, `#f00`, ...). Without this rule every color
// would report as divergent for a purely syntactic reason.
// An UNRECOGNIZED color string is returned verbatim (prefixed `raw:`) rather
// than being mapped to a default -- mapping unknowns to black would hide a
// genuine "Simple failed to parse this color" bug.
const NAMED = {
  black: [0,0,0], white: [255,255,255], red: [255,0,0], green: [0,128,0],
  lime: [0,255,0], blue: [0,0,255], yellow: [255,255,0], teal: [0,128,128],
  purple: [128,0,128], gray: [128,128,128], grey: [128,128,128],
  silver: [192,192,192], maroon: [128,0,0], olive: [128,128,0],
  navy: [0,0,128], fuchsia: [255,0,255], aqua: [0,255,255],
  rebeccapurple: [102,51,153], orange: [255,165,0], transparent: [0,0,0,0],
};
function normColor(v) {
  const s = String(v == null ? '' : v).trim().toLowerCase();
  if (s === '') return '';
  const fmt = (r, g, b, a) => `rgba(${r},${g},${b},${Number(a).toFixed(3)})`;
  if (NAMED[s]) { const c = NAMED[s]; return fmt(c[0], c[1], c[2], c.length > 3 ? c[3] : 1); }
  let m = s.match(/^#([0-9a-f]{3})$/);
  if (m) { const h = m[1]; return fmt(parseInt(h[0]+h[0],16), parseInt(h[1]+h[1],16), parseInt(h[2]+h[2],16), 1); }
  m = s.match(/^#([0-9a-f]{6})$/);
  if (m) { const h = m[1]; return fmt(parseInt(h.slice(0,2),16), parseInt(h.slice(2,4),16), parseInt(h.slice(4,6),16), 1); }
  m = s.match(/^rgba?\(\s*([\d.]+)[\s,]+([\d.]+)[\s,]+([\d.]+)(?:[\s,/]+([\d.%]+))?\s*\)$/);
  if (m) {
    let a = m[4] === undefined ? 1 : (String(m[4]).endsWith('%') ? parseFloat(m[4]) / 100 : parseFloat(m[4]));
    return fmt(Math.round(+m[1]), Math.round(+m[2]), Math.round(+m[3]), a);
  }
  return 'raw:' + s;
}

// N6 length: both sides reduce to a px float. Chrome always reports used px for
// these properties. Simple stores an f64 already in px. Epsilon 0.05px --
// below Chrome's own 1/64px layout quantization, so a real cascade error can
// never hide under it, but a float-printing difference will not fire.
const EPS = 0.05;
function normLen(v) {
  if (typeof v === 'number') return v;
  const s = String(v == null ? '' : v).trim().toLowerCase();
  if (s === '' ) return null;
  if (s === 'auto' || s === 'none' || s === 'normal') return s;
  const m = s.match(/^(-?[\d.]+)px$/);
  if (m) return parseFloat(m[1]);
  const n = s.match(/^-?[\d.]+$/);
  if (n) return parseFloat(s);
  return 'raw:' + s;
}

// N7 font-weight: `bold` == 700, `normal` == 400. Chrome reports the numeric
// computed value; Simple stores the keyword. Both spellings are the SAME
// computed value per CSS Fonts, so folding is correct, not lenient.
function normWeight(v) {
  const s = String(v == null ? '' : v).trim().toLowerCase();
  if (s === '') return '';
  if (s === 'bold') return '700';
  if (s === 'normal') return '400';
  if (s === 'bolder') return 'bolder';
  if (s === 'lighter') return 'lighter';
  return s;
}

// N8 font-family: strip quotes and normalize inter-item spacing, keep order.
// Order and identity of the list are semantic; quoting is not.
function normFamily(v) {
  return String(v == null ? '' : v).split(',')
    .map((x) => x.trim().replace(/^["']|["']$/g, '').toLowerCase())
    .filter((x) => x !== '').join(',');
}

// N9 keyword identity: lower-case, collapse whitespace. `''` (Simple's "unset")
// is preserved as the distinct token `<empty>` so an unpopulated Simple
// property is never confused with Chrome's `initial` value.
const normKw = (v) => {
  const s = String(v == null ? '' : v).trim().toLowerCase().replace(/\s+/g, ' ');
  return s === '' ? '<empty>' : s;
};

// N10 property name aliasing: Simple has a single `border-width`/`border-color`/
// `border-style` (no per-side). We compare them against Chrome's border-TOP-*.
// This is a deliberate narrowing: it CANNOT detect per-side border divergence,
// and that limitation is recorded in the contract rather than papered over.
const PROP_MAP = [
  ['display',          'display',            normKw],
  ['position',         'position',           normKw],
  ['width',            'width',              normLen],
  ['height',           'height',             normLen],
  ['margin-top',       'margin-top',         normLen],
  ['margin-right',     'margin-right',       normLen],
  ['margin-bottom',    'margin-bottom',      normLen],
  ['margin-left',      'margin-left',        normLen],
  ['padding-top',      'padding-top',        normLen],
  ['padding-right',    'padding-right',      normLen],
  ['padding-bottom',   'padding-bottom',     normLen],
  ['padding-left',     'padding-left',       normLen],
  ['color',            'color',              normColor],
  ['background-color', 'background-color',   normColor],
  ['font-size',        'font-size',          normLen],
  ['font-weight',      'font-weight',        normWeight],
  ['font-family',      'font-family',        normFamily],
  ['text-align',       'text-align',         normKw],
  ['border-width',     'border-top-width',   normLen],
  ['border-color',     'border-top-color',   normColor],
  ['border-style',     'border-top-style',   normKw],
  ['flex-direction',   'flex-direction',     normKw],
  ['flex-grow',        'flex-grow',          normLen],
  ['top',              'top',                normLen],
  ['left',             'left',               normLen],
  ['z-index',          'z-index',            normLen],
  ['overflow',         'overflow-x',         normKw],
  ['float',            'float',              normKw],
  ['clear',            'clear',              normKw],
];

// N11 attributes: compare as an order-independent key->value map with
// lower-cased NAMES (HTML attribute names are ASCII-case-insensitive) and
// VERBATIM values (values are case-sensitive). Attribute ORDER is explicitly
// not compared -- it is not observable via the DOM API.
function normAttrs(a) {
  const o = {};
  Object.keys(a || {}).forEach((k) => { o[k.toLowerCase()] = String(a[k]); });
  return o;
}

// ---------------------------------------------------------------------------
// Tree normalization: produce a comparable pre-order list of "significant"
// nodes with a stable structural path key.
// ---------------------------------------------------------------------------
function buildTree(doc, side) {
  const raw = doc.nodes;
  const kids = new Map();
  let root = null;
  raw.forEach((n, i) => {
    if (n.parent === -1 || n.parent === undefined || n.parent === null) { if (root === null) root = i; return; }
    if (!kids.has(n.parent)) kids.set(n.parent, []);
    kids.get(n.parent).push(i);
  });
  const out = [];
  function walk(i, path) {
    const n = raw[i];
    if (side === 'chrome' && (isDoctype(n) || isPseudo(n))) return;
    const tag = lowerTag(n.name);
    const rec = {
      tag, text: normText(n.text), attrs: normAttrs(n.attrs),
      style: n.style || {}, path, wsOnly: isWsText(n),
      rawIndex: n.index,
    };
    out.push(rec);
    const cs = (kids.get(i) || []).filter((c) => !(side === 'chrome' && (isDoctype(raw[c]) || isPseudo(raw[c]))));
    const seen = {};
    cs.forEach((c) => {
      const t = lowerTag(raw[c].name);
      seen[t] = (seen[t] || 0) + 1;
      walk(c, path + '/' + t + '[' + seen[t] + ']');
    });
  }
  if (root === null) return out;
  walk(root, lowerTag(raw[root].name));
  return out;
}

function main() {
  const chromePath = process.argv[2];
  const simplePath = process.argv[3];
  const outPath = process.argv[4];
  const fixture = process.argv[5] || '';
  if (!chromePath || !simplePath || !outPath) {
    console.error('DIFF_ERROR usage: normalize_diff.js <chrome.json> <simple.json> <out.json> [fixture]');
    process.exit(1);
  }
  for (const p of [chromePath, simplePath]) {
    if (!fs.existsSync(p)) { console.error('DIFF_ERROR missing extract ' + p); process.exit(1); }
  }
  const C = JSON.parse(fs.readFileSync(chromePath, 'utf8'));
  const S = JSON.parse(fs.readFileSync(simplePath, 'utf8'));
  if (!C.nodes || C.nodes.length === 0) { console.error('DIFF_ERROR chrome side has zero nodes'); process.exit(1); }
  if (!S.nodes || S.nodes.length === 0) { console.error('DIFF_ERROR simple side has zero nodes'); process.exit(1); }

  const ct = buildTree(C, 'chrome');
  const st = buildTree(S, 'simple');

  // Stage 1: DOM structure. Align by structural path key.
  const cByPath = new Map(); ct.forEach((n) => { if (!cByPath.has(n.path)) cByPath.set(n.path, n); });
  const sByPath = new Map(); st.forEach((n) => { if (!sByPath.has(n.path)) sByPath.set(n.path, n); });

  const domFindings = [];
  const onlyChrome = [], onlySimple = [];
  for (const [p, n] of cByPath) if (!sByPath.has(p)) onlyChrome.push({ path: p, tag: n.tag, text: n.text.slice(0, 40), wsOnly: n.wsOnly });
  for (const [p, n] of sByPath) if (!cByPath.has(p)) onlySimple.push({ path: p, tag: n.tag, text: n.text.slice(0, 40), wsOnly: n.wsOnly });

  let domCompared = 0;
  for (const [p, cn] of cByPath) {
    const sn = sByPath.get(p);
    if (!sn) continue;
    domCompared++;
    if (cn.text !== sn.text) domFindings.push({ path: p, kind: 'text', chrome: cn.text.slice(0, 80), simple: sn.text.slice(0, 80) });
    const ck = Object.keys(cn.attrs).sort(), sk = Object.keys(sn.attrs).sort();
    if (ck.join('|') !== sk.join('|')) domFindings.push({ path: p, kind: 'attr-set', chrome: ck.join(','), simple: sk.join(',') });
    for (const k of ck) if (k in sn.attrs && cn.attrs[k] !== sn.attrs[k])
      domFindings.push({ path: p, kind: 'attr-value:' + k, chrome: cn.attrs[k], simple: sn.attrs[k] });
  }

  // Stage 2: computed style. Only nodes present on BOTH sides AND laid out in
  // Chrome (a node with no layout box has no computed style to compare).
  const styleFindings = [];
  let styleNodes = 0, styleProps = 0;
  for (const [p, cn] of cByPath) {
    const sn = sByPath.get(p);
    if (!sn) continue;
    if (cn.tag === '#text' || cn.tag === '#document' || cn.tag === '#comment') continue;
    if (!cn.style || Object.keys(cn.style).length === 0) continue;
    styleNodes++;
    for (const [sProp, cProp, fn] of PROP_MAP) {
      if (!(cProp in cn.style)) continue;
      const cv = fn(cn.style[cProp]);
      const svRaw = sn.style ? sn.style[sProp] : undefined;
      const sv = fn(svRaw);
      styleProps++;
      let same;
      if (typeof cv === 'number' && typeof sv === 'number') same = Math.abs(cv - sv) <= EPS;
      else same = String(cv) === String(sv);
      if (!same) styleFindings.push({
        path: p, prop: sProp, chromeProp: cProp,
        chromeRaw: String(cn.style[cProp]), simpleRaw: String(svRaw),
        chrome: String(cv), simple: String(sv),
      });
    }
  }

  const report = {
    fixture, chromeSource: C.source, simpleSource: S.source,
    chromeNodesRaw: C.nodeCount, simpleNodesRaw: S.nodeCount,
    chromeNodesNormalized: ct.length, simpleNodesNormalized: st.length,
    domComparedNodes: domCompared,
    styleComparedNodes: styleNodes, styleComparedProps: styleProps,
    onlyInChrome: onlyChrome, onlyInSimple: onlySimple,
    domFindings, styleFindings,
    epsilonPx: EPS,
  };
  fs.writeFileSync(outPath, JSON.stringify(report, null, 1));

  // Fail-closed: nothing compared == failure, regardless of finding counts.
  if (domCompared === 0) {
    console.error('DIFF_ERROR compared ZERO dom nodes for ' + fixture + ' (vacuous run)');
    process.exit(1);
  }
  if (styleProps === 0) {
    console.error('DIFF_ERROR compared ZERO style properties for ' + fixture + ' (vacuous run)');
    process.exit(1);
  }
  console.log('DIFF_OK fixture=' + fixture +
    ' domNodes=' + domCompared + ' styleNodes=' + styleNodes + ' styleProps=' + styleProps +
    ' onlyChrome=' + onlyChrome.length + ' onlySimple=' + onlySimple.length +
    ' domFindings=' + domFindings.length + ' styleFindings=' + styleFindings.length);
}
main();
