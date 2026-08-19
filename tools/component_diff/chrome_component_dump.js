#!/usr/bin/env node
// Chrome-side extractor for the per-component chrome-alignment IO harness.
//
// Loads one component fixture, dumps box geometry as a canonical TEXT form
// (state 0), then drives the component's IO through the REAL browser event
// path (page.click on #inc, then #dec) and dumps the geometry again after
// each interaction (states 1 and 2). The same text form is produced by
// tools/component_diff/simple_component_dump.spl, and the two are diffed by
// component_geom_diff.spl via std layout_text_diff.
//
// Canonical geometry text form (one line per retained node, sorted):
//   <key> [x,y wxh] "<normalized text, 40 chars max>"
// Keys follow tools/layout_diff/CONTRACT.md: #<id> for elements with ids,
// else <parentKey>/<tag>[<ordinal>]. Non-rendered subtrees (head, style,
// script, meta, title, link, base) and whitespace-only text nodes are
// dropped; the document root is excluded from geometry (viewport vs extent
// category error, see CONTRACT.md rule 3).
//
// Usage: node chrome_component_dump.js --chrome <path> --out <dir>
//        [--width 800] [--height 600] fixture.html
// Fail-closed: any error exits non-zero.

const fs = require('fs');
const path = require('path');
const PW_ROOT = path.resolve(__dirname, '..', 'pixel_compare', 'node_modules');
const { chromium } = require(path.join(PW_ROOT, 'playwright'));

const DROP_TAGS = new Set(['head', 'meta', 'style', 'script', 'title', 'link', 'base']);

function parseArgs(argv) {
  const out = { chrome: null, outDir: null, width: 800, height: 600, fixtures: [] };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--chrome') out.chrome = argv[++i];
    else if (a === '--out') out.outDir = argv[++i];
    else if (a === '--width') out.width = parseInt(argv[++i], 10);
    else if (a === '--height') out.height = parseInt(argv[++i], 10);
    else out.fixtures.push(a);
  }
  return out;
}

function normText(s) {
  const t = (s || '').replace(/\s+/g, ' ').trim();
  return t.length > 40 ? t.substring(0, 40) + '...' : t;
}

// Build the canonical geometry text from a DOMSnapshot.
function geometryText(snap) {
  const S = (i) => (i === undefined || i === null || i < 0 ? null : snap.strings[i]);
  const doc = snap.documents[0];
  const nodes = doc.nodes;
  const layout = doc.layout;
  const n = nodes.nodeName.length;
  const tag = [], id = [], parent = [], value = [];
  for (let i = 0; i < n; i++) {
    tag.push((S(nodes.nodeName[i]) || '').toLowerCase());
    parent.push(nodes.parentIndex ? nodes.parentIndex[i] : -1);
    value.push(nodes.nodeValue ? S(nodes.nodeValue[i]) : null);
    id.push('');
  }
  for (let i = 0; i < nodes.attributes.length; i++) {
    const attrs = nodes.attributes[i] || [];
    for (let a = 0; a + 1 < attrs.length; a += 2) {
      if (S(attrs[a]) === 'id') id[i] = S(attrs[a + 1]);
    }
  }
  // retained = not (in a dropped subtree) and not whitespace-only text; the
  // document node itself is retained for keying but emits no geometry line.
  const retained = new Array(n).fill(false);
  const isDoc = (i) => tag[i] === '#document';
  for (let i = 0; i < n; i++) {
    let drop = false;
    // Doctype nodes (nodeType 10) report nodeName "html" and would shift the
    // real <html> element's sibling ordinal; Simple's arena has no doctype node.
    if (nodes.nodeType && nodes.nodeType[i] === 10) drop = true;
    for (let a = i; !drop && a >= 0; a = parent[a]) {
      if (DROP_TAGS.has(tag[a])) { drop = true; break; }
    }
    if (!drop && tag[i] === '#text' && normText(value[i]) === '') drop = true;
    retained[i] = !drop;
  }
  // keys
  const key = new Array(n).fill(null);
  const ordCount = new Map(); // parentKey + '/' + tag -> count
  const retainedParentKey = (i) => {
    for (let a = parent[i]; a >= 0; a = parent[a]) {
      if (retained[a] && key[a] !== null) return key[a];
    }
    return '#root';
  };
  for (let i = 0; i < n; i++) {
    if (!retained[i]) continue;
    if (isDoc(i)) { key[i] = '#root'; continue; }
    if (id[i] !== '') { key[i] = '#' + id[i]; continue; }
    const pk = retainedParentKey(i);
    const bucket = pk + '/' + tag[i];
    const ord = ordCount.get(bucket) || 0;
    ordCount.set(bucket, ord + 1);
    key[i] = bucket + '[' + ord + ']';
  }
  // geometry lines from layout tree
  const lines = [];
  for (let li = 0; li < layout.nodeIndex.length; li++) {
    const di = layout.nodeIndex[li];
    if (!retained[di] || isDoc(di)) continue;
    // html/body wrappers exist on both sides; keep them.
    const b = layout.bounds[li];
    const txt = tag[di] === '#text' ? normText(value[di]) : '';
    lines.push(key[di] + ' [' + Math.round(b[0]) + ',' + Math.round(b[1]) +
               ' ' + Math.round(b[2]) + 'x' + Math.round(b[3]) + '] "' + txt + '"');
  }
  lines.sort();
  return lines.join('\n') + '\n';
}

async function main() {
  const args = parseArgs(process.argv);
  if (!args.chrome || !args.outDir || args.fixtures.length !== 1) {
    console.error('usage: chrome_component_dump.js --chrome <path> --out <dir> <fixture.html>');
    process.exit(2);
  }
  if (!fs.existsSync(args.chrome)) {
    console.error('FATAL: chrome executable not found: ' + args.chrome);
    process.exit(3);
  }
  fs.mkdirSync(args.outDir, { recursive: true });
  const browser = await chromium.launch({
    executablePath: args.chrome,
    headless: true,
    args: ['--no-sandbox', '--disable-gpu', '--force-device-scale-factor=1',
           '--font-render-hinting=none', '--disable-lcd-text'],
  });
  try {
    const context = await browser.newContext({
      viewport: { width: args.width, height: args.height },
      deviceScaleFactor: 1,
    });
    const page = await context.newPage();
    const cdp = await context.newCDPSession(page);
    await cdp.send('DOM.enable');
    await cdp.send('DOMSnapshot.enable');
    const version = (await cdp.send('Browser.getVersion')).product;

    const fixture = path.resolve(args.fixtures[0]);
    const base = path.basename(fixture).replace(/\.html$/, '');
    await page.goto('file://' + fixture, { waitUntil: 'load' });
    await page.evaluate(() => document.fonts.ready);

    const capture = async () => geometryText(await cdp.send('DOMSnapshot.captureSnapshot', {
      computedStyles: [], includeTextBoxes: false, includePaintOrder: false, includeDOMRects: false,
    }));

    // Per-fixture interaction script, declared IN the fixture:
    //   <meta name="component-actions" content="click:#id,fill:#id:value">
    //   <meta name="component-observe" content="idOfObservedElement">
    const meta = await page.evaluate(() => {
      const g = (n) => {
        const m = document.querySelector('meta[name="' + n + '"]');
        return m ? m.getAttribute('content') || '' : '';
      };
      return { actions: g('component-actions'), observe: g('component-observe') };
    });
    const actions = meta.actions === '' ? [] : meta.actions.split(',');
    const observeId = meta.observe;
    const displayText = async () => observeId === '' ? '' : page.evaluate(
      (id) => document.getElementById(id).textContent, observeId);

    const states = [];
    const displays = [];
    states.push(await capture()); displays.push(await displayText());
    for (const action of actions) {
      const parts = action.split(':');
      if (parts[0] === 'click') {
        await page.click(parts[1]);                        // REAL browser event path
      } else if (parts[0] === 'fill') {
        await page.fill(parts[1], parts.slice(2).join(':')); // REAL input pipeline (fires input events)
      } else {
        console.error('FATAL: unknown action: ' + action); process.exit(6);
      }
      states.push(await capture()); displays.push(await displayText());
    }

    for (let s = 0; s < states.length; s++) {
      fs.writeFileSync(path.join(args.outDir, base + '.state' + s + '.txt'), states[s]);
    }
    fs.writeFileSync(path.join(args.outDir, base + '.meta.json'), JSON.stringify({
      engine: 'chrome', chrome_version: version, fixture,
      viewport: { w: args.width, h: args.height }, displays,
    }, null, 1));
    if (!version.includes('Chrome/')) { console.error('FATAL: not a real chrome'); process.exit(5); }
    console.log('OK ' + base + ' ' + states.length + ' states, displays: ' + JSON.stringify(displays));
  } finally {
    await browser.close();
  }
}

main().catch((e) => { console.error('FATAL: ' + e.stack); process.exit(4); });
