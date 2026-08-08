// Chrome-side stage extractor for the Chrome<->Simple component differential.
//
// Uses CDP DOMSnapshot.captureSnapshot, which returns in ONE call:
//   * the flattened node tree (nodeName, nodeValue, parentIndex, attributes)
//   * per-node computed styles for an explicitly requested property list
//
// Emits the SAME JSON shape as tools/web_diff/simple_extract.spl so the
// differ can align both sides without engine-specific branching.
//
// FAIL-CLOSED: any missing chrome binary, launch failure, extraction failure,
// or a zero-node snapshot exits non-zero. There is no "0 nodes, all good"
// success path.
'use strict';

const fs = require('fs');
const path = require('path');

const REPO = path.resolve(__dirname, '..', '..');
const PW = path.join(REPO, 'tools', 'pixel_compare', 'node_modules', 'playwright');

// The comparable property set. Deliberately small: these are exactly the
// properties Simple's StyleProps can represent. Extracting all ~340 computed
// properties would produce noise Simple has no concept of.
const PROPS = [
  'display', 'position', 'width', 'height',
  'margin-top', 'margin-right', 'margin-bottom', 'margin-left',
  'padding-top', 'padding-right', 'padding-bottom', 'padding-left',
  'color', 'background-color',
  'font-size', 'font-weight', 'font-family', 'text-align',
  'border-top-width', 'border-top-color', 'border-top-style',
  'flex-direction', 'flex-grow',
  'top', 'left', 'z-index', 'overflow-x', 'float', 'clear',
];

function die(msg) {
  console.error('CHROME_EXTRACT_ERROR ' + msg);
  process.exit(1);
}

async function main() {
  const inPath = process.env.WEB_DIFF_IN || '';
  const outPath = process.env.WEB_DIFF_OUT || '';
  const chromePath = process.env.WEB_DIFF_CHROME || '';
  if (!inPath || !outPath) die('missing WEB_DIFF_IN/WEB_DIFF_OUT');
  if (!chromePath) die('missing WEB_DIFF_CHROME (explicit chrome path required)');
  if (!fs.existsSync(chromePath)) die('chrome not found at ' + chromePath);
  if (!fs.existsSync(inPath)) die('fixture not found at ' + inPath);

  let chromium;
  try {
    chromium = require(PW).chromium;
  } catch (e) {
    die('playwright not loadable from ' + PW + ': ' + e.message);
  }

  const browser = await chromium.launch({
    executablePath: chromePath,
    headless: true,
    args: ['--no-sandbox', '--disable-gpu', '--hide-scrollbars',
           '--force-device-scale-factor=1'],
  });
  let doc;
  try {
    const ctx = await browser.newContext({ viewport: { width: 800, height: 600 } });
    const page = await ctx.newPage();
    await page.goto('file://' + path.resolve(inPath), { waitUntil: 'load' });
    const cdp = await ctx.newCDPSession(page);
    await cdp.send('DOM.enable');
    await cdp.send('CSS.enable');
    const snap = await cdp.send('DOMSnapshot.captureSnapshot', {
      computedStyles: PROPS,
      includeDOMRects: false,
      includePaintOrder: false,
    });

    const strings = snap.strings;
    const s = (i) => (i === undefined || i < 0 ? '' : strings[i]);
    if (!snap.documents || snap.documents.length === 0) die('no documents in snapshot');
    const d = snap.documents[0];
    const nodes = d.nodes;
    const n = nodes.nodeName.length;
    if (n === 0) die('snapshot has zero nodes');

    // layout.styles is indexed by layout node, layout.nodeIndex maps to DOM node.
    const styleByNode = new Map();
    const L = d.layout;
    if (L && L.nodeIndex) {
      for (let i = 0; i < L.nodeIndex.length; i++) {
        styleByNode.set(L.nodeIndex[i], L.styles[i]);
      }
    }

    const out = [];
    for (let i = 0; i < n; i++) {
      const attrs = {};
      const a = nodes.attributes[i] || [];
      for (let k = 0; k + 1 < a.length; k += 2) attrs[s(a[k])] = s(a[k + 1]);
      const sortedAttrs = {};
      Object.keys(attrs).sort().forEach((k) => { sortedAttrs[k] = attrs[k]; });

      const style = {};
      const sv = styleByNode.get(i);
      if (sv) for (let p = 0; p < PROPS.length; p++) style[PROPS[p]] = s(sv[p]);

      out.push({
        index: i,
        parent: nodes.parentIndex ? nodes.parentIndex[i] : -1,
        nodeType: nodes.nodeType[i],
        name: s(nodes.nodeName[i]),
        text: s(nodes.nodeValue[i]),
        attrs: sortedAttrs,
        style: style,
        hasLayout: !!sv,
      });
    }
    doc = { engine: 'chrome', source: inPath, nodeCount: out.length, nodes: out };
  } finally {
    await browser.close();
  }

  if (!doc || doc.nodeCount === 0) die('extraction produced zero nodes');
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, JSON.stringify(doc));
  console.log('CHROME_EXTRACT_OK nodes=' + doc.nodeCount + ' -> ' + outPath);
}

main().catch((e) => die(e && e.stack ? e.stack : String(e)));
