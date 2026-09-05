#!/usr/bin/env node
// Chrome-side layout extractor for the Chrome<->Simple component-level layout
// differential.
//
// Stage (3) box geometry  : DOMSnapshot.captureSnapshot layout-tree `bounds`
//                           (border-box, document coords, css px).
// Stage (4) line boxes    : the same snapshot's `textBoxes` (per inline
//                           fragment: bounds + start offset + length into the
//                           layout text), i.e. the shaping/line-breaking oracle.
//
// Usage:
//   node chrome_layout_dump.js --chrome <path> --out <dir> [--width 800]
//                              [--height 600] fixture.html [fixture.html ...]
//
// Fail-closed: any launch/extraction error exits non-zero and writes nothing.

const fs = require('fs');
const path = require('path');

const PW_ROOT = path.resolve(__dirname, '..', 'pixel_compare', 'node_modules');
const { chromium } = require(path.join(PW_ROOT, 'playwright'));

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

// The DOMSnapshot payload is heavily string-interned. These helpers resolve
// the interned indices back to real values.
function mkResolver(strings) {
  return (idx) => (idx === undefined || idx === null || idx < 0 ? null : strings[idx]);
}

function rareStringMap(rare, S) {
  const m = new Map();
  if (!rare) return m;
  for (let i = 0; i < rare.index.length; i++) m.set(rare.index[i], S(rare.value[i]));
  return m;
}

async function main() {
  const args = parseArgs(process.argv);
  if (!args.chrome || !args.outDir || args.fixtures.length === 0) {
    console.error('usage: chrome_layout_dump.js --chrome <path> --out <dir> [--width N] [--height N] <fixture.html>...');
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

  let failures = 0;
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

    for (const fixture of args.fixtures) {
      const abs = path.resolve(fixture);
      try {
        await page.goto('file://' + abs, { waitUntil: 'load' });
        await page.evaluate(() => document.fonts.ready);

        const metrics = await cdp.send('Page.getLayoutMetrics');
        const snap = await cdp.send('DOMSnapshot.captureSnapshot', {
          computedStyles: ['display', 'font-size', 'line-height', 'text-align',
                           'margin-top', 'margin-bottom', 'box-sizing', 'float',
                           'white-space'],
          includeTextBoxes: true,
          includePaintOrder: false,
          includeDOMRects: false,
        });

        const S = mkResolver(snap.strings);
        const doc = snap.documents[0];
        const nodes = doc.nodes;
        const layout = doc.layout;
        const textBoxes = doc.textBoxes;

        // --- DOM side: id attribute + nodeName + parent, per DOM node index.
        const idOf = new Map();
        const nodeName = [];
        for (let i = 0; i < nodes.nodeName.length; i++) nodeName.push(S(nodes.nodeName[i]));
        for (let i = 0; i < nodes.attributes.length; i++) {
          const attrs = nodes.attributes[i] || [];
          for (let a = 0; a + 1 < attrs.length; a += 2) {
            if (S(attrs[a]) === 'id') idOf.set(i, S(attrs[a + 1]));
          }
        }
        const nodeValue = rareStringMap(nodes.nodeValue !== undefined ? null : null, S);
        const rawNodeValue = [];
        for (let i = 0; i < (nodes.nodeValue ? nodes.nodeValue.length : 0); i++) {
          rawNodeValue.push(S(nodes.nodeValue[i]));
        }

        // --- Layout tree: one entry per laid-out node.
        const layoutNodes = [];
        const layoutIndexOfDomNode = new Map();
        for (let li = 0; li < layout.nodeIndex.length; li++) {
          const domIdx = layout.nodeIndex[li];
          const b = layout.bounds[li];
          layoutIndexOfDomNode.set(domIdx, li);
          layoutNodes.push({
            layoutIndex: li,
            domIndex: domIdx,
            nodeName: nodeName[domIdx] || null,
            id: idOf.has(domIdx) ? idOf.get(domIdx) : '',
            parentDom: nodes.parentIndex ? nodes.parentIndex[domIdx] : -1,
            // bounds = [x, y, width, height] border-box, document coordinates,
            // css px, already converted out of LayoutUnit by the browser.
            x: b[0], y: b[1], w: b[2], h: b[3],
            text: layout.text !== undefined && layout.text[li] !== undefined
              ? S(layout.text[li]) : null,
            styles: (layout.styles && layout.styles[li])
              ? layout.styles[li].map(S) : [],
            lines: [],
          });
        }

        // --- Text boxes: attach each inline fragment to its layout node.
        if (textBoxes && textBoxes.layoutIndex) {
          for (let t = 0; t < textBoxes.layoutIndex.length; t++) {
            const li = textBoxes.layoutIndex[t];
            const b = textBoxes.bounds[t];
            const start = textBoxes.start[t];
            const len = textBoxes.length[t];
            const owner = layoutNodes[li];
            if (!owner) continue;
            const full = owner.text || '';
            owner.lines.push({
              start, length: len,
              text: full.substr(start, len),
              x: b[0], y: b[1], w: b[2], h: b[3],
            });
          }
        }
        for (const n of layoutNodes) {
          n.lines.sort((p, q) => (p.y - q.y) || (p.x - q.x));
        }

        const out = {
          engine: 'chrome',
          chrome_version: version,
          fixture: abs,
          viewport: { w: args.width, h: args.height },
          doc_height: metrics.contentSize.height,
          computed_style_names: ['display', 'font-size', 'line-height', 'text-align',
                                 'margin-top', 'margin-bottom', 'box-sizing', 'float',
                                 'white-space'],
          nodes: layoutNodes,
        };
        const outFile = path.join(args.outDir,
          path.basename(fixture).replace(/\.html$/, '') + '.chrome.json');
        fs.writeFileSync(outFile, JSON.stringify(out, null, 1));
        console.log('OK   ' + path.basename(fixture) + ' -> ' + outFile +
                    ' (' + layoutNodes.length + ' layout nodes)');
      } catch (e) {
        failures++;
        console.error('FAIL ' + fixture + ': ' + e.message);
      }
    }
  } finally {
    await browser.close();
  }
  process.exit(failures === 0 ? 0 : 1);
}

main().catch((e) => { console.error('FATAL: ' + e.stack); process.exit(4); });
