#!/usr/bin/env node
// Chrome-side COMPOSITING extractor for the Chrome<->Simple component-level
// differential (stage 6: compositing / layerization).
//
// Input  : one HTML fixture + viewport size.
// Output : Chrome's composited layer list -- the units cc will raster and draw
//          independently -- plus, for every layer, the NAMED reason the
//          compositor promoted it. Normalised into the canonical compositing
//          model documented in tools/composite_diff/CONTRACT.md.
//
// Sources of truth:
//   * `LayerTree.layerTreeDidChange`  -> the layer list itself (bounds, parent,
//     offset, transform, scrollRects, stickyPositionConstraint, drawsContent)
//   * `LayerTree.compositingReasons`  -> the promotion decision, by name
//     (WillChangeTransform, 3DTransform, ActiveOpacityAnimation, Overlap, ...)
//
// This is the layer STRUCTURE, one stage below the paint op stream that
// tools/paint_diff compares. It is not a pixel comparison.
//
// Two launch-ordering facts are load-bearing and were established empirically
// by tools/paint_diff; both fail SILENTLY, producing an empty layer list that
// is indistinguishable from perfect agreement:
//   1. `--disable-gpu` yields ZERO layers. Compositing must be on.
//   2. `LayerTree.enable` must be sent ONCE, after the document has painted,
//      and the layer list read off the persistent `LayerTree.layerTreeDidChange`
//      event. Enabling before navigation, or cycling enable/disable per
//      fixture, also yields zero layers.
// This extractor therefore fails closed on an empty layer list.
//
// Usage:
//   node chrome_composite_dump.js --chrome <path> --out <dir> [--width 800]
//                                 [--height 600] fixture.html [fixture.html ...]

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

// Chrome always emits four scaffolding layers for an ordinary document,
// regardless of content: an anonymous 0x0 root, the root scroll container, the
// root scrolling-contents layer, and the visual viewport layer. They describe
// the frame, not any element, so counting them as "layers Simple is missing"
// would inflate every fixture by a constant four and drown the real signal.
//
// A layer is SCAFFOLDING iff it is one of:
//   * the anonymous 0x0 root layer,
//   * a layer whose reasons include `Viewport`,
//   * a layer whose reasons include `RootScroller`,
//   * the root scroll container: reasons are exactly [OverflowScrolling], it
//     draws no content, and its bounds equal the viewport exactly.
// Everything else is an ELEMENT layer -- a promotion decision Chrome made about
// a specific element, and therefore a decision Simple can be compared against.
//
// The last clause is deliberately narrow. An element's own scroll container
// (e.g. `overflow: scroll` on a 200x100 div) also carries [OverflowScrolling]
// with drawsContent=false, but its bounds are NOT the viewport, so it stays an
// element layer. Verified against fixture 08_overflow_scroll.
function classifyLayer(l, reasons, viewport) {
  if (l.width === 0 && l.height === 0) return 'scaffold_root';
  if (reasons.includes('Viewport')) return 'scaffold_viewport';
  if (reasons.includes('RootScroller')) return 'scaffold_root_scroller';
  if (reasons.length === 1 && reasons[0] === 'OverflowScrolling' &&
      !l.drawsContent && l.width === viewport.w && l.height === viewport.h) {
    return 'scaffold_root_scroll_container';
  }
  return 'element';
}

function transformSummary(t) {
  if (!t || !Array.isArray(t) || t.length !== 16) return null;
  // Column-major 4x4. Identity is the common case and carries no information.
  const identity = [1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1];
  let isIdentity = true;
  for (let i = 0; i < 16; i++) if (Math.abs(t[i] - identity[i]) > 1e-6) { isIdentity = false; break; }
  if (isIdentity) return null;
  // Report whether it has a 3D component, which is what drives promotion.
  const has3d = Math.abs(t[2]) > 1e-6 || Math.abs(t[6]) > 1e-6 ||
                Math.abs(t[8]) > 1e-6 || Math.abs(t[9]) > 1e-6 ||
                Math.abs(t[11]) > 1e-6 || Math.abs(t[14]) > 1e-6;
  return { matrix: t.map((v) => Math.round(v * 1000) / 1000), has_3d: has3d };
}

async function dumpFixture(cdp, page, fixture, args, tracker) {
  const url = 'file://' + path.resolve(fixture);
  tracker.layers = [];
  await page.goto(url, { waitUntil: 'load' });
  // Let the compositor produce a frame, then wait for the layer tree that frame
  // implies. LayerTree is enabled ONCE for the whole session (see main).
  await page.evaluate(() => new Promise((res) => requestAnimationFrame(() => requestAnimationFrame(res))));
  for (let i = 0; i < 60 && tracker.layers.length === 0; i++) {
    await page.waitForTimeout(50);
  }

  const viewport = { w: args.width, h: args.height };
  const out = [];
  for (const l of tracker.layers) {
    let reasons = [];
    try {
      const res = await cdp.send('LayerTree.compositingReasons', { layerId: l.layerId });
      reasons = res.compositingReasonIds || [];
    } catch (e) {
      reasons = [];
    }
    const scroll = (l.scrollRects || []).map((s) => ({
      type: s.type,
      x: Math.round(s.rect.x), y: Math.round(s.rect.y),
      w: Math.round(s.rect.width), h: Math.round(s.rect.height),
    }));
    out.push({
      layer_id: String(l.layerId),
      parent_id: l.parentLayerId === undefined || l.parentLayerId === null ? null : String(l.parentLayerId),
      role: classifyLayer(l, reasons, viewport),
      x: Math.round(l.offsetX || 0), y: Math.round(l.offsetY || 0),
      w: Math.round(l.width), h: Math.round(l.height),
      draws_content: !!l.drawsContent,
      compositing_reasons: reasons,
      transform: transformSummary(l.transform),
      scroll_rects: scroll,
      sticky: l.stickyPositionConstraint ? {
        x: Math.round(l.stickyPositionConstraint.stickyBoxRect.x),
        y: Math.round(l.stickyPositionConstraint.stickyBoxRect.y),
        w: Math.round(l.stickyPositionConstraint.stickyBoxRect.width),
        h: Math.round(l.stickyPositionConstraint.stickyBoxRect.height),
      } : null,
    });
  }
  return out;
}

async function main() {
  const args = parseArgs(process.argv);
  if (!args.chrome || !args.outDir || args.fixtures.length === 0) {
    console.error('usage: chrome_composite_dump.js --chrome <path> --out <dir> [--width N] [--height N] <fixture.html>...');
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
    // NOTE: no --disable-gpu. With it, LayerTree reports zero layers and the
    // whole differential silently compares nothing.
    args: ['--no-sandbox', '--force-device-scale-factor=1',
           '--font-render-hinting=none', '--disable-lcd-text',
           '--enable-gpu-rasterization', '--disable-partial-raster'],
  });

  let failures = 0;
  let totalLayers = 0;
  let totalElementLayers = 0;
  try {
    const context = await browser.newContext({
      viewport: { width: args.width, height: args.height },
      deviceScaleFactor: 1,
    });
    const page = await context.newPage();
    const cdp = await context.newCDPSession(page);
    const version = (await cdp.send('Browser.getVersion')).product;
    console.log('chrome: ' + version);

    // Enable LayerTree exactly once, after a first real paint.
    const tracker = { layers: [] };
    cdp.on('LayerTree.layerTreeDidChange', (e) => { if (e.layers) tracker.layers = e.layers; });
    await page.goto('file://' + path.resolve(args.fixtures[0]), { waitUntil: 'load' });
    await cdp.send('LayerTree.enable');
    await page.waitForTimeout(500);

    for (const f of args.fixtures) {
      const base = path.basename(f, '.html');
      let layers;
      try {
        layers = await dumpFixture(cdp, page, f, args, tracker);
      } catch (e) {
        console.error('FAIL ' + base + ': ' + e.message);
        failures++;
        continue;
      }
      if (layers.length === 0) {
        // Fail closed: an empty layer list is indistinguishable from agreement.
        console.error('FAIL ' + base + ': chrome produced 0 layers (compositing off?)');
        failures++;
        continue;
      }
      const elements = layers.filter((l) => l.role === 'element');
      // A fixture where Chrome emitted no scaffolding at all means the
      // classifier is wrong, not that the page is simple. Fail closed on it.
      if (layers.length === elements.length) {
        console.error('FAIL ' + base + ': every layer classified as an element; scaffolding classifier is broken');
        failures++;
        continue;
      }
      totalLayers += layers.length;
      totalElementLayers += elements.length;
      const out = path.join(args.outDir, base + '.chrome.json');
      fs.writeFileSync(out, JSON.stringify({
        engine: 'chrome', chrome_version: version, fixture: f,
        viewport: { w: args.width, h: args.height },
        layer_count: layers.length,
        element_layer_count: elements.length,
        layers,
      }, null, 1));
      console.log('OK   ' + base + ' -> ' + layers.length + ' layer(s), '
        + elements.length + ' element promotion(s) ['
        + elements.map((e) => e.compositing_reasons.join('+') || 'no-reason').join(', ') + ']');
    }
  } finally {
    await browser.close();
  }
  console.log('chrome total layers: ' + totalLayers + ' (' + totalElementLayers + ' element promotions)');
  if (totalLayers === 0) { console.error('FATAL: chrome extracted 0 layers overall'); process.exit(5); }
  // The whole point of the fixture set is that some elements ARE promoted. If
  // none were, the differential has nothing to measure and must not report a
  // pass.
  if (totalElementLayers === 0) {
    console.error('FATAL: chrome promoted 0 elements across all fixtures; the promotion oracle would be vacuous');
    process.exit(6);
  }
  process.exit(failures > 0 ? 1 : 0);
}

main().catch((e) => { console.error('FATAL: ' + (e && e.stack || e)); process.exit(4); });
