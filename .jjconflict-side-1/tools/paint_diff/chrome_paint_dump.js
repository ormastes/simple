#!/usr/bin/env node
// Chrome-side PAINT extractor for the Chrome<->Simple component-level
// differential (stage 5: paint / display list).
//
// Input  : one HTML fixture + viewport size.
// Output : Chrome's own Skia op list for every content-drawing composited
//          layer, normalised into the canonical paint-op model documented in
//          tools/paint_diff/CONTRACT.md.
//
// Source of truth is `LayerTree.snapshotCommandLog`, i.e. the recorded
// SkPicture for the layer -- literally what Blink's paint phase produced,
// before rasterisation. This is NOT a pixel comparison.
//
// Two launch-ordering facts were established empirically and are load-bearing:
//   1. `--disable-gpu` yields ZERO layers. Compositing must be on.
//   2. `LayerTree.enable` must be sent AFTER the document has painted, and the
//      layer list must be read off the `LayerTree.layerTreeDidChange` event.
//      Enabling before navigation also yields zero layers.
// Getting either wrong produces an empty command log, which would look like a
// clean pass. This extractor therefore fails closed on an empty op list.
//
// Usage:
//   node chrome_paint_dump.js --chrome <path> --out <dir> [--width 800]
//                             [--height 600] fixture.html [fixture.html ...]

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

// Skia reports colours as "#AARRGGBB". Canonical model uses the same u32 an
// `.color` field on Simple's DrawIrCommand holds, so both sides are directly
// comparable as integers.
function colorToU32(s) {
  if (typeof s !== 'string' || s[0] !== '#') return null;
  const v = parseInt(s.slice(1), 16);
  return Number.isFinite(v) ? v >>> 0 : null;
}

function r(v) {
  // Skia emits fractional device coords; the canonical model is integral css px
  // (Simple's DrawIR is i32). Round rather than truncate so a 0.5 px antialias
  // inset does not read as a 1 px divergence.
  return typeof v === 'number' ? Math.round(v) : null;
}

function rectOf(p) {
  if (!p) return null;
  return { x: r(p.left), y: r(p.top), w: r(p.right - p.left), h: r(p.bottom - p.top) };
}

// Normalise one Skia command into the canonical paint-op model, or null if the
// command carries no cross-engine meaning (save/restore bookkeeping).
function normalizeSkiaOp(cmd, layer) {
  const m = cmd.method;
  const p = cmd.params || {};
  const paint = p.paint || {};
  const color = colorToU32(paint.color);
  const style = (paint.styleName || 'Fill').toLowerCase();
  const dx = layer.offsetX || 0;
  const dy = layer.offsetY || 0;
  const shift = (o) => (o && o.x !== null ? { ...o, x: o.x + dx, y: o.y + dy } : o);

  switch (m) {
    case 'drawPaint':
      // Fills the whole clip. For the root layer this is the canvas clear.
      return { kind: 'canvas_fill', x: dx, y: dy, w: layer.width, h: layer.height, color, style: 'fill' };
    case 'drawRect': {
      const rc = shift(rectOf(p.rect));
      if (!rc) return null;
      return {
        kind: style === 'stroke' ? 'stroke_rect' : 'fill_rect',
        ...rc, color, style,
        stroke_width: r(paint.strokeWidth) || 0,
      };
    }
    case 'drawRRect':
    case 'drawRoundRect': {
      const rr = p.rrect || p.rect;
      const rc = shift(rectOf(rr && rr.rect ? rr.rect : rr));
      if (!rc) return null;
      return { kind: 'fill_rrect', ...rc, color, style, radius: r((rr && rr.radii && rr.radii[0]) || 0) };
    }
    case 'drawDRRect': {
      // Outer-minus-inner round rect: how Chrome paints a rounded border.
      const rc = shift(rectOf((p.outer && p.outer.rect) || p.outer));
      if (!rc) return null;
      return { kind: 'stroke_rrect', ...rc, color, style };
    }
    case 'drawPath':
      return { kind: 'path', x: null, y: null, w: null, h: null, color, style };
    case 'drawTextBlob': {
      // (x, y) is the text BASELINE origin, not the top-left. The differ
      // accounts for this; see CONTRACT.md "baseline".
      return { kind: 'text', x: r(p.x) + dx, y: r(p.y) + dy, w: null, h: null, color, style: 'fill' };
    }
    case 'drawImageRect':
    case 'drawImage': {
      const rc = shift(rectOf(p.dst || p.rect));
      return { kind: 'image', ...(rc || { x: null, y: null, w: null, h: null }), color, style };
    }
    case 'clipRect': {
      const rc = shift(rectOf(p.rect));
      if (!rc) return null;
      return { kind: 'clip_rect', ...rc, color: null, style: 'clip' };
    }
    default:
      return null; // save/restore/concat/setMatrix/translate: structural only
  }
}

async function dumpFixture(cdp, page, fixture, args, tracker) {
  const url = 'file://' + path.resolve(fixture);
  tracker.layers = [];
  await page.goto(url, { waitUntil: 'load' });
  // Let the compositor produce a frame, then wait for the layer tree that
  // frame implies. LayerTree is enabled ONCE for the whole session (see main);
  // enabling/disabling per fixture suppresses the change event entirely and
  // yields zero layers.
  await page.evaluate(() => new Promise((res) => requestAnimationFrame(() => requestAnimationFrame(res))));
  for (let i = 0; i < 60 && tracker.layers.length === 0; i++) {
    await page.waitForTimeout(50);
  }
  const layers = tracker.layers;

  const outLayers = [];
  let opCount = 0;
  for (const l of layers) {
    if (!l.drawsContent) continue;
    let commandLog;
    try {
      const { snapshotId } = await cdp.send('LayerTree.makeSnapshot', { layerId: l.layerId });
      ({ commandLog } = await cdp.send('LayerTree.snapshotCommandLog', { snapshotId }));
      await cdp.send('LayerTree.releaseSnapshot', { snapshotId }).catch(() => {});
    } catch (e) {
      continue; // "Layer does not draw content" for 0x0 helper layers
    }
    const ops = [];
    for (const c of commandLog) {
      const o = normalizeSkiaOp(c, l);
      if (o) ops.push(o);
    }
    opCount += ops.length;
    outLayers.push({
      layer_id: String(l.layerId),
      width: l.width, height: l.height,
      offset_x: l.offsetX || 0, offset_y: l.offsetY || 0,
      raw_op_count: commandLog.length,
      ops,
    });
  }
  return { layers: outLayers, opCount };
}

async function main() {
  const args = parseArgs(process.argv);
  if (!args.chrome || !args.outDir || args.fixtures.length === 0) {
    console.error('usage: chrome_paint_dump.js --chrome <path> --out <dir> [--width N] [--height N] <fixture.html>...');
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
  let totalOps = 0;
  try {
    const context = await browser.newContext({
      viewport: { width: args.width, height: args.height },
      deviceScaleFactor: 1,
    });
    const page = await context.newPage();
    const cdp = await context.newCDPSession(page);
    const version = (await cdp.send('Browser.getVersion')).product;
    console.log('chrome: ' + version);

    // Enable LayerTree exactly once, after a first real paint. A persistent
    // listener keeps the newest layer list; per-fixture enable/disable cycles
    // silently produce zero layers.
    const tracker = { layers: [] };
    cdp.on('LayerTree.layerTreeDidChange', (e) => { if (e.layers) tracker.layers = e.layers; });
    await page.goto('file://' + path.resolve(args.fixtures[0]), { waitUntil: 'load' });
    await cdp.send('LayerTree.enable');
    await page.waitForTimeout(500);

    for (const f of args.fixtures) {
      const base = path.basename(f, '.html');
      let res;
      try {
        res = await dumpFixture(cdp, page, f, args, tracker);
      } catch (e) {
        console.error('FAIL ' + base + ': ' + e.message);
        failures++;
        continue;
      }
      if (res.opCount === 0) {
        // Fail closed: an empty op list is indistinguishable from agreement.
        console.error('FAIL ' + base + ': chrome produced 0 paint ops (compositing off?)');
        failures++;
        continue;
      }
      totalOps += res.opCount;
      const out = path.join(args.outDir, base + '.chrome.json');
      fs.writeFileSync(out, JSON.stringify({
        engine: 'chrome', chrome_version: version, fixture: f,
        viewport: { w: args.width, h: args.height },
        op_count: res.opCount, layers: res.layers,
      }, null, 1));
      console.log('OK   ' + base + ' -> ' + res.opCount + ' paint ops in ' + res.layers.length + ' layer(s)');
    }
  } finally {
    await browser.close();
  }
  console.log('chrome total paint ops: ' + totalOps);
  if (totalOps === 0) { console.error('FATAL: chrome extracted 0 ops overall'); process.exit(5); }
  process.exit(failures > 0 ? 1 : 0);
}

main().catch((e) => { console.error('FATAL: ' + (e && e.stack || e)); process.exit(4); });
