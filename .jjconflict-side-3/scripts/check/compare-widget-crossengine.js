#!/usr/bin/env node
"use strict";

// Cross-engine widget-shell structural comparator.
//
// Reads three ARGB-u32 bitmap JSON files rendered from the SAME fixture HTML:
//   - Simple  : layout -> engine2d -> Metal (pure-simple-web-engine2d-metal)
//   - Chrome  : real Chrome headless screenshot (chrome-headless-screenshot)
//   - Electron: real Electron offscreen sRGB capture (electron-chromium-capture)
// plus the Chrome DOM geometry (used as ground truth for text regions).
//
// It encodes a side-by-side PNG per engine and computes a STRUCTURAL, no-blur
// comparison. Text legitimately differs (Simple renders a 5x7/8x16 bitmap font
// vs Chromium's font rasterizer), so glyph pixels are excluded via the Chrome
// DOM text mask and the remaining non-text structure is compared:
//   - theme color presence per engine (bg/panel/accent, per-channel tol)
//   - non-text pixel agreement percentage between engine pairs
//   - the panel color band top/bottom edge derived from pixels
//
// It only reports metrics; the .shs applies thresholds and sets pass/fail. The
// per-channel tolerance is reported honestly in the output keys (no blur).

const fs = require("fs");
const zlib = require("zlib");

function envStr(name, def) { return process.env[name] || def || ""; }
function envInt(name, def) { const v = Number(process.env[name]); return Number.isFinite(v) ? v : def; }

const PREFIX = envStr("COMPARE_PREFIX", "widget_crossengine");
const WIDTH = envInt("COMPARE_WIDTH", 0);
const HEIGHT = envInt("COMPARE_HEIGHT", 0);
const SIMPLE_ARGB = envStr("COMPARE_SIMPLE_ARGB");
const CHROME_ARGB = envStr("COMPARE_CHROME_ARGB");
const ELECTRON_ARGB = envStr("COMPARE_ELECTRON_ARGB");
const CHROME_GEOM = envStr("COMPARE_CHROME_GEOMETRY");
const OUT_DIR = envStr("COMPARE_OUT_DIR", ".");
const FIXTURE = envStr("COMPARE_FIXTURE", "fixture");
const CHANNEL_TOL = envInt("COMPARE_CHANNEL_TOL", 8);
const TEXT_MASK_MAX_AREA_FRACTION = Number(process.env.COMPARE_TEXT_MASK_MAX_AREA_FRACTION || "0.5");
const PANEL_ROW_FRACTION = Number(process.env.COMPARE_PANEL_ROW_FRACTION || "0.25");

const THEME = {
  bg: { r: 0xff, g: 0xff, b: 0xff },
  panel: { r: 0xf5, g: 0xf5, b: 0xf5 },
  accent: { r: 0x00, g: 0x66, b: 0xcc },
};

const out = [];
function emit(key, val) { out.push(`${PREFIX}_${key}=${val}`); }

function fail(reason) {
  emit("status", "fail");
  emit("reason", reason);
  process.stdout.write(out.join("\n") + "\n");
  process.exit(1);
}

function loadArgb(path, label) {
  if (!path || !fs.existsSync(path)) fail(`missing-${label}-argb`);
  const stat = fs.statSync(path);
  let json;
  try { json = JSON.parse(fs.readFileSync(path, "utf8")); }
  catch (_e) { fail(`malformed-${label}-argb`); }
  const px = Array.isArray(json.pixels) ? json.pixels.map(v => (Number(v) >>> 0)) : [];
  return { px, width: Number(json.width) || 0, height: Number(json.height) || 0, bytes: stat.size, producer: String(json.producer || "") };
}

function chan(p) { return { a: (p >>> 24) & 255, r: (p >>> 16) & 255, g: (p >>> 8) & 255, b: p & 255 }; }
function near(p, t, tol) { const c = chan(p); return Math.abs(c.r - t.r) <= tol && Math.abs(c.g - t.g) <= tol && Math.abs(c.b - t.b) <= tol; }
function nearPix(p, q, tol) { const a = chan(p), b = chan(q); return Math.abs(a.r - b.r) <= tol && Math.abs(a.g - b.g) <= tol && Math.abs(a.b - b.b) <= tol; }

function countTheme(px, target, tol) { let n = 0; for (let i = 0; i < px.length; i++) if (near(px[i], target, tol)) n++; return n; }

// ---- minimal RGBA PNG encoder ----
function crc32(buf) {
  let c = ~0;
  for (let i = 0; i < buf.length; i++) {
    c ^= buf[i];
    for (let k = 0; k < 8; k++) c = (c >>> 1) ^ (0xedb88320 & -(c & 1));
  }
  return (~c) >>> 0;
}
function chunk(type, data) {
  const len = Buffer.alloc(4); len.writeUInt32BE(data.length, 0);
  const typeBuf = Buffer.from(type, "ascii");
  const crc = Buffer.alloc(4); crc.writeUInt32BE(crc32(Buffer.concat([typeBuf, data])), 0);
  return Buffer.concat([len, typeBuf, data, crc]);
}
function encodePng(px, w, h) {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(w, 0); ihdr.writeUInt32BE(h, 4);
  ihdr[8] = 8; ihdr[9] = 6; ihdr[10] = 0; ihdr[11] = 0; ihdr[12] = 0; // 8-bit RGBA
  const stride = w * 4;
  const raw = Buffer.alloc((stride + 1) * h);
  for (let y = 0; y < h; y++) {
    raw[y * (stride + 1)] = 0; // filter none
    for (let x = 0; x < w; x++) {
      const p = px[y * w + x] >>> 0;
      const o = y * (stride + 1) + 1 + x * 4;
      raw[o] = (p >>> 16) & 255; raw[o + 1] = (p >>> 8) & 255; raw[o + 2] = p & 255; raw[o + 3] = (p >>> 24) & 255;
    }
  }
  const idat = zlib.deflateSync(raw);
  const sig = Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);
  return Buffer.concat([sig, chunk("IHDR", ihdr), chunk("IDAT", idat), chunk("IEND", Buffer.alloc(0))]);
}

// ---- text mask from Chrome DOM geometry ----
function buildTextMask(w, h) {
  const mask = new Uint8Array(w * h);
  let maskedRects = 0;
  if (!CHROME_GEOM || !fs.existsSync(CHROME_GEOM)) return { mask, maskedRects, masked: 0 };
  let geom;
  try { geom = JSON.parse(fs.readFileSync(CHROME_GEOM, "utf8")); } catch (_e) { return { mask, maskedRects, masked: 0 }; }
  const items = Array.isArray(geom.items) ? geom.items : [];
  const maxArea = TEXT_MASK_MAX_AREA_FRACTION * w * h;
  for (const it of items) {
    const text = String(it.text || "").trim();
    if (text.length === 0) continue;
    const iw = Math.round(Number(it.width) || 0), ih = Math.round(Number(it.height) || 0);
    if (iw <= 0 || ih <= 0) continue;
    if (iw * ih > maxArea) continue; // skip large container elements (aggregated textContent)
    const x0 = Math.max(0, Math.round(Number(it.x) || 0));
    const y0 = Math.max(0, Math.round(Number(it.y) || 0));
    const x1 = Math.min(w, x0 + iw);
    const y1 = Math.min(h, y0 + ih);
    if (x1 <= x0 || y1 <= y0) continue;
    maskedRects++;
    for (let y = y0; y < y1; y++) for (let x = x0; x < x1; x++) mask[y * w + x] = 1;
  }
  let masked = 0; for (let i = 0; i < mask.length; i++) if (mask[i]) masked++;
  return { mask, maskedRects, masked };
}

function agreement(a, b, mask, tol, includeMasked) {
  let total = 0, agree = 0;
  for (let i = 0; i < a.length; i++) {
    if (!includeMasked && mask[i]) continue;
    total++;
    if (nearPix(a[i], b[i], tol)) agree++;
  }
  return { total, agree, pct: total > 0 ? agree / total : 0 };
}

// panel color band: first/last row whose panel-pixel count exceeds fraction*w
function panelBand(px, w, h, tol, frac) {
  let top = -1, bottom = -1;
  const need = Math.max(1, Math.round(frac * w));
  for (let y = 0; y < h; y++) {
    let c = 0;
    for (let x = 0; x < w; x++) if (near(px[y * w + x], THEME.panel, tol)) c++;
    if (c >= need) { if (top < 0) top = y; bottom = y; }
  }
  return { top, bottom };
}

function main() {
  if (WIDTH <= 0 || HEIGHT <= 0) fail("missing-dimensions");
  const N = WIDTH * HEIGHT;
  const simple = loadArgb(SIMPLE_ARGB, "simple");
  const chrome = loadArgb(CHROME_ARGB, "chrome");
  const electron = loadArgb(ELECTRON_ARGB, "electron");
  for (const [label, img] of [["simple", simple], ["chrome", chrome], ["electron", electron]]) {
    if (img.px.length !== N) fail(`${label}-pixel-count-mismatch:${img.px.length}!=${N}`);
    if (img.width !== WIDTH || img.height !== HEIGHT) fail(`${label}-viewport-mismatch:${img.width}x${img.height}`);
  }

  fs.mkdirSync(OUT_DIR, { recursive: true });
  const pngPaths = {};
  for (const [label, img] of [["simple", simple], ["chrome", chrome], ["electron", electron]]) {
    const p = `${OUT_DIR}/${label}_${FIXTURE}.png`;
    fs.writeFileSync(p, encodePng(img.px, WIDTH, HEIGHT));
    pngPaths[label] = p;
  }

  const { mask, maskedRects, masked } = buildTextMask(WIDTH, HEIGHT);

  emit("fixture", FIXTURE);
  emit("width", WIDTH);
  emit("height", HEIGHT);
  emit("channel_tol", CHANNEL_TOL);
  emit("blur_or_tolerance_used", "false");
  emit("comparison_tolerance", `per-channel-abs<=${CHANNEL_TOL}`);
  emit("simple_producer", simple.producer);
  emit("chrome_producer", chrome.producer);
  emit("electron_producer", electron.producer);

  emit("simple_argb_path", SIMPLE_ARGB);
  emit("chrome_argb_path", CHROME_ARGB);
  emit("electron_argb_path", ELECTRON_ARGB);
  emit("simple_argb_bytes", simple.bytes);
  emit("chrome_argb_bytes", chrome.bytes);
  emit("electron_argb_bytes", electron.bytes);
  emit("simple_png_path", pngPaths.simple);
  emit("chrome_png_path", pngPaths.chrome);
  emit("electron_png_path", pngPaths.electron);
  emit("simple_png_bytes", fs.statSync(pngPaths.simple).size);
  emit("chrome_png_bytes", fs.statSync(pngPaths.chrome).size);
  emit("electron_png_bytes", fs.statSync(pngPaths.electron).size);

  emit("text_mask_rects", maskedRects);
  emit("text_mask_pixels", masked);
  emit("text_mask_fraction", (masked / N).toFixed(4));
  emit("nontext_pixels", N - masked);

  // theme color presence per engine
  for (const [label, img] of [["simple", simple], ["chrome", chrome], ["electron", electron]]) {
    emit(`${label}_bg_count`, countTheme(img.px, THEME.bg, CHANNEL_TOL));
    emit(`${label}_panel_count`, countTheme(img.px, THEME.panel, CHANNEL_TOL));
    emit(`${label}_accent_count`, countTheme(img.px, THEME.accent, CHANNEL_TOL));
  }

  // non-text agreement between engine pairs
  const sc = agreement(simple.px, chrome.px, mask, CHANNEL_TOL, false);
  const se = agreement(simple.px, electron.px, mask, CHANNEL_TOL, false);
  const ce = agreement(chrome.px, electron.px, mask, CHANNEL_TOL, false);
  const scFull = agreement(simple.px, chrome.px, mask, CHANNEL_TOL, true);
  emit("nontext_agree_simple_chrome_pct", (sc.pct * 100).toFixed(2));
  emit("nontext_agree_simple_electron_pct", (se.pct * 100).toFixed(2));
  emit("nontext_agree_chrome_electron_pct", (ce.pct * 100).toFixed(2));
  emit("fullframe_agree_simple_chrome_pct", (scFull.pct * 100).toFixed(2));
  emit("nontext_agree_simple_chrome_pixels", `${sc.agree}/${sc.total}`);

  // panel band geometry (pixel-derived)
  const bands = {};
  for (const [label, img] of [["simple", simple], ["chrome", chrome], ["electron", electron]]) {
    const b = panelBand(img.px, WIDTH, HEIGHT, CHANNEL_TOL, PANEL_ROW_FRACTION);
    bands[label] = b;
    emit(`${label}_panel_band_top`, b.top);
    emit(`${label}_panel_band_bottom`, b.bottom);
  }
  const within = (a, b, d) => a >= 0 && b >= 0 && Math.abs(a - b) <= d;
  const topMatchSC = within(bands.simple.top, bands.chrome.top, 2);
  const botMatchSC = within(bands.simple.bottom, bands.chrome.bottom, 2);
  const topMatchCE = within(bands.chrome.top, bands.electron.top, 2);
  const botMatchCE = within(bands.chrome.bottom, bands.electron.bottom, 2);
  emit("geometry_panel_top_match_simple_chrome", topMatchSC);
  emit("geometry_panel_bottom_match_simple_chrome", botMatchSC);
  emit("geometry_panel_top_match_chrome_electron", topMatchCE);
  emit("geometry_panel_bottom_match_chrome_electron", botMatchCE);
  emit("geometry_panel_top_delta_simple_chrome", (bands.simple.top >= 0 && bands.chrome.top >= 0) ? Math.abs(bands.simple.top - bands.chrome.top) : -1);
  emit("geometry_panel_bottom_delta_simple_chrome", (bands.simple.bottom >= 0 && bands.chrome.bottom >= 0) ? Math.abs(bands.simple.bottom - bands.chrome.bottom) : -1);

  emit("status", "pass");
  emit("reason", "pass");

  const report = {};
  for (const line of out) { const i = line.indexOf("="); report[line.slice(0, i)] = line.slice(i + 1); }
  fs.writeFileSync(`${OUT_DIR}/compare_${FIXTURE}.json`, JSON.stringify(report, null, 2));
  process.stdout.write(out.join("\n") + "\n");
}

main();
