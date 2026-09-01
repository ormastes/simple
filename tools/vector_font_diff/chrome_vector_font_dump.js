#!/usr/bin/env node
// Chrome-side vector-font glyph dump for the Chrome vector-font differential.
//
// Renders each sample codepoint one-per-row in headless Chrome using the SAME
// TTF file the Simple side rasterizes (@font-face file:// URL, so no system
// font substitution), screenshots the page, decodes the PNG (minimal decoder
// copied from tools/electron-shell/generate_famous_site_glyph_atlas.js), and
// emits per-glyph ink metrics comparable to simple_vector_font_dump.spl:
//   w/h  = ink bounding box of the glyph's row (luminance < 128 = ink)
//   ink  = ink pixel count inside that box
//   density_permille = ink * 1000 / (w * h)
//
// Usage: node chrome_vector_font_dump.js --chrome <bin> --ttf <path> --out <json>

const fs = require("fs");
const os = require("os");
const path = require("path");
const zlib = require("zlib");
const { execFileSync } = require("child_process");

const args = process.argv.slice(2);
function argOf(name) {
  const i = args.indexOf(name);
  return i >= 0 ? args[i + 1] : null;
}
const chromeBin = argOf("--chrome");
const ttfPath = path.resolve(argOf("--ttf"));
const outPath = argOf("--out");
if (!chromeBin || !ttfPath || !outPath) {
  console.error("usage: chrome_vector_font_dump.js --chrome <bin> --ttf <path> --out <json>");
  process.exit(2);
}

// Must stay in sync with SAMPLE in simple_vector_font_dump.spl
const SAMPLE = [65, 103, 72, 120, 111, 48, 49, 86, 87, 46]; // A g H x o 0 1 V W .
const SIZE = 96;
const ROW_H = 160; // generous row so ascenders/descenders never clip

// ---- minimal PNG decode (8-bit, non-interlaced, RGB/RGBA) ----
function decodePng(buf) {
  if (buf.readUInt32BE(0) !== 0x89504e47) throw new Error("not a PNG");
  let pos = 8, width = 0, height = 0, colorType = 0, bitDepth = 0;
  const idat = [];
  while (pos < buf.length) {
    const len = buf.readUInt32BE(pos);
    const type = buf.toString("ascii", pos + 4, pos + 8);
    const data = buf.slice(pos + 8, pos + 8 + len);
    if (type === "IHDR") {
      width = data.readUInt32BE(0);
      height = data.readUInt32BE(4);
      bitDepth = data[8];
      colorType = data[9];
      if (bitDepth !== 8 || (colorType !== 2 && colorType !== 6) || data[12] !== 0) {
        throw new Error(`unsupported PNG format depth=${bitDepth} color=${colorType}`);
      }
    } else if (type === "IDAT") {
      idat.push(data);
    } else if (type === "IEND") break;
    pos += 12 + len;
  }
  const raw = zlib.inflateSync(Buffer.concat(idat));
  const bpp = colorType === 6 ? 4 : 3;
  const stride = width * bpp;
  const out = Buffer.alloc(width * height * 3);
  let prev = Buffer.alloc(stride);
  for (let y = 0; y < height; y += 1) {
    const filter = raw[y * (stride + 1)];
    const row = raw.slice(y * (stride + 1) + 1, (y + 1) * (stride + 1));
    for (let i = 0; i < stride; i += 1) {
      const a = i >= bpp ? row[i - bpp] : 0;
      const b = prev[i];
      const c = i >= bpp ? prev[i - bpp] : 0;
      let v = row[i];
      if (filter === 1) v = (v + a) & 255;
      else if (filter === 2) v = (v + b) & 255;
      else if (filter === 3) v = (v + ((a + b) >> 1)) & 255;
      else if (filter === 4) {
        const p = a + b - c;
        const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c);
        v = (v + (pa <= pb && pa <= pc ? a : pb <= pc ? b : c)) & 255;
      }
      row[i] = v;
    }
    prev = row;
    for (let x = 0; x < width; x += 1) {
      out[(y * width + x) * 3] = row[x * bpp];
      out[(y * width + x) * 3 + 1] = row[x * bpp + 1];
      out[(y * width + x) * 3 + 2] = row[x * bpp + 2];
    }
  }
  return { width, height, data: out };
}

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "vecfontdiff-"));
const htmlPath = path.join(tmp, "sample.html");
const pngPath = path.join(tmp, "sample.png");
let body = "";
for (let i = 0; i < SAMPLE.length; i += 1) {
  const ch = String.fromCodePoint(SAMPLE[i]).replace("&", "&amp;").replace("<", "&lt;");
  body += `<div style="position:absolute;left:8px;top:${i * ROW_H}px;` +
          `font-family:SharedVec;font-size:${SIZE}px;color:#000;` +
          `-webkit-font-smoothing:antialiased;">${ch}</div>\n`;
}
fs.writeFileSync(htmlPath, `<!doctype html><html><head><style>
@font-face { font-family: SharedVec; src: url("file://${ttfPath}"); }
html,body { margin:0; padding:0; background:#fff; }
</style></head><body>${body}</body></html>`);

const height = SAMPLE.length * ROW_H;
execFileSync(chromeBin, [
  "--headless=new", "--no-sandbox", "--disable-gpu",
  "--force-device-scale-factor=1", "--allow-file-access-from-files",
  "--hide-scrollbars", `--window-size=400,${height}`,
  `--screenshot=${pngPath}`, `file://${htmlPath}`,
], { stdio: ["ignore", "pipe", "pipe"], timeout: 120000 });

const versionOut = execFileSync(chromeBin, ["--version"], { timeout: 30000 }).toString().trim();

const img = decodePng(fs.readFileSync(pngPath));
const glyphs = [];
for (let i = 0; i < SAMPLE.length; i += 1) {
  const y0 = i * ROW_H, y1 = Math.min((i + 1) * ROW_H, img.height);
  let minX = Infinity, maxX = -1, minY = Infinity, maxY = -1, ink = 0;
  for (let y = y0; y < y1; y += 1) {
    for (let x = 0; x < img.width; x += 1) {
      const o = (y * img.width + x) * 3;
      const lum = (img.data[o] * 299 + img.data[o + 1] * 587 + img.data[o + 2] * 114) / 1000;
      if (lum < 128) {
        ink += 1;
        if (x < minX) minX = x;
        if (x > maxX) maxX = x;
        if (y < minY) minY = y;
        if (y > maxY) maxY = y;
      }
    }
  }
  const w = maxX >= minX ? maxX - minX + 1 : 0;
  const h = maxY >= minY ? maxY - minY + 1 : 0;
  glyphs.push({
    cp: SAMPLE[i], w, h, ink,
    density_permille: w > 0 && h > 0 ? Math.round((ink * 1000) / (w * h)) : 0,
  });
}
fs.writeFileSync(outPath, JSON.stringify({ chrome_version: versionOut, size: SIZE, glyphs }, null, 1));
fs.rmSync(tmp, { recursive: true, force: true });
console.log(`OK wrote ${outPath} (${versionOut})`);
