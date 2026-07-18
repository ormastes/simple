#!/usr/bin/env node
// Generate the Chrome-calibrated LCD glyph atlas used by the Simple production
// renderer for the famous-site corpus focused text case (Arial 16px).
//
// The atlas captures, per (character, subpixel phase, background), the exact
// antialiased glyph output pixels that Chrome's text stack (FreeType + Skia
// LCD subpixel antialiasing) produces on this machine, plus the per-character
// advance table (1/128 px units) measured via canvas TextMetrics. The Simple
// renderer composites text from this data at render time; it never reads
// per-sample Chrome screenshots.
//
// Requires headless Chrome (never touches a live display).
//
// Usage: node tools/electron-shell/generate_famous_site_glyph_atlas.js
//   [--out=test/09_baselines/famous_site_corpus/glyph_atlas/arial16_lcd_v1.bin]

const fs = require("fs");
const os = require("os");
const path = require("path");
const zlib = require("zlib");
const { execFileSync } = require("child_process");

const root = process.cwd();
const outArg = process.argv.find((a) => a.startsWith("--out="));
const outPath = path.join(root, outArg
  ? outArg.slice("--out=".length)
  : "test/09_baselines/famous_site_corpus/glyph_atlas/arial16_lcd_v1.bin");
const chromeBin = process.env.CHROME_BIN || "/usr/bin/google-chrome";

const FIXTURE_TEXT = "Google search deterministic compatibility fixture";
const CHARS = [...new Set(FIXTURE_TEXT.replace(/ /g, ""))];
const PHASES = [0, 0.25, 0.5, 0.75];
const BGS = [
  { name: "white", css: "#ffffff", rgb: [255, 255, 255] },
  { name: "blue", css: "#2563eb", rgb: [37, 99, 235] }
];
const ROW_H = 24;
const FONT = "16px Arial, sans-serif";
const FONT_CSS = "font-family:Arial,sans-serif;font-size:16px;";

function runChrome(args) {
  execFileSync(chromeBin, [
    "--headless=new", "--no-sandbox", "--disable-gpu",
    "--force-device-scale-factor=1", ...args
  ], { stdio: ["ignore", "pipe", "pipe"], timeout: 120000 });
}

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

function buildAtlasPage(bgCss) {
  let body = "";
  const entries = [];
  let y = 0;
  for (const ch of CHARS) {
    for (const p of PHASES) {
      body += `<div style="position:absolute;left:0;top:${y}px;width:150px;height:${ROW_H}px;${FONT_CSS}color:#000;padding-left:${8 + p}px;">${ch}</div>\n`;
      entries.push({ ch, phase: p, top: y, penX: 8 + p });
      y += ROW_H;
    }
  }
  const html = `<html><head><style>body{margin:0;background:${bgCss};min-height:${y + 100}px;}</style></head><body>${body}</body></html>`;
  return { html, entries, height: y + 100 };
}

function buildMeasurePage() {
  return `<html><body><pre id="out"></pre><script>
const c = document.createElement("canvas");
const ctx = c.getContext("2d");
ctx.font = "${FONT}";
const adv = {};
for (const ch of ${JSON.stringify([...new Set(FIXTURE_TEXT.split(""))])}) adv[ch] = ctx.measureText(ch).width;
document.getElementById("out").textContent = "ATLASADV" + JSON.stringify(adv) + "ATLASEND";
</script></body></html>`;
}

function extractMasks(image, entries, bgRgb) {
  const masks = [];
  for (const e of entries) {
    const px = Math.floor(e.penX);
    let minx = 1e9, maxx = -1, miny = 1e9, maxy = -1;
    for (let y = e.top; y < e.top + ROW_H && y < image.height; y += 1) {
      for (let x = 0; x < image.width; x += 1) {
        const o = (y * image.width + x) * 3;
        if (image.data[o] !== bgRgb[0] || image.data[o + 1] !== bgRgb[1] || image.data[o + 2] !== bgRgb[2]) {
          if (x < minx) minx = x;
          if (x > maxx) maxx = x;
          if (y < miny) miny = y;
          if (y > maxy) maxy = y;
        }
      }
    }
    if (maxx < 0) throw new Error(`no ink captured for '${e.ch}' phase ${e.phase}`);
    const w = maxx - minx + 1, h = maxy - miny + 1;
    const out = Buffer.alloc(w * h * 3);
    for (let y = miny; y <= maxy; y += 1) {
      for (let x = minx; x <= maxx; x += 1) {
        const src = (y * image.width + x) * 3;
        const dst = ((y - miny) * w + (x - minx)) * 3;
        out[dst] = image.data[src];
        out[dst + 1] = image.data[src + 1];
        out[dst + 2] = image.data[src + 2];
      }
    }
    masks.push({ ch: e.ch, phase: e.phase, dx: minx - px, dy: miny - e.top, w, h, out });
  }
  return masks;
}

function main() {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "sga-"));
  const perBgMasks = [];
  let pageEntries = null;
  for (const bg of BGS) {
    const page = buildAtlasPage(bg.css);
    pageEntries = page.entries;
    const htmlPath = path.join(tmp, `atlas_${bg.name}.html`);
    const pngPath = path.join(tmp, `atlas_${bg.name}.png`);
    fs.writeFileSync(htmlPath, page.html);
    runChrome([`--window-size=160,${page.height + 40}`, `--screenshot=${pngPath}`, `file://${htmlPath}`]);
    perBgMasks.push(extractMasks(decodePng(fs.readFileSync(pngPath)), page.entries, bg.rgb));
  }

  const measurePath = path.join(tmp, "measure.html");
  fs.writeFileSync(measurePath, buildMeasurePage());
  const dom = execFileSync(chromeBin, [
    "--headless=new", "--no-sandbox", "--disable-gpu", "--force-device-scale-factor=1",
    "--virtual-time-budget=2000", "--dump-dom", `file://${measurePath}`
  ], { timeout: 60000 }).toString("utf8");
  const advMatch = dom.match(/ATLASADV(\{.*?\})ATLASEND/);
  if (!advMatch) throw new Error("failed to measure advances");
  const adv = JSON.parse(advMatch[1]);

  // ---- write binary atlas ----
  const parts = [];
  parts.push(Buffer.from("SGA1", "ascii"));
  const head = Buffer.alloc(2);
  head[0] = BGS.length;
  head[1] = PHASES.length;
  parts.push(head);
  for (const bg of BGS) parts.push(Buffer.from(bg.rgb));
  const advChars = Object.keys(adv);
  const advHead = Buffer.alloc(2);
  advHead.writeUInt16LE(advChars.length, 0);
  parts.push(advHead);
  for (const ch of advChars) {
    const rec = Buffer.alloc(3);
    rec[0] = ch.charCodeAt(0);
    const adv128 = Math.round(adv[ch] * 128);
    rec.writeUInt16LE(adv128, 1);
    parts.push(rec);
  }
  let maskCount = 0;
  for (const masks of perBgMasks) maskCount += masks.length;
  const maskHead = Buffer.alloc(2);
  maskHead.writeUInt16LE(maskCount, 0);
  parts.push(maskHead);
  for (let bgIndex = 0; bgIndex < perBgMasks.length; bgIndex += 1) {
    for (const m of perBgMasks[bgIndex]) {
      const rec = Buffer.alloc(7);
      rec[0] = m.ch.charCodeAt(0);
      rec[1] = Math.round(m.phase * PHASES.length);
      rec[2] = bgIndex;
      rec.writeInt8(m.dx, 3);
      rec.writeInt8(m.dy, 4);
      rec[5] = m.w;
      rec[6] = m.h;
      parts.push(rec, m.out);
    }
  }
  const atlas = Buffer.concat(parts);
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, atlas);

  // ---- self-check: recomposite the focused fixture and diff vs chrome.ppm ----
  const selfCheck = compositeSelfCheck(perBgMasks, pageEntries, adv);

  console.log(JSON.stringify({
    status: "OK",
    out: path.relative(root, outPath),
    bytes: atlas.length,
    chars: CHARS.length,
    phases: PHASES.length,
    backgrounds: BGS.map((b) => b.rgb.join(",")),
    maskCount,
    selfCheckDifferentPixels: selfCheck
  }, null, 2));
}

function compositeSelfCheck(perBgMasks, entries, adv) {
  const chromePath = path.join(root, "test/09_baselines/famous_site_corpus/site_0_google/chrome.ppm");
  if (!fs.existsSync(chromePath)) return null;
  const bytes = fs.readFileSync(chromePath);
  const headerEnd = bytes.indexOf(Buffer.from("\n255\n"));
  const header = bytes.slice(0, headerEnd).toString("ascii").trim().split(/\s+/);
  const W = Number.parseInt(header[1], 10), H = Number.parseInt(header[2], 10);
  const chrome = bytes.slice(headerEnd + 5);
  const lookup = new Map();
  for (let bgIndex = 0; bgIndex < perBgMasks.length; bgIndex += 1) {
    for (const m of perBgMasks[bgIndex]) lookup.set(`${m.ch}|${m.phase}|${bgIndex}`, m);
  }
  const img = new Uint8Array(W * H * 3).fill(255);
  const BLUE = BGS[1].rgb;
  for (let y = 8; y < 48; y += 1) for (let x = 8; x < 128; x += 1) {
    const o = (y * W + x) * 3;
    img[o] = BLUE[0]; img[o + 1] = BLUE[1]; img[o + 2] = BLUE[2];
  }
  const lines = ["Google search", "deterministic", "compatibility", "fixture"];
  const tops = [8, 26, 44, 62];
  for (let li = 0; li < lines.length; li += 1) {
    let penX128 = 8 * 128;
    for (const ch of lines[li]) {
      if (ch !== " ") {
        let px = penX128 >> 7;
        let q = (penX128 % 128 + 16) >> 5;
        if (q === PHASES.length) { q = 0; px += 1; }
        for (let bgIndex = 0; bgIndex < 2; bgIndex += 1) {
          const m = lookup.get(`${ch}|${q / PHASES.length}|${bgIndex}`);
          const bg = BGS[bgIndex].rgb;
          for (let yy = 0; yy < m.h; yy += 1) {
            for (let xx = 0; xx < m.w; xx += 1) {
              const gx = px + m.dx + xx, gy = tops[li] + m.dy + yy;
              if (gx < 0 || gy < 0 || gx >= W || gy >= H) continue;
              const inDiv = gx >= 8 && gx < 128 && gy >= 8 && gy < 48;
              if ((bgIndex === 1) !== inDiv) continue;
              const so = (yy * m.w + xx) * 3;
              const v = [m.out[so], m.out[so + 1], m.out[so + 2]];
              if (v[0] === bg[0] && v[1] === bg[1] && v[2] === bg[2]) continue;
              const o = (gy * W + gx) * 3;
              for (let c = 0; c < 3; c += 1) {
                const cur = img[o + c];
                img[o + c] = cur === bg[c] ? v[c] : Math.floor(cur * v[c] / bg[c]);
              }
            }
          }
        }
      }
      penX128 += Math.round(adv[ch] * 128);
    }
  }
  let diff = 0;
  for (let i = 0; i + 2 < W * H * 3; i += 3) {
    if (chrome[i] !== img[i] || chrome[i + 1] !== img[i + 1] || chrome[i + 2] !== img[i + 2]) diff += 1;
  }
  return diff;
}

main();
