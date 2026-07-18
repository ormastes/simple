#!/usr/bin/env node
"use strict";
// Diff two PPM images and report pixel-level statistics.
// Supports both raw (P6) and ASCII (P3) PPM.
//
// Usage:
//   node tools/pixel_compare/diff_ppm.js <reference.ppm> <test.ppm> [diff_out.ppm]

const fs = require("fs");

function parsePPM(path) {
  const data = fs.readFileSync(path);
  const isAscii = data[0] === 0x50 && data[1] === 0x33; // "P3"
  const isRaw = data[0] === 0x50 && data[1] === 0x36;   // "P6"

  if (isAscii) {
    const text = data.toString("utf8");
    const tokens = text.split(/\s+/).filter(t => t.length > 0 && !t.startsWith("#"));
    const magic = tokens[0];
    const w = Number(tokens[1]);
    const h = Number(tokens[2]);
    const maxval = Number(tokens[3]);
    const pixels = new Uint32Array(w * h);
    for (let i = 0; i < w * h; i++) {
      const r = Number(tokens[4 + i * 3]);
      const g = Number(tokens[4 + i * 3 + 1]);
      const b = Number(tokens[4 + i * 3 + 2]);
      pixels[i] = ((0xFF << 24) | (r << 16) | (g << 8) | b) >>> 0;
    }
    return { width: w, height: h, pixels };
  }

  if (isRaw) {
    let pos = 2;
    // Skip whitespace and comments
    const skipWS = () => {
      while (pos < data.length) {
        if (data[pos] === 0x23) { // '#' comment
          while (pos < data.length && data[pos] !== 0x0A) pos++;
          pos++;
        } else if (data[pos] <= 0x20) {
          pos++;
        } else break;
      }
    };
    const readNum = () => {
      skipWS();
      let n = 0;
      while (pos < data.length && data[pos] >= 0x30 && data[pos] <= 0x39) {
        n = n * 10 + (data[pos] - 0x30);
        pos++;
      }
      return n;
    };
    const w = readNum();
    const h = readNum();
    const maxval = readNum();
    pos++; // skip single whitespace after maxval
    const pixels = new Uint32Array(w * h);
    for (let i = 0; i < w * h; i++) {
      const r = data[pos++] || 0;
      const g = data[pos++] || 0;
      const b = data[pos++] || 0;
      pixels[i] = ((0xFF << 24) | (r << 16) | (g << 8) | b) >>> 0;
    }
    return { width: w, height: h, pixels };
  }

  throw new Error("Unsupported PPM format in " + path);
}

const args = process.argv.slice(2);
if (args.length < 2) {
  console.error("Usage: diff_ppm.js <reference.ppm> <test.ppm> [diff_out.ppm]");
  process.exit(1);
}

const ref = parsePPM(args[0]);
const test = parsePPM(args[1]);

if (ref.width !== test.width || ref.height !== test.height) {
  console.error(`Size mismatch: ref=${ref.width}x${ref.height} test=${test.width}x${test.height}`);
  process.exit(1);
}

const w = ref.width, h = ref.height, total = w * h;
let differing = 0, maxDelta = 0, bgDiff = 0, textDiff = 0;
let totalDelta = 0n;
const samples = [];
const WHITE = 0xFFFFFFFF;

for (let i = 0; i < total; i++) {
  const rp = ref.pixels[i], tp = test.pixels[i];
  if (rp !== tp) {
    const rr = (rp >> 16) & 0xFF, rg = (rp >> 8) & 0xFF, rb = rp & 0xFF;
    const tr = (tp >> 16) & 0xFF, tg = (tp >> 8) & 0xFF, tb = tp & 0xFF;
    const dr = Math.abs(rr - tr), dg = Math.abs(rg - tg), db = Math.abs(rb - tb);
    const d = dr + dg + db;
    totalDelta += BigInt(d);
    if (d > maxDelta) maxDelta = d;
    differing++;
    if (rp === WHITE || tp === WHITE) bgDiff++;
    else textDiff++;
    if (samples.length < 10) {
      samples.push({ col: i % w, row: Math.floor(i / w),
        ref: rp.toString(16).padStart(8, "0"), test: tp.toString(16).padStart(8, "0"), delta: d });
    }
  }
}

const pct = total > 0 ? ((differing / total) * 100).toFixed(2) : "0";
console.log(`ref=${args[0]} (${ref.width}x${ref.height})`);
console.log(`test=${args[1]} (${test.width}x${test.height})`);
console.log(`differing=${differing}/${total} (${pct}%)`);
console.log(`max_channel_delta=${maxDelta} total_delta=${totalDelta}`);
console.log(`bg_diff=${bgDiff} text_diff=${textDiff}`);

// Classify: are differences structural or fringe (AA)?
let smallDelta = 0, largeDelta = 0;
for (let i = 0; i < total; i++) {
  const rp = ref.pixels[i], tp = test.pixels[i];
  if (rp !== tp) {
    const rr = (rp >> 16) & 0xFF, rg = (rp >> 8) & 0xFF, rb = rp & 0xFF;
    const tr = (tp >> 16) & 0xFF, tg = (tp >> 8) & 0xFF, tb = tp & 0xFF;
    const d = Math.abs(rr - tr) + Math.abs(rg - tg) + Math.abs(rb - tb);
    if (d <= 30) smallDelta++;
    else largeDelta++;
  }
}
console.log(`classification: small_delta(<=30)=${smallDelta} large_delta(>30)=${largeDelta}`);
if (largeDelta > smallDelta) console.log("type=STRUCTURAL (large color differences dominate)");
else console.log("type=FRINGE (small AA-like differences dominate)");

if (samples.length > 0) {
  console.log("samples:");
  for (const s of samples) {
    console.log(`  [${s.col},${s.row}] ref=0x${s.ref} test=0x${s.test} delta=${s.delta}`);
  }
}

// Write diff PPM
if (args[2]) {
  const header = `P6\n${w} ${h}\n255\n`;
  const buf = Buffer.alloc(w * h * 3);
  for (let i = 0; i < total; i++) {
    const rp = ref.pixels[i], tp = test.pixels[i];
    const off = i * 3;
    if (rp === tp) {
      const gray = Math.round(((rp >> 16) & 0xFF) * 0.3 + ((rp >> 8) & 0xFF) * 0.59 + (rp & 0xFF) * 0.11);
      buf[off] = buf[off + 1] = buf[off + 2] = Math.round(gray * 0.4);
    } else {
      const rr = (rp >> 16) & 0xFF, rg = (rp >> 8) & 0xFF, rb = rp & 0xFF;
      const tr = (tp >> 16) & 0xFF, tg = (tp >> 8) & 0xFF, tb = tp & 0xFF;
      const d = Math.abs(rr - tr) + Math.abs(rg - tg) + Math.abs(rb - tb);
      buf[off] = Math.min(255, d * 3);
      buf[off + 1] = 0;
      buf[off + 2] = 0;
    }
  }
  fs.writeFileSync(args[2], Buffer.concat([Buffer.from(header), buf]));
  console.log(`diff_ppm=${args[2]}`);
}
