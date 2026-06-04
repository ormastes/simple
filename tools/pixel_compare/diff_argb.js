#!/usr/bin/env node
"use strict";
// Diff two ARGB pixel captures (JSON format) and report pixel-level statistics.
//
// Usage:
//   node tools/pixel_compare/diff_argb.js \
//     build/pixel_compare/electron_simple_text.json \
//     build/pixel_compare/simple_simple_text.json

const fs = require("fs");

const args = process.argv.slice(2);
if (args.length < 2) {
  console.error("Usage: diff_argb.js <reference.json> <test.json>");
  process.exit(1);
}

const ref = JSON.parse(fs.readFileSync(args[0], "utf8"));
const test = JSON.parse(fs.readFileSync(args[1], "utf8"));

if (ref.width !== test.width || ref.height !== test.height) {
  console.error(`Size mismatch: ref=${ref.width}x${ref.height} test=${test.width}x${test.height}`);
  process.exit(1);
}

const w = ref.width;
const h = ref.height;
const total = w * h;

let differing = 0;
let maxDelta = 0;
let totalDelta = 0n;
let bgDiff = 0;
let textDiff = 0;
const WHITE = 0xFFFFFFFF;
const samples = [];

for (let i = 0; i < total; i++) {
  const rp = ref.pixels[i] >>> 0;
  const tp = test.pixels[i] >>> 0;
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
      const row = Math.floor(i / w);
      const col = i % w;
      samples.push({ col, row, ref: rp.toString(16).padStart(8, "0"), test: tp.toString(16).padStart(8, "0"), delta: d });
    }
  }
}

const pct = total > 0 ? ((differing / total) * 100).toFixed(2) : "0";
console.log(`size=${w}x${h} total=${total}`);
console.log(`differing=${differing} (${pct}%)`);
console.log(`max_channel_delta=${maxDelta} total_delta=${totalDelta}`);
console.log(`bg_diff=${bgDiff} text_diff=${textDiff}`);
console.log(`ref_producer=${ref.producer} test_producer=${test.producer}`);
if (samples.length > 0) {
  console.log("samples:");
  for (const s of samples) {
    console.log(`  [${s.col},${s.row}] ref=0x${s.ref} test=0x${s.test} delta=${s.delta}`);
  }
}

// Write diff image as PPM for visual inspection
if (args[2]) {
  const ppmPath = args[2];
  const header = `P6\n${w} ${h}\n255\n`;
  const buf = Buffer.alloc(w * h * 3);
  for (let i = 0; i < total; i++) {
    const rp = ref.pixels[i] >>> 0;
    const tp = test.pixels[i] >>> 0;
    const off = i * 3;
    if (rp === tp) {
      // Identical: show grayscale of reference
      const gray = Math.round(((rp >> 16) & 0xFF) * 0.3 + ((rp >> 8) & 0xFF) * 0.59 + (rp & 0xFF) * 0.11);
      buf[off] = Math.round(gray * 0.5);
      buf[off + 1] = Math.round(gray * 0.5);
      buf[off + 2] = Math.round(gray * 0.5);
    } else {
      // Different: red channel = delta magnitude, green = ref brightness, blue = test brightness
      const rr = (rp >> 16) & 0xFF, rg = (rp >> 8) & 0xFF, rb = rp & 0xFF;
      const tr = (tp >> 16) & 0xFF, tg = (tp >> 8) & 0xFF, tb = tp & 0xFF;
      const d = Math.abs(rr - tr) + Math.abs(rg - tg) + Math.abs(rb - tb);
      buf[off] = Math.min(255, d * 2);     // red = delta
      buf[off + 1] = Math.round(rr * 0.3 + rg * 0.59 + rb * 0.11) >> 1; // green = ref
      buf[off + 2] = Math.round(tr * 0.3 + tg * 0.59 + tb * 0.11) >> 1; // blue = test
    }
  }
  fs.writeFileSync(ppmPath, Buffer.concat([Buffer.from(header), buf]));
  console.log(`diff_image=${ppmPath}`);
}
