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
let minCol = w, minRow = h, maxCol = -1, maxRow = -1;
const WHITE = 0xFFFFFFFF;
const samples = [];

function findComponents() {
  const seen = new Uint8Array(total);
  const components = [];
  const queue = [];
  for (let start = 0; start < total; start++) {
    if (seen[start] || ((ref.pixels[start] >>> 0) === (test.pixels[start] >>> 0))) continue;
    seen[start] = 1;
    queue.length = 0;
    queue.push(start);
    let head = 0, count = 0;
    let c0 = w, r0 = h, c1 = -1, r1 = -1;
    while (head < queue.length) {
      const i = queue[head++];
      const row = Math.floor(i / w);
      const col = i % w;
      count++;
      if (col < c0) c0 = col;
      if (col > c1) c1 = col;
      if (row < r0) r0 = row;
      if (row > r1) r1 = row;
      const neighbors = [i - w, i + w, col > 0 ? i - 1 : -1, col + 1 < w ? i + 1 : -1];
      for (const n of neighbors) {
        if (n < 0 || n >= total || seen[n]) continue;
        if ((ref.pixels[n] >>> 0) === (test.pixels[n] >>> 0)) continue;
        seen[n] = 1;
        queue.push(n);
      }
    }
    components.push({ count, c0, r0, c1, r1 });
  }
  components.sort((a, b) => b.count - a.count);
  return components;
}

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
    const row = Math.floor(i / w);
    const col = i % w;
    if (col < minCol) minCol = col;
    if (col > maxCol) maxCol = col;
    if (row < minRow) minRow = row;
    if (row > maxRow) maxRow = row;
    if (rp === WHITE || tp === WHITE) bgDiff++;
    else textDiff++;
    if (samples.length < 10) {
      samples.push({ col, row, ref: rp.toString(16).padStart(8, "0"), test: tp.toString(16).padStart(8, "0"), delta: d });
    }
  }
}

const pct = total > 0 ? ((differing / total) * 100).toFixed(2) : "0";
console.log(`size=${w}x${h} total=${total}`);
console.log(`differing=${differing} (${pct}%)`);
console.log(`max_channel_delta=${maxDelta} total_delta=${totalDelta}`);
console.log(`bg_diff=${bgDiff} text_diff=${textDiff}`);
console.log(differing === 0 ? "diff_bbox=none" : `diff_bbox=${minCol},${minRow},${maxCol},${maxRow}`);
const components = differing === 0 ? [] : findComponents();
console.log(`diff_component_count=${components.length}`);
console.log(`diff_top_components=${components.slice(0, 8).map(c => `${c.c0},${c.r0},${c.c1},${c.r1}:${c.count}`).join("|")}`);
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
