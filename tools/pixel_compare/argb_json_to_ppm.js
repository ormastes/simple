#!/usr/bin/env node
"use strict";
// Convert ARGB JSON pixel capture to raw PPM (P6).
const fs = require("fs");
const args = process.argv.slice(2);
if (args.length < 2) { console.error("Usage: argb_json_to_ppm.js <input.json> <output.ppm>"); process.exit(1); }
const data = JSON.parse(fs.readFileSync(args[0], "utf8"));
const w = data.width, h = data.height;
const header = `P6\n${w} ${h}\n255\n`;
const buf = Buffer.alloc(w * h * 3);
for (let i = 0; i < w * h; i++) {
  const px = data.pixels[i] >>> 0;
  buf[i * 3] = (px >> 16) & 0xFF;
  buf[i * 3 + 1] = (px >> 8) & 0xFF;
  buf[i * 3 + 2] = px & 0xFF;
}
fs.writeFileSync(args[1], Buffer.concat([Buffer.from(header), buf]));
console.log(`wrote ${args[1]} (${w}x${h})`);
