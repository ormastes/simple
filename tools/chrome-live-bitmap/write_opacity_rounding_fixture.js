#!/usr/bin/env node
"use strict";

const fs = require("fs");
const path = require("path");

const [outDir, capturedHalfArg] = process.argv.slice(2);
if (!outDir || !capturedHalfArg) {
  console.error("usage: write_opacity_rounding_fixture.js <out-dir> <captured-half-argb-hex>");
  process.exit(64);
}

const capturedHalf = Number(capturedHalfArg);
if (!Number.isFinite(capturedHalf)) {
  console.error("invalid captured half ARGB");
  process.exit(65);
}

fs.mkdirSync(outDir, { recursive: true });

const htmlPath = path.join(outDir, "scene.html");
const expectedPath = path.join(outDir, "expected-argb.json");
const capturedPath = path.join(outDir, "captured-argb.json");
const html = "<html><head><style>html,body{margin:0;padding:0;width:96px;height:64px;overflow:hidden;background-color:#f8fafc}.shell{background-color:#f8fafc;padding:4px;width:88px;height:56px}.half{background-color:#1d4ed8;opacity:0.5;width:20px;height:12px}.zero{background-color:#ef4444;opacity:0;width:24px;height:10px;margin-top:4px}.full{background-color:#22c55e;opacity:1;width:16px;height:8px;margin-top:4px}</style></head><body><section class='shell'><div class='half'></div><div class='zero'></div><div class='full'></div></section></body></html>";

const width = 96;
const height = 64;
const expectedPixels = Array(width * height).fill(0xfff8fafc);
const capturedPixels = expectedPixels.slice();
for (let y = 4; y < 16; y += 1) {
  for (let x = 4; x < 24; x += 1) {
    const i = y * width + x;
    expectedPixels[i] = 0xff89a3e9;
    capturedPixels[i] = capturedHalf >>> 0;
  }
}

fs.writeFileSync(htmlPath, html);
fs.writeFileSync(expectedPath, JSON.stringify({ width, height, pixels: expectedPixels }));
fs.writeFileSync(capturedPath, JSON.stringify({ width, height, pixels: capturedPixels }));
console.log(`html_path=${htmlPath}`);
console.log(`expected_argb_path=${expectedPath}`);
console.log(`captured_argb_path=${capturedPath}`);
