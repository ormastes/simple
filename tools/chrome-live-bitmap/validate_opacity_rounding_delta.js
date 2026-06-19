#!/usr/bin/env node
"use strict";

const fs = require("fs");

function usage() {
  console.error("usage: validate_opacity_rounding_delta.js <html> <expected-argb.json> <captured-argb.json>");
  process.exit(64);
}

const [htmlPath, expectedPath, capturedPath] = process.argv.slice(2);
if (!htmlPath || !expectedPath || !capturedPath) usage();

function fail(reason) {
  console.log(`opacity_rounding_policy_status=fail`);
  console.log(`opacity_rounding_policy_reason=${reason}`);
  process.exit(1);
}

function readJson(path) {
  try {
    return JSON.parse(fs.readFileSync(path, "utf8"));
  } catch (_err) {
    fail(`invalid-json:${path}`);
  }
}

let html = "";
try {
  html = fs.readFileSync(htmlPath, "utf8");
} catch (_err) {
  fail("missing-html");
}

const requiredHtml = [
  ".half{background-color:#1d4ed8;opacity:0.5;width:20px;height:12px}",
  ".zero{background-color:#ef4444;opacity:0;width:24px;height:10px;margin-top:4px}",
  ".full{background-color:#22c55e;opacity:1;width:16px;height:8px;margin-top:4px}",
  ".shell{background-color:#f8fafc;padding:4px;width:88px;height:56px}",
];
for (const fragment of requiredHtml) {
  if (!html.includes(fragment)) fail("unexpected-opacity-fixture-html");
}

const expected = readJson(expectedPath);
const captured = readJson(capturedPath);
if (expected.width !== 96 || expected.height !== 64) fail("unexpected-expected-dimensions");
if (captured.width !== 96 || captured.height !== 64) fail("unexpected-captured-dimensions");

const expectedPixels = expected.pixels || [];
const capturedPixels = captured.pixels || [];
if (expectedPixels.length !== 96 * 64 || capturedPixels.length !== 96 * 64) {
  fail("unexpected-pixel-count");
}

let mismatch = 0;
for (let i = 0; i < expectedPixels.length; i += 1) {
  const expectedPixel = expectedPixels[i] >>> 0;
  const capturedPixel = capturedPixels[i] >>> 0;
  if (expectedPixel === capturedPixel) continue;
  mismatch += 1;
  const x = i % 96;
  const y = Math.floor(i / 96);
  if (x < 4 || x >= 24 || y < 4 || y >= 16) fail("mismatch-outside-half-opacity-rect");
  if (expectedPixel !== 0xff89a3e9 || capturedPixel !== 0xff8ba4ea) {
    fail("unexpected-opacity-rounding-colors");
  }
}

if (mismatch !== 240) fail("unexpected-opacity-rounding-mismatch-count");

console.log("opacity_rounding_policy_status=pass");
console.log("opacity_rounding_policy_reason=pass");
console.log("opacity_rounding_policy_mismatch_count=240");
console.log("opacity_rounding_policy_expected_argb=0xff89a3e9");
console.log("opacity_rounding_policy_captured_argb=0xff8ba4ea");
