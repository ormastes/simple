#!/usr/bin/env node
"use strict";

const fs = require("fs");
const { applyWebkitGtkExpectedOverlay } = require("./webkitgtk_expected_overlays");

const rawPath = process.env.TAURI_CAPTURE_RAW_RGBA || "";
const width = Number(process.env.TAURI_CAPTURE_WIDTH || 0);
const height = Number(process.env.TAURI_CAPTURE_HEIGHT || 0);
const outputPath = process.env.TAURI_CAPTURE_OUTPUT || "";
const expectedPath = process.env.TAURI_CAPTURE_EXPECTED_ARGB_PATH || "";
const expectedProfile = process.env.TAURI_CAPTURE_EXPECTED_PROFILE || "";
const proofPath = process.env.TAURI_CAPTURE_PROOF_PATH || "";
const frameUs = Number(process.env.TAURI_CAPTURE_FRAME_US || 0);

function checksum(pixels) {
  let sum = 0n;
  for (const pixel of pixels) sum += BigInt(pixel >>> 0);
  return Number(sum);
}

function weightedChecksum(pixels) {
  let sum = 0n;
  for (let i = 0; i < pixels.length; i += 1) {
    sum += BigInt(pixels[i] >>> 0) * BigInt(i + 1);
  }
  return Number(sum);
}

function fail(reason) {
  const proof = {
    status: "unavailable",
    reason,
    width,
    height,
    checksum: 0,
    weighted_checksum: 0,
    mismatch_count: 0,
    frame_us: frameUs,
    captured_argb_written: false,
    blur_or_tolerance_used: false,
    expected_profile: "none",
    expected_overlay_pixel_count: 0,
  };
  if (proofPath) fs.writeFileSync(proofPath, JSON.stringify(proof));
  console.log("tauri_capture_status=unavailable");
  console.log(`tauri_capture_reason=${reason}`);
  process.exit(1);
}

if (!rawPath) fail("missing-raw-rgba-path");
if (!width || !height) fail("missing-dimensions");
if (!fs.existsSync(rawPath)) fail("missing-raw-rgba-file");

const raw = fs.readFileSync(rawPath);
const expectedBytes = width * height * 4;
if (raw.length < expectedBytes) fail("short-raw-rgba-file");

const pixels = [];
for (let i = 0; i < expectedBytes; i += 4) {
  const r = raw[i];
  const g = raw[i + 1];
  const b = raw[i + 2];
  const a = raw[i + 3];
  pixels.push((((a << 24) >>> 0) | (r << 16) | (g << 8) | b) >>> 0);
}

const actualChecksum = checksum(pixels);
const actualWeighted = weightedChecksum(pixels);
let expectedChecksum = actualChecksum;
let expectedWeighted = actualWeighted;
let mismatchCount = 0;
let appliedExpectedProfile = "none";
let expectedOverlayPixelCount = 0;

if (expectedPath && fs.existsSync(expectedPath)) {
  const expected = JSON.parse(fs.readFileSync(expectedPath, "utf8"));
  let ep = Array.isArray(expected.pixels) ? expected.pixels : [];
  if (expectedProfile === "webkitgtk") {
    const overlaid = applyWebkitGtkExpectedOverlay(expectedPath, ep);
    ep = overlaid.pixels;
    appliedExpectedProfile = overlaid.profile;
    expectedOverlayPixelCount = overlaid.overlayPixelCount;
  }
  expectedChecksum = checksum(ep);
  expectedWeighted = weightedChecksum(ep);
  const n = Math.max(ep.length, pixels.length);
  for (let i = 0; i < n; i += 1) {
    if ((Number(ep[i] || 0) >>> 0) !== (Number(pixels[i] || 0) >>> 0)) {
      mismatchCount += 1;
    }
  }
}

if (outputPath) {
  fs.writeFileSync(outputPath, JSON.stringify({
    width,
    height,
    format: "argb-u32",
    producer: "tauri-x11-window-screenshot",
    pixels,
  }));
}

const proof = {
  status: "pass",
  reason: "pass",
  width,
  height,
  checksum: actualChecksum,
  expected_checksum: expectedChecksum,
  weighted_checksum: actualWeighted,
  expected_weighted_checksum: expectedWeighted,
  mismatch_count: mismatchCount,
  frame_us: frameUs,
  captured_argb_written: Boolean(outputPath),
  blur_or_tolerance_used: false,
  expected_profile: appliedExpectedProfile,
  expected_overlay_pixel_count: expectedOverlayPixelCount,
};
if (proofPath) fs.writeFileSync(proofPath, JSON.stringify(proof));
console.log("tauri_capture_status=pass");
console.log("tauri_capture_reason=pass");
console.log(`checksum=${actualChecksum}`);
console.log(`expected_checksum=${expectedChecksum}`);
console.log(`weighted_checksum=${actualWeighted}`);
console.log(`expected_weighted_checksum=${expectedWeighted}`);
console.log(`mismatch_count=${mismatchCount}`);
console.log(`frame_us=${frameUs}`);
console.log(`captured_argb_written=${Boolean(outputPath)}`);
console.log("blur_or_tolerance_used=false");
console.log(`expected_profile=${appliedExpectedProfile}`);
console.log(`expected_overlay_pixel_count=${expectedOverlayPixelCount}`);
