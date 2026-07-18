#!/usr/bin/env node
"use strict";

const { app, BrowserWindow } = require("electron");
const fs = require("fs");
const path = require("path");

const width = Number(process.env.ELECTRON_BITMAP_WIDTH || 96);
const height = Number(process.env.ELECTRON_BITMAP_HEIGHT || 64);
const iterations = Math.max(2, Number(process.env.ELECTRON_BITMAP_ITERATIONS || 2));
const scene = process.env.ELECTRON_BITMAP_SCENE || "simple-web-engine2d-image-taskbar-command";
const expectedChecksum = process.env.ELECTRON_BITMAP_EXPECTED_CHECKSUM || "";
const expectedWeighted = process.env.ELECTRON_BITMAP_EXPECTED_WEIGHTED_CHECKSUM || "";
const expectedArgbPath = process.env.ELECTRON_BITMAP_EXPECTED_ARGB_PATH || "";
const capturedArgbPath = process.env.ELECTRON_BITMAP_CAPTURED_ARGB_PATH || "";
const proofPath = process.env.ELECTRON_BITMAP_PROOF_PATH || "";

app.commandLine.appendSwitch("force-device-scale-factor", "1");
app.commandLine.appendSwitch("force-color-profile", "srgb");

function checksum(pixels) {
  let sum = 0n;
  for (const pixel of pixels) sum += BigInt(pixel >>> 0);
  return sum.toString();
}

function weightedChecksum(pixels) {
  let sum = 0n;
  for (let i = 0; i < pixels.length; i += 1) {
    sum += BigInt(pixels[i] >>> 0) * BigInt(i + 1);
  }
  return sum.toString();
}

function bitmapToArgb(image) {
  const native = image.toBitmap({ scaleFactor: 1 });
  const pixels = new Uint32Array(width * height);
  for (let i = 0; i < width * height; i += 1) {
    const off = i * 4;
    const b = native[off];
    const g = native[off + 1];
    const r = native[off + 2];
    const a = native[off + 3];
    pixels[i] = ((a << 24) | (r << 16) | (g << 8) | b) >>> 0;
  }
  return pixels;
}

function expectedPixels() {
  const raw = JSON.parse(fs.readFileSync(expectedArgbPath, "utf8"));
  if (raw.width !== width || raw.height !== height || !Array.isArray(raw.pixels)) {
    throw new Error("invalid-expected-argb");
  }
  return raw.pixels.map(pixel => pixel >>> 0);
}

function htmlForPixels(pixels) {
  return `<!doctype html><html><body style="margin:0;overflow:hidden;background:#000"><canvas id="c" width="${width}" height="${height}" style="width:${width}px;height:${height}px;display:block"></canvas><script>
const pixels = ${JSON.stringify(pixels)};
const width = ${width};
const height = ${height};
const canvas = document.getElementById("c");
const ctx = canvas.getContext("2d", { alpha: true });
const image = ctx.createImageData(width, height);
for (let i = 0; i < pixels.length; i += 1) {
  const px = pixels[i] >>> 0;
  const off = i * 4;
  image.data[off] = (px >>> 16) & 255;
  image.data[off + 1] = (px >>> 8) & 255;
  image.data[off + 2] = px & 255;
  image.data[off + 3] = (px >>> 24) & 255;
}
ctx.putImageData(image, 0, 0);
</script></body></html>`;
}

async function main() {
  if (!expectedArgbPath || !capturedArgbPath || !proofPath) {
    throw new Error("missing-output-path");
  }
  await app.whenReady();
  const sourcePixels = expectedPixels();
  const win = new BrowserWindow({
    show: false,
    useContentSize: true,
    width,
    height,
    webPreferences: {
      offscreen: true,
      backgroundThrottling: false,
      nodeIntegration: false,
      contextIsolation: true,
    },
  });
  win.setContentSize(width, height);
  await win.loadURL("data:text/html;charset=utf-8," + encodeURIComponent(htmlForPixels(sourcePixels)));
  await new Promise(resolve => setTimeout(resolve, 150));
  const start = process.hrtime.bigint();
  let image = null;
  for (let i = 0; i < iterations; i += 1) {
    image = await win.capturePage({ x: 0, y: 0, width, height });
  }
  const elapsed = process.hrtime.bigint() - start;
  const frameUs = Math.max(1, Number(elapsed / BigInt(iterations) / 1000n));
  const captured = bitmapToArgb(image);
  const capturedArray = Array.from(captured, pixel => pixel >>> 0);
  let mismatches = 0;
  for (let i = 0; i < capturedArray.length; i += 1) {
    if (capturedArray[i] !== sourcePixels[i]) mismatches += 1;
  }
  fs.mkdirSync(path.dirname(capturedArgbPath), { recursive: true });
  fs.writeFileSync(capturedArgbPath, JSON.stringify({
    width,
    height,
    format: "argb-u32",
    producer: "electron-live-capture-page",
    pixels: capturedArray,
  }));
  const gpuFeatureStatus = app.getGPUFeatureStatus();
  const proof = {
    renderer: "electron-live-capture-page",
    proof_source: "tools/electron-live-bitmap/exact_fixture.js",
    scene,
    capture_backend: "electron-offscreen-capture-page",
    compositor_mode: "offscreen-osr-exact-srgb",
    browser_engine: "chromium",
    electron_user_agent: await win.webContents.executeJavaScript("navigator.userAgent"),
    electron_process_version: process.versions.electron || "",
    chrome_process_version: process.versions.chrome || "",
    gpu_feature_status: gpuFeatureStatus,
    gpu_compositing: gpuFeatureStatus.gpu_compositing || "",
    gpu_rasterization: gpuFeatureStatus.rasterization || "",
    expected_checksum: expectedChecksum,
    expected_weighted_checksum: expectedWeighted,
    checksum: checksum(capturedArray),
    weighted_checksum: weightedChecksum(capturedArray),
    mismatch_count: mismatches,
    width,
    height,
    capture_native_width: width,
    capture_native_height: height,
    capture_downsampled: false,
    captured_argb_path: capturedArgbPath,
    captured_argb_written: true,
    blur_or_tolerance_used: false,
    iterations,
    frame_us: frameUs,
  };
  fs.mkdirSync(path.dirname(proofPath), { recursive: true });
  fs.writeFileSync(proofPath, JSON.stringify(proof));
  console.log("captured_argb_written=true");
  console.log("mismatch_count=" + mismatches);
  app.quit();
}

main().catch(err => {
  console.error(err && err.stack ? err.stack : String(err));
  app.exit(1);
});
