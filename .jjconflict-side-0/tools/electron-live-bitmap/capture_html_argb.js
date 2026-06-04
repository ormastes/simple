#!/usr/bin/env node
"use strict";
// Capture arbitrary HTML through real Chromium and export ARGB pixel buffer.
//
// Usage:
//   ELECTRON_CAPTURE_HTML=path.html \
//   ELECTRON_CAPTURE_WIDTH=320 \
//   ELECTRON_CAPTURE_HEIGHT=240 \
//   ELECTRON_CAPTURE_OUTPUT=build/pixel_compare/captured.json \
//   xvfb-run --auto-servernum electron --no-sandbox --disable-gpu capture_html_argb.js

const { app, BrowserWindow } = require("electron");
const fs = require("fs");
const path = require("path");

const htmlPath = process.env.ELECTRON_CAPTURE_HTML || "";
const width = Number(process.env.ELECTRON_CAPTURE_WIDTH || 320);
const height = Number(process.env.ELECTRON_CAPTURE_HEIGHT || 240);
const outputPath = process.env.ELECTRON_CAPTURE_OUTPUT || "build/pixel_compare/captured.json";
const settleMs = Number(process.env.ELECTRON_CAPTURE_SETTLE_MS || 1500);

function bitmapToLogicalArgb(image) {
  const size = image.getSize();
  const native = image.toBitmap({ scaleFactor: 1 });
  const nw = size.width;
  const nh = size.height;
  if (nw === width && nh === height) {
    const pixels = new Uint32Array(width * height);
    for (let i = 0; i < width * height; i++) {
      const off = i * 4;
      const b = native[off];
      const g = native[off + 1];
      const r = native[off + 2];
      const a = native[off + 3];
      pixels[i] = ((a << 24) | (r << 16) | (g << 8) | b) >>> 0;
    }
    return { pixels, nativeWidth: nw, nativeHeight: nh, downsampled: false };
  }
  const sx = Math.round(nw / width);
  const sy = Math.round(nh / height);
  const pixels = new Uint32Array(width * height);
  for (let ly = 0; ly < height; ly++) {
    for (let lx = 0; lx < width; lx++) {
      let rSum = 0, gSum = 0, bSum = 0, aSum = 0, n = 0;
      for (let dy = 0; dy < sy; dy++) {
        for (let dx = 0; dx < sx; dx++) {
          const nx = lx * sx + dx;
          const ny = ly * sy + dy;
          if (nx < nw && ny < nh) {
            const off = (ny * nw + nx) * 4;
            bSum += native[off];
            gSum += native[off + 1];
            rSum += native[off + 2];
            aSum += native[off + 3];
            n++;
          }
        }
      }
      const r = Math.round(rSum / n);
      const g = Math.round(gSum / n);
      const b = Math.round(bSum / n);
      const a = Math.round(aSum / n);
      pixels[ly * width + lx] = ((a << 24) | (r << 16) | (g << 8) | b) >>> 0;
    }
  }
  return { pixels, nativeWidth: nw, nativeHeight: nh, downsampled: true };
}

async function main() {
  if (!htmlPath) {
    console.error("ELECTRON_CAPTURE_HTML is required");
    process.exit(1);
  }

  await app.whenReady();
  const win = new BrowserWindow({
    show: false,
    useContentSize: true,
    width,
    height,
    backgroundColor: "#ffffff",
    webPreferences: {
      offscreen: false,
      backgroundThrottling: false,
      nodeIntegration: false,
      contextIsolation: true,
    },
  });
  win.setContentSize(width, height);

  const absHtml = path.resolve(htmlPath);
  await win.loadFile(absHtml);
  await new Promise(r => setTimeout(r, settleMs));

  const image = await win.capturePage({ x: 0, y: 0, width, height });
  const result = bitmapToLogicalArgb(image);

  const payload = {
    width,
    height,
    format: "argb-u32",
    producer: "electron-chromium-capture",
    nativeWidth: result.nativeWidth,
    nativeHeight: result.nativeHeight,
    downsampled: result.downsampled,
    pixels: Array.from(result.pixels, v => v >>> 0),
  };

  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, JSON.stringify(payload));
  console.log("captured=" + outputPath);
  console.log("size=" + width + "x" + height);
  console.log("native=" + result.nativeWidth + "x" + result.nativeHeight);
  console.log("downsampled=" + result.downsampled);
  console.log("pixels=" + result.pixels.length);

  app.quit();
}

main().catch(e => {
  console.error(e);
  process.exit(1);
});
