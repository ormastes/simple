#!/usr/bin/env node
"use strict";
const { webkit } = require("playwright");
const fs = require("fs");
const path = require("path");
const { PNG } = require("pngjs");

(async () => {
  const htmlPath = process.env.WEBKIT_CAPTURE_HTML || "";
  const width = parseInt(process.env.WEBKIT_CAPTURE_WIDTH || "320", 10);
  const height = parseInt(process.env.WEBKIT_CAPTURE_HEIGHT || "240", 10);
  const output = process.env.WEBKIT_CAPTURE_OUTPUT || "";

  if (!htmlPath) { console.error("WEBKIT_CAPTURE_HTML required"); process.exit(1); }
  const absPath = path.resolve(htmlPath);
  const html = fs.readFileSync(absPath, "utf8");

  const browser = await webkit.launch({ headless: true });
  const page = await browser.newPage({ viewport: { width, height } });
  await page.setContent(html, { waitUntil: "networkidle" });
  await page.waitForTimeout(500);

  const buf = await page.screenshot({ type: "png", fullPage: false });
  await browser.close();

  const png = PNG.sync.read(buf);
  const pixels = [];
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const off = (y * png.width + x) * 4;
      const r = png.data[off], g = png.data[off+1], b = png.data[off+2], a = png.data[off+3];
      pixels.push(((a << 24) | (r << 16) | (g << 8) | b) >>> 0);
    }
  }

  const result = { width, height, pixels };
  if (output) {
    fs.writeFileSync(output, JSON.stringify(result));
    console.log("wrote " + output);
  } else {
    console.log("pixels=" + pixels.length);
  }
})().catch(e => { console.error(e); process.exit(1); });
