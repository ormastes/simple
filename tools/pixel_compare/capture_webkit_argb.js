#!/usr/bin/env node
"use strict";
/**
 * Capture HTML rendering via Playwright WebKit (Tauri-equivalent).
 * Outputs ARGB JSON in the same format as capture_html_argb.js (Electron).
 *
 * Env vars:
 *   WEBKIT_CAPTURE_HTML    - HTML string to render
 *   WEBKIT_CAPTURE_WIDTH   - viewport width (default 320)
 *   WEBKIT_CAPTURE_HEIGHT  - viewport height (default 240)
 *   WEBKIT_CAPTURE_OUTPUT  - output JSON path
 */
const { webkit } = require("playwright");
const fs = require("fs");
const { PNG } = require("pngjs");

(async () => {
  const html = process.env.WEBKIT_CAPTURE_HTML || "<p>Hello</p>";
  const width = parseInt(process.env.WEBKIT_CAPTURE_WIDTH || "320", 10);
  const height = parseInt(process.env.WEBKIT_CAPTURE_HEIGHT || "240", 10);
  const output = process.env.WEBKIT_CAPTURE_OUTPUT || "";

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
    console.log(`wrote ${output}`);
  } else {
    console.log(`pixels=${pixels.length}`);
  }
})().catch(e => { console.error(e); process.exit(1); });
