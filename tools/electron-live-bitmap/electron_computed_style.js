"use strict";
// Minimal Electron (Chromium) computed-style probe. Emits the same per-selector
// fields as tools/webkit-live-geometry/capture_geometry.swift so Chromium and
// WebKit titlebar rendering can be compared field-for-field.
//
// Usage:
//   ELECTRON_CS_HTML=fixture.html ELECTRON_CS_WIDTH=600 ELECTRON_CS_HEIGHT=120 \
//   ELECTRON_CS_SELECTORS=".a,.b" ELECTRON_CS_OUTPUT=out.json \
//   Electron --no-sandbox --disable-gpu electron_computed_style.js

const { app, BrowserWindow } = require("electron");
const fs = require("fs");
const path = require("path");

const htmlPath = process.env.ELECTRON_CS_HTML || "";
const width = Number(process.env.ELECTRON_CS_WIDTH || 600);
const height = Number(process.env.ELECTRON_CS_HEIGHT || 120);
const selectors = (process.env.ELECTRON_CS_SELECTORS || "")
  .split(",").map(s => s.trim()).filter(Boolean);
const outputPath = process.env.ELECTRON_CS_OUTPUT || "electron_computed_style.json";
const settleMs = Number(process.env.ELECTRON_CS_SETTLE_MS || 600);

app.commandLine.appendSwitch("disable-gpu");

app.whenReady().then(async () => {
  const win = new BrowserWindow({
    width, height, show: false,
    webPreferences: { offscreen: true },
  });
  await win.loadFile(htmlPath);
  await new Promise(r => setTimeout(r, settleMs));
  const js = `(function(){
    var selectors = ${JSON.stringify(selectors)};
    var items = [];
    selectors.forEach(function(sel){
      Array.prototype.slice.call(document.querySelectorAll(sel)).forEach(function(el, index){
        var r = el.getBoundingClientRect();
        var cs = getComputedStyle(el);
        items.push({
          selector: sel, index: index, tag: el.tagName.toLowerCase(),
          rect: { left: Math.round(r.left), top: Math.round(r.top),
                  width: Math.round(r.width), height: Math.round(r.height) },
          display: cs.display, position: cs.position,
          boxSizing: cs.boxSizing, borderTopWidth: cs.borderTopWidth,
          paddingTop: cs.paddingTop, paddingLeft: cs.paddingLeft,
          fontFamily: cs.fontFamily, fontSize: cs.fontSize,
          lineHeight: cs.lineHeight, appearance: cs.appearance || cs.webkitAppearance,
          color: cs.color, background: cs.backgroundColor,
          userSelect: cs.userSelect || cs.webkitUserSelect, cursor: cs.cursor
        });
      });
    });
    return JSON.stringify({ producer: "electron-chromium-computed-style",
      viewport: { width: ${width}, height: ${height} }, items: items });
  })();`;
  const json = await win.webContents.executeJavaScript(js);
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, json);
  console.log("electron_cs=" + outputPath);
  console.log("electron_cs_items=" + selectors.length);
  app.quit();
});
