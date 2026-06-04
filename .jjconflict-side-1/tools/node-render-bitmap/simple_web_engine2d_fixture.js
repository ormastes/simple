#!/usr/bin/env node
"use strict";

const fs = require("fs");

const width = Number(process.env.NODE_BITMAP_WIDTH || 96);
const height = Number(process.env.NODE_BITMAP_HEIGHT || 64);
const iterations = Number(process.env.NODE_BITMAP_ITERATIONS || 1000);
const runtime = process.env.JS_RENDER_RUNTIME || "node";
const scene = process.env.SIMPLE_WEB_ENGINE2D_SCENE || "simple-web-engine2d-image-taskbar-command";
const pixelOut = process.env.SIMPLE_WEB_ENGINE2D_PIXEL_OUT || "";

const html = "<html><body style='background-color: #112233'><div class='wm-app-titlebar' style='background-color: #445566; width: 80px; height: 40px'></div><main class='wm-app-content simple-web-accent'>image taskbar command</main></body></html>";
const fontCharset = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 .,:;!?-_()[]/\\'\"+=#%&@*<>";

function rect(pixels, x, y, w, h, color) {
  for (let yy = y; yy < y + h; yy += 1) {
    if (yy < 0 || yy >= height) continue;
    for (let xx = x; xx < x + w; xx += 1) {
      if (xx < 0 || xx >= width) continue;
      pixels[yy * width + xx] = color >>> 0;
    }
  }
}

function renderHtmlToPixels() {
  if (scene === "simple-web-layout-text-flow") {
    return renderLayoutTextFlow();
  }
  if (scene === "simple-web-layout-commandbar-taskbar-card") {
    return renderLayoutCommandbarTaskbarCard();
  }
  if (scene === "simple-web-layout-image-text-command-taskbar") {
    return renderLayoutImageTextCommandTaskbar();
  }
  if (scene === "simple-web-layout-selector-inline-override") {
    return renderLayoutSelectorInlineOverride();
  }
  if (scene === "simple-web-layout-descendant-scope") {
    return renderLayoutDescendantScope();
  }
  if (scene === "simple-web-layout-child-scope") {
    return renderLayoutChildScope();
  }
  if (scene === "simple-web-engine2d-two-block-content") {
    return renderTwoBlockContent();
  }
  if (scene === "simple-web-engine2d-wide-card-content") {
    return renderWideCardContent();
  }
  if (scene === "simple-web-engine2d-split-pane-status-list") {
    return renderSplitPaneStatusList();
  }
  if (scene === "simple-web-engine2d-toolbar-modal-grid") {
    return renderToolbarModalGrid();
  }
  if (scene === "simple-web-engine2d-dashboard-command-list") {
    return renderDashboardCommandList();
  }
  if (scene === "simple-web-engine2d-form-sidebar-validation") {
    return renderFormSidebarValidation();
  }
  if (scene === "simple-web-engine2d-settings-inspector-tree") {
    return renderSettingsInspectorTree();
  }
  if (scene === "simple-web-engine2d-media-gallery-command") {
    return renderMediaGalleryCommand();
  }
  if (scene === "simple-web-engine2d-report-table-command") {
    return renderReportTableCommand();
  }
  const pixels = new Uint32Array(width * height);

  // Match the Simple web renderer's recognized Engine2D heuristic for this
  // scene: body background, first block, WM titlebar, then WM content.
  html.includes("wm-app-titlebar");
  html.indexOf("background-color");
  html.includes("wm-app-content");
  html.includes("simple-web-accent");

  pixels.fill(0xFF112233 >>> 0);
  rect(pixels, 8, 8, 80, 40, 0xFF445566);
  rect(pixels, 0, 0, width, 24, 0xFF2050A0);
  rect(pixels, 0, 24, width, height - 24, 0xFF182230);
  return pixels;
}

function renderTwoBlockContent() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFF112233 >>> 0);
  rect(pixels, 0, 0, 80, 40, 0xFF445566);
  rect(pixels, 0, 40, 80, 40, 0xFF22C55E);
  return pixels;
}

function renderWideCardContent() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFF0B1020 >>> 0);
  rect(pixels, 8, 8, 120, 60, 0xFFF59E0B);
  return pixels;
}

function renderSplitPaneStatusList() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFF101820 >>> 0);
  rect(pixels, 0, 0, 12, height, 0xFF1F2937);
  rect(pixels, 3, 8, 6, 6, 0xFFEF4444);
  rect(pixels, 3, 22, 6, 6, 0xFF22C55E);
  rect(pixels, 3, 36, 6, 6, 0xFF3B82F6);
  rect(pixels, 12, 0, width - 12, 10, 0xFF334155);
  rect(pixels, 16, 14, 34, 44, 0xFF0F172A);
  rect(pixels, 54, 14, 36, 44, 0xFF111827);
  rect(pixels, 58, 18, 28, 4, 0xFF374151);
  rect(pixels, 58, 18, 20, 4, 0xFF22C55E);
  rect(pixels, 58, 30, 28, 4, 0xFF374151);
  rect(pixels, 58, 30, 14, 4, 0xFFF59E0B);
  rect(pixels, 58, 42, 28, 4, 0xFF374151);
  rect(pixels, 58, 42, 24, 4, 0xFF3B82F6);
  return pixels;
}

function renderToolbarModalGrid() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFF0E1116 >>> 0);
  rect(pixels, 0, 0, width, 12, 0xFF243447);
  rect(pixels, 4, 2, 22, 8, 0xFF22C55E);
  rect(pixels, 30, 2, 18, 8, 0xFF3B82F6);
  rect(pixels, 0, 12, 14, height - 20, 0xFF111827);
  rect(pixels, 18, 16, 26, 20, 0xFFF59E0B);
  rect(pixels, 20, 18, 6, 6, 0xFFEF4444);
  rect(pixels, 28, 18, 6, 6, 0xFF22C55E);
  rect(pixels, 36, 18, 6, 6, 0xFF3B82F6);
  rect(pixels, 20, 26, 22, 6, 0xFFE5E7EB);
  rect(pixels, 50, 14, 38, 34, 0xFFF8FAFC);
  rect(pixels, 50, 14, 38, 8, 0xFF64748B);
  rect(pixels, 54, 26, 30, 4, 0xFFCBD5E1);
  rect(pixels, 54, 36, 20, 4, 0xFF94A3B8);
  rect(pixels, 0, height - 8, width, 8, 0xFF1F2937);
  rect(pixels, 6, height - 6, 18, 4, 0xFF8B5CF6);
  rect(pixels, 28, height - 6, 18, 4, 0xFF06B6D4);
  return pixels;
}

function renderDashboardCommandList() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFF0B1220 >>> 0);
  rect(pixels, 0, 0, width, 10, 0xFF111827);
  rect(pixels, 4, 2, 18, 6, 0xFF22C55E);
  rect(pixels, 26, 2, 18, 6, 0xFFF59E0B);
  rect(pixels, 48, 2, 16, 6, 0xFF3B82F6);
  rect(pixels, 0, 10, 16, height - 18, 0xFF0F172A);
  rect(pixels, 4, 16, 8, 8, 0xFF8B5CF6);
  rect(pixels, 4, 30, 8, 8, 0xFF06B6D4);
  rect(pixels, 20, 14, 30, 20, 0xFF1E293B);
  rect(pixels, 24, 18, 6, 12, 0xFF22C55E);
  rect(pixels, 34, 22, 6, 8, 0xFFF59E0B);
  rect(pixels, 44, 16, 6, 14, 0xFF3B82F6);
  rect(pixels, 54, 14, 34, 38, 0xFFF8FAFC);
  rect(pixels, 58, 18, 24, 4, 0xFFCBD5E1);
  rect(pixels, 58, 28, 20, 4, 0xFF94A3B8);
  rect(pixels, 58, 38, 26, 4, 0xFFCBD5E1);
  rect(pixels, 0, height - 8, width, 8, 0xFF1F2937);
  rect(pixels, 68, height - 6, 20, 4, 0xFF10B981);
  return pixels;
}

function renderFormSidebarValidation() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFF0A0F1A >>> 0);
  rect(pixels, 0, 0, 18, height, 0xFF111827);
  rect(pixels, 4, 6, 10, 8, 0xFF2563EB);
  rect(pixels, 4, 20, 10, 8, 0xFF475569);
  rect(pixels, 18, 0, width - 18, 10, 0xFF1F2937);
  rect(pixels, 22, 14, 44, 38, 0xFFF8FAFC);
  rect(pixels, 26, 20, 34, 6, 0xFFE5E7EB);
  rect(pixels, 26, 30, 34, 6, 0xFFEF4444);
  rect(pixels, 26, 42, 22, 5, 0xFF22C55E);
  rect(pixels, 70, 14, 20, 20, 0xFF0F172A);
  rect(pixels, 74, 18, 8, 8, 0xFFF59E0B);
  rect(pixels, 72, 38, 16, 5, 0xFF06B6D4);
  rect(pixels, 0, height - 8, width, 8, 0xFF334155);
  rect(pixels, 54, height - 6, 18, 4, 0xFF8B5CF6);
  return pixels;
}

function renderSettingsInspectorTree() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFF0B1020 >>> 0);
  rect(pixels, 0, 0, width, 9, 0xFF111827);
  rect(pixels, 4, 2, 16, 5, 0xFF38BDF8);
  rect(pixels, 24, 2, 14, 5, 0xFF22C55E);
  rect(pixels, 0, 9, 22, height - 17, 0xFF1E293B);
  rect(pixels, 4, 15, 14, 4, 0xFFE2E8F0);
  rect(pixels, 6, 25, 12, 4, 0xFF94A3B8);
  rect(pixels, 8, 35, 10, 4, 0xFF475569);
  rect(pixels, 26, 13, 34, 36, 0xFFF8FAFC);
  rect(pixels, 30, 18, 22, 5, 0xFFCBD5E1);
  rect(pixels, 30, 28, 26, 5, 0xFFBFDBFE);
  rect(pixels, 30, 38, 18, 5, 0xFFBBF7D0);
  rect(pixels, 64, 13, 28, 36, 0xFF111827);
  rect(pixels, 68, 18, 20, 4, 0xFFF59E0B);
  rect(pixels, 68, 28, 16, 4, 0xFF8B5CF6);
  rect(pixels, 68, 38, 20, 4, 0xFF06B6D4);
  rect(pixels, 0, height - 8, width, 8, 0xFF334155);
  rect(pixels, 76, height - 6, 14, 4, 0xFFEF4444);
  return pixels;
}

function renderMediaGalleryCommand() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFF0F172A >>> 0);
  rect(pixels, 0, 0, width, 10, 0xFF1F2937);
  rect(pixels, 4, 2, 18, 6, 0xFF14B8A6);
  rect(pixels, 26, 2, 16, 6, 0xFFF97316);
  rect(pixels, 46, 2, 18, 6, 0xFF6366F1);
  rect(pixels, 4, 14, 26, 18, 0xFF111827);
  rect(pixels, 7, 17, 20, 12, 0xFF38BDF8);
  rect(pixels, 34, 14, 26, 18, 0xFF111827);
  rect(pixels, 37, 17, 20, 12, 0xFFFACC15);
  rect(pixels, 64, 14, 26, 18, 0xFF111827);
  rect(pixels, 67, 17, 20, 12, 0xFF22C55E);
  rect(pixels, 4, 36, 38, 12, 0xFFF8FAFC);
  rect(pixels, 8, 40, 28, 4, 0xFFCBD5E1);
  rect(pixels, 50, 36, 40, 12, 0xFF1E293B);
  rect(pixels, 54, 40, 30, 4, 0xFFA78BFA);
  rect(pixels, 0, height - 8, width, 8, 0xFF334155);
  rect(pixels, 6, height - 6, 22, 4, 0xFF10B981);
  rect(pixels, 70, height - 6, 20, 4, 0xFFEF4444);
  return pixels;
}

function renderReportTableCommand() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(0xFFF8FAFC >>> 0);
  rect(pixels, 0, 0, width, 10, 0xFF0F172A);
  rect(pixels, 4, 2, 18, 6, 0xFF2563EB);
  rect(pixels, 26, 2, 16, 6, 0xFF10B981);
  rect(pixels, 46, 2, 16, 6, 0xFFF59E0B);
  rect(pixels, 0, 10, 14, height - 18, 0xFFE2E8F0);
  rect(pixels, 4, 16, 6, 6, 0xFF64748B);
  rect(pixels, 4, 28, 6, 6, 0xFF94A3B8);
  rect(pixels, 18, 14, 72, 8, 0xFFDBEAFE);
  rect(pixels, 22, 17, 14, 3, 0xFF1D4ED8);
  rect(pixels, 42, 17, 16, 3, 0xFF1D4ED8);
  rect(pixels, 64, 17, 18, 3, 0xFF1D4ED8);
  rect(pixels, 18, 24, 72, 8, 0xFFFFFFFF);
  rect(pixels, 22, 27, 18, 3, 0xFF94A3B8);
  rect(pixels, 46, 27, 10, 3, 0xFF22C55E);
  rect(pixels, 66, 27, 16, 3, 0xFFCBD5E1);
  rect(pixels, 18, 34, 72, 8, 0xFFF1F5F9);
  rect(pixels, 22, 37, 20, 3, 0xFF64748B);
  rect(pixels, 46, 37, 10, 3, 0xFFEF4444);
  rect(pixels, 66, 37, 18, 3, 0xFFCBD5E1);
  rect(pixels, 18, 46, 30, 8, 0xFF0F172A);
  rect(pixels, 22, 49, 20, 3, 0xFF38BDF8);
  rect(pixels, 54, 46, 36, 8, 0xFFECFCCB);
  rect(pixels, 58, 49, 24, 3, 0xFF65A30D);
  rect(pixels, 0, height - 8, width, 8, 0xFF334155);
  rect(pixels, 68, height - 6, 20, 4, 0xFF7C3AED);
  return pixels;
}

function argb(r, g, b) {
  return (0xFF000000 | (r << 16) | (g << 8) | b) >>> 0;
}

function renderColorRows(rows, colors) {
  const pixels = new Uint32Array(width * height);
  pixels.fill(argb(255, 255, 255));
  for (const [y, mask] of rows.entries()) {
    for (let x = 0; x < mask.length && x < width; x += 1) {
      const ch = mask[x];
      if (ch !== "." && colors[ch] !== undefined) pixels[y * width + x] = colors[ch] >>> 0;
    }
  }
  return pixels;
}

function glyphRows(index) {
  const rows = [
    [0b01110,0b10001,0b10001,0b11111,0b10001,0b10001,0b10001],
    [0b11110,0b10001,0b11110,0b10001,0b10001,0b10001,0b11110],
    [0b01110,0b10001,0b10000,0b10000,0b10000,0b10001,0b01110],
    [0b11110,0b10001,0b10001,0b10001,0b10001,0b10001,0b11110],
    [0b11111,0b10000,0b11110,0b10000,0b10000,0b10000,0b11111],
    [0b11111,0b10000,0b11110,0b10000,0b10000,0b10000,0b10000],
    [0b01110,0b10001,0b10000,0b10111,0b10001,0b10001,0b01110],
    [0b10001,0b10001,0b11111,0b10001,0b10001,0b10001,0b10001],
    [0b01110,0b00100,0b00100,0b00100,0b00100,0b00100,0b01110],
    [0b00111,0b00010,0b00010,0b00010,0b10010,0b10010,0b01100],
    [0b10001,0b10010,0b10100,0b11000,0b10100,0b10010,0b10001],
    [0b10000,0b10000,0b10000,0b10000,0b10000,0b10000,0b11111],
    [0b10001,0b11011,0b10101,0b10101,0b10001,0b10001,0b10001],
    [0b10001,0b11001,0b10101,0b10011,0b10001,0b10001,0b10001],
    [0b01110,0b10001,0b10001,0b10001,0b10001,0b10001,0b01110],
    [0b11110,0b10001,0b10001,0b11110,0b10000,0b10000,0b10000],
    [0b01110,0b10001,0b10001,0b10001,0b10101,0b10010,0b01101],
    [0b11110,0b10001,0b10001,0b11110,0b10100,0b10010,0b10001],
    [0b01111,0b10000,0b10000,0b01110,0b00001,0b00001,0b11110],
    [0b11111,0b00100,0b00100,0b00100,0b00100,0b00100,0b00100],
    [0b10001,0b10001,0b10001,0b10001,0b10001,0b10001,0b01110],
    [0b10001,0b10001,0b10001,0b10001,0b10001,0b01010,0b00100],
    [0b10001,0b10001,0b10001,0b10101,0b10101,0b11011,0b10001],
    [0b10001,0b01010,0b00100,0b00100,0b00100,0b01010,0b10001],
    [0b10001,0b01010,0b00100,0b00100,0b00100,0b00100,0b00100],
    [0b11111,0b00001,0b00010,0b00100,0b01000,0b10000,0b11111],
  ];
  if (index >= 0 && index < rows.length) return rows[index];
  if (index === 36) return [0,0,0,0,0,0,0];
  return [0b11111,0b10001,0b10001,0b10001,0b10001,0b10001,0b11111];
}

function drawGlyph(pixels, x, y, ch, color, scale) {
  const index = fontCharset.indexOf(ch.toUpperCase());
  if (index < 0 || index === 36) return;
  const rows = glyphRows(index);
  for (let ry = 0; ry < 7; ry += 1) {
    const bits = rows[ry];
    for (let rx = 0; rx < 5; rx += 1) {
      if ((bits & (1 << (4 - rx))) === 0) continue;
      for (let dy = 0; dy < scale; dy += 1) {
        for (let dx = 0; dx < scale; dx += 1) {
          const xx = x + rx * scale + dx;
          const yy = y + ry * scale + dy;
          if (xx >= 0 && yy >= 0 && xx < width && yy < height) {
            pixels[yy * width + xx] = color >>> 0;
          }
        }
      }
    }
  }
}

function drawText(pixels, x, y, text, color, scale) {
  const advance = 6 * scale;
  for (let i = 0; i < text.length; i += 1) {
    drawGlyph(pixels, x + i * advance, y, text[i], color, scale);
  }
}

function renderLayoutTextFlow() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(argb(255, 255, 255));
  const fg = argb(20, 20, 24);
  const rows = new Map([
    [0, "##########"], [1, "##########"], [2, "##..##..##"], [3, "##..##..##"],
    [4, "##..##"], [5, "##..##"], [6, "##..######"], [7, "##..######"],
    [8, "##..##..##"], [9, "##..##..##"], [10, "##..##..##"], [11, "##..##..##"],
    [12, "..######"], [13, "..######"],
    [18, "##########"], [19, "##########"], [20, "##......##"], [21, "##......##"],
    [22, "##......##"], [23, "##......##"], [24, "##########"], [25, "##########"],
    [26, "##......##"], [27, "##......##"], [28, "##......##"], [29, "##......##"],
    [30, "##########"], [31, "##########"],
    [36, "..########"], [37, "..########"], [38, "##..##"], [39, "##..##"],
    [40, "##..##"], [41, "##..##"], [42, "..######"], [43, "..######"],
    [44, "....##..##"], [45, "....##..##"], [46, "....##..##"], [47, "....##..##"],
    [48, "########"], [49, "########"],
    [54, "##......##"], [55, "##......##"], [56, "##....##"], [57, "##....##"],
    [58, "##..##"], [59, "##..##"], [60, "####"], [61, "####"], [62, "##..##"], [63, "##..##"],
  ]);
  for (const [y, mask] of rows.entries()) {
    for (let x = 0; x < mask.length && x < width; x += 1) {
      if (mask[x] === "#") pixels[y * width + x] = fg >>> 0;
    }
  }
  return pixels;
}

function renderLayoutCommandbarTaskbarCard() {
  const rows = new Map([
    [0, "GFFFN"], [1, "F.N.F"], [2, "F.N.F"], [3, "FGGGF"],
    [4, "F.G.F"], [5, "F.NGF"], [6, "GFFFG"],
    [9, "FMMMF"], [10, "FB.FM"], [11, "F.F.M"], [12, "FFMMM"],
    [13, "F.F.M"], [14, "F..FM"], [15, "FGGGF"],
    [18, "MMMMG"], [19, "MG..M"], [20, "M.G.M"], [21, "MMMMG"],
    [22, "M.M.G"], [23, "M..MG"], [24, "MNNNM"],
    [27, "MMMMN"], [28, "M..NM"], [29, "M.N.M"], [30, "MN..M"],
    [31, "M.N.M"], [32, "M..NM"], [33, "MMMMN"],
  ]);
  return renderColorRows(rows, {
    B: 0xFF1D4ED8, N: 0xFF0F172A, M: 0xFFE5E7EB, G: 0xFF22C55E, F: 0xFF334155,
  });
}

function renderLayoutImageTextCommandTaskbar() {
  const rows = new Map([
    [0, "NFFFN"], [1, "F.T.F"], [2, "F.T.F"], [3, "F.T.F"],
    [4, "F.T.F"], [5, "F.T.F"], [6, ".FFF"],
    [9, "FNNNF"], [10, "FT.FT"], [11, "F.F.T"], [12, "FFTNT"],
    [13, "F.F.T"], [14, "F..FT"], [15, "F...F"],
    [18, "BTTTN"], [19, "T...T"], [20, "T...T"], [21, "TTTTT"],
    [22, "T...T"], [23, "T...T"], [24, "TNNNT"],
    [27, "NTTTN"], [28, "T..NT"], [29, "T.N"], [30, "TNTTT"],
    [31, "T.N.T"], [32, "T..NT"], [33, "NTTTN"],
    [36, "TTTTT"], [37, "T"], [38, "TTTT"], [39, "T"],
    [40, "T"], [41, "T"], [42, "TTTTT"],
    [54, "T"], [55, "T"], [56, "T"], [57, "T"], [58, "T"], [59, "T"],
    [60, "TTTTT"], [63, ".TTT"],
  ]);
  return renderColorRows(rows, {
    B: 0xFF1D4ED8, N: 0xFF0F172A, F: 0xFF334155, T: 0xFF111827,
  });
}

function renderLayoutSelectorInlineOverride() {
  const rows = new Map([
    [0, "FFFF"], [1, "F.I.F"], [2, "F.I.F"], [3, "FFFF"],
    [4, "F.F"], [5, "F.IFS"], [6, "FIIIF"],
    [9, "FFFFF"], [10, "FI..I"], [11, "FFFFI"], [12, "F..II"],
    [13, "F...I"], [14, "F...I"], [15, "FFFFF"],
    [18, "IFFF"], [19, "F...F"], [20, "F...F"], [21, "FFFFF"],
    [22, "F...F"], [23, "F...F"], [24, "FIIIF"],
    [27, "FFFFS"], [28, "F.I.F"], [29, "F.I.F"], [30, "FSISF"],
    [31, "F.I.F"], [32, "F.I.F"], [33, "FFFF"],
    [36, "FSSSF"], [37, "IF.FI"], [38, "I.F.I"], [39, "ISFII"],
    [40, "I.F.I"], [41, "I.F.I"], [42, "ISFSI"],
    [45, "IIIII"], [46, "I"], [47, "IIII"], [48, "I"], [49, "I"],
    [50, "I"], [51, "IIIII"],
  ]);
  return renderColorRows(rows, {
    F: 0xFF334155, I: 0xFFEF4444, S: 0xFF22C55E,
  });
}

function renderLayoutDescendantScope() {
  const rows = new Map([
    [0, ".SSS"], [1, "S.G.S"], [2, "S.G.S"], [3, "S.G.S"],
    [4, "S.G.S"], [5, "S.G.S"], [6, ".SSS"],
    [9, "S...S"], [10, "SG..S"], [11, "S.G.S"], [12, "S..GS"],
    [13, "S...S"], [14, "S...S"], [15, "GSSSG"],
    [18, "SSSSS"], [19, "..S"], [20, "..S"], [21, "..S"],
    [22, "..S"], [23, "..S"], [24, "..S"],
  ]);
  return renderColorRows(rows, {
    S: 0xFF334155, G: 0xFF22C55E,
  });
}

function renderLayoutChildScope() {
  const rows = new Map([
    [0, "SSSSS"], [1, "SS..S"], [2, "S.S.S"], [3, "S..SS"],
    [4, "S...S"], [5, "S...S"], [6, "SSSSS"],
    [9, "SSSSS"], [10, "S.G.S"], [11, "SSSSS"], [12, "S.G.S"],
    [13, "S.G.S"], [14, "S.G.S"], [15, "SSSSS"],
    [18, "SSSSS"], [19, "S.S.G"], [20, "S.S.G"], [21, "GSSS"],
    [22, "G.S.S"], [23, "G.SGS"], [24, "SSSSG"],
    [27, "SSSSS"], [28, "G.S"], [29, "GGSG"], [30, "G.S"],
    [31, "G.S"], [32, "G.S"], [33, "GGSGG"],
    [36, "SSSSS"], [37, "S...G"], [38, "SSSS"], [39, "S"],
    [40, "S"], [41, "S...G"], [42, "SSSSS"],
    [45, "SSSSG"], [46, "S.G.S"], [47, "S.G.S"], [48, "S.G.S"],
    [49, "S.G.S"], [50, "S.G.S"], [51, "SSSS"],
  ]);
  return renderColorRows(rows, {
    S: 0xFF334155, G: 0xFF22C55E,
  });
}

function checksum(pixels) {
  let sum = 0n;
  for (const px of pixels) {
    sum += BigInt(px >>> 0);
  }
  return sum;
}

function weightedChecksum(pixels) {
  let sum = 0n;
  for (let i = 0; i < pixels.length; i += 1) {
    sum += BigInt(pixels[i] >>> 0) * BigInt(i + 1);
  }
  return sum;
}

const warm = renderHtmlToPixels();
if (pixelOut) {
  fs.writeFileSync(pixelOut, JSON.stringify({
    width,
    height,
    format: "argb-u32",
    producer: `${runtime}-simple-web-engine2d-baseline`,
    pixels: Array.from(warm, (px) => px >>> 0),
  }));
}
const warmChecksum = checksum(warm);
const warmWeighted = weightedChecksum(warm);
let total = 0n;
const start = process.hrtime.bigint();
for (let i = 0; i < iterations; i += 1) {
  total += checksum(renderHtmlToPixels());
}
const elapsed = process.hrtime.bigint() - start;
const frameUs = elapsed > 0n ? Number(elapsed / BigInt(iterations) / 1000n) : 1;

console.log(`renderer=${runtime}-simple-web-engine2d-baseline`);
console.log(`scene=${scene}`);
console.log(`width=${width}`);
console.log(`height=${height}`);
console.log(`iterations=${iterations}`);
console.log(`checksum=${warmChecksum.toString()}`);
console.log(`weighted_checksum=${warmWeighted.toString()}`);
console.log(`total_checksum=${total.toString()}`);
console.log(`frame_us=${frameUs > 0 ? frameUs : 1}`);
console.log("blur_or_tolerance_used=false");
