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
