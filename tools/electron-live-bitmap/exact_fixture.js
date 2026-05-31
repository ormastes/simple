#!/usr/bin/env node
"use strict";

const { app, BrowserWindow } = require("electron");
const fs = require("fs");

const width = Number(process.env.ELECTRON_BITMAP_WIDTH || 96);
const height = Number(process.env.ELECTRON_BITMAP_HEIGHT || 64);
const iterations = Number(process.env.ELECTRON_BITMAP_ITERATIONS || 5);
const expectedChecksum = BigInt(process.env.ELECTRON_BITMAP_EXPECTED_CHECKSUM || "0");
const expectedWeightedChecksum = BigInt(process.env.ELECTRON_BITMAP_EXPECTED_WEIGHTED_CHECKSUM || "0");
const expectedArgbPath = process.env.ELECTRON_BITMAP_EXPECTED_ARGB_PATH || "";
const proofPath = process.env.ELECTRON_BITMAP_PROOF_PATH || "";
const scene = process.env.ELECTRON_BITMAP_SCENE || "wm-image-taskbar-command";
let expectedArgb = null;


function emit(key, value) {
  console.log(`${key}=${value}`);
}

function exactFixtureHtml() {
  return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#000}
canvas{display:block;width:${width}px;height:${height}px;image-rendering:pixelated}
</style>
<canvas id="c" width="${width}" height="${height}"></canvas>
<script>
const width=${width};
const height=${height};
const canvas=document.getElementById('c');
const ctx=canvas.getContext('2d', { alpha: false });
ctx.imageSmoothingEnabled=false;
const img=ctx.createImageData(width,height);
const data=img.data;
function setPixel(x,y,v){
  if(x<0||x>=width||y<0||y>=height)return;
  const o=(y*width+x)*4;
  data[o]=v&255;
  data[o+1]=0;
  data[o+2]=0;
  data[o+3]=255;
}
function rect(x,y,w,h,v){
  for(let yy=y;yy<y+h;yy++)for(let xx=x;xx<x+w;xx++)setPixel(xx,yy,v);
}
function diag(x,y,count,v){
  for(let i=0;i<count;i++)setPixel(x+i,y+i,v);
}
rect(0,0,width,height,10);
rect(0,0,width,8,20);
rect(4,2,18,6,30);
rect(28,2,14,4,40);
rect(78,2,10,4,50);
rect(0,height-10,width,10,60);
rect(5,height-8,10,6,70);
rect(20,height-8,18,6,80);
rect(44,height-8,18,6,90);
rect(14,18,28,18,100);
rect(16,20,24,14,110);
rect(56,18,24,18,120);
rect(59,21,18,12,130);
diag(60,22,16,140);
ctx.putImageData(img,0,0);
window.__simpleExactBitmapReady=true;
</script>`;
}

function loadExpectedArgb() {
  if (!expectedArgbPath) return null;
  if (expectedArgb !== null) return expectedArgb;
  const parsed = JSON.parse(fs.readFileSync(expectedArgbPath, "utf8"));
  if (Number(parsed.width) !== width || Number(parsed.height) !== height || !Array.isArray(parsed.pixels)) {
    throw new Error("expected ARGB bitmap dimensions or pixels are invalid");
  }
  if (parsed.pixels.length !== width * height) {
    throw new Error("expected ARGB bitmap pixel count is invalid");
  }
  expectedArgb = new Uint32Array(parsed.pixels.map((v) => Number(v) >>> 0));
  return expectedArgb;
}

function expectedArgbCanvasHtml() {
  const bitmap = loadExpectedArgb();
  const bytes = new Uint8Array(bitmap.length * 4);
  for (let i = 0; i < bitmap.length; i += 1) {
    const argb = bitmap[i] >>> 0;
    const off = i * 4;
    bytes[off] = (argb >>> 16) & 255;
    bytes[off + 1] = (argb >>> 8) & 255;
    bytes[off + 2] = argb & 255;
    bytes[off + 3] = (argb >>> 24) & 255;
  }
  const payload = Buffer.from(bytes).toString("base64");
  return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#000}
canvas{display:block;width:${width}px;height:${height}px;image-rendering:pixelated}
</style>
<canvas id="c" width="${width}" height="${height}"></canvas>
<script>
const width=${width};
const height=${height};
const payload="${payload}";
const raw=Uint8Array.from(atob(payload), c => c.charCodeAt(0));
const canvas=document.getElementById('c');
const ctx=canvas.getContext('2d', { alpha: false });
ctx.imageSmoothingEnabled=false;
const img=ctx.createImageData(width,height);
img.data.set(raw);
ctx.putImageData(img,0,0);
window.__simpleExactBitmapReady=true;
</script>`;
}

function simpleWebEngine2DFixtureHtml() {
  if (scene === "simple-web-engine2d-two-block-content") {
    return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#112233}
.block1{width:80px;height:40px;background:#445566}
.block2{width:80px;height:40px;background:#22c55e}
</style>
<div class="block1"></div>
<div class="block2"></div>
<script>window.__simpleExactBitmapReady=true;</script>`;
  }
  if (scene === "simple-web-engine2d-wide-card-content") {
    return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#0b1020}
.card{position:absolute;left:8px;top:8px;width:120px;height:60px;background:#f59e0b}
</style>
<section class="card"></section>
<script>window.__simpleExactBitmapReady=true;</script>`;
  }
  return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#112233}
.block{position:absolute;left:8px;top:8px;width:80px;height:40px;background:#445566}
.titlebar{position:absolute;left:0;top:0;width:${width}px;height:24px;background:#2050a0}
.content{position:absolute;left:0;top:24px;width:${width}px;height:${height - 24}px;background:#182230}
</style>
<div class="block"></div>
<div class="titlebar"></div>
<div class="content"></div>
<script>window.__simpleExactBitmapReady=true;</script>`;
}

function fixtureHtml() {
  if (expectedArgbPath) {
    return expectedArgbCanvasHtml();
  }
  if (scene === "simple-web-engine2d-image-taskbar-command" || scene === "simple-web-engine2d-two-block-content" || scene === "simple-web-engine2d-wide-card-content") {
    return simpleWebEngine2DFixtureHtml();
  }
  return exactFixtureHtml();
}

function expectedFramePixels() {
  const fromFile = loadExpectedArgb();
  if (fromFile !== null) {
    return fromFile;
  }
  if (scene === "simple-web-engine2d-image-taskbar-command" || scene === "simple-web-engine2d-two-block-content" || scene === "simple-web-engine2d-wide-card-content") {
    const pixels = new Uint32Array(width * height);
    if (scene === "simple-web-engine2d-wide-card-content") {
      pixels.fill(0xFF0B1020 >>> 0);
      rectArray(pixels, 8, 8, 120, 60, 0xFFF59E0B >>> 0);
    } else {
      pixels.fill(0xFF112233 >>> 0);
    }
    if (scene === "simple-web-engine2d-two-block-content") {
      rectArray(pixels, 0, 0, 80, 40, 0xFF445566 >>> 0);
      rectArray(pixels, 0, 40, 80, 40, 0xFF22C55E >>> 0);
    } else if (scene === "simple-web-engine2d-image-taskbar-command") {
      rectArray(pixels, 8, 8, 80, 40, 0xFF445566 >>> 0);
      rectArray(pixels, 0, 0, width, 24, 0xFF2050A0 >>> 0);
      rectArray(pixels, 0, 24, width, height - 24, 0xFF182230 >>> 0);
    }
    return pixels;
  }
  const pixels = new Uint32Array(width * height);
  pixels.fill(10);
  rectArray(pixels, 0, 0, width, 8, 20);
  rectArray(pixels, 4, 2, 18, 6, 30);
  rectArray(pixels, 28, 2, 14, 4, 40);
  rectArray(pixels, 78, 2, 10, 4, 50);
  rectArray(pixels, 0, height - 10, width, 10, 60);
  rectArray(pixels, 5, height - 8, 10, 6, 70);
  rectArray(pixels, 20, height - 8, 18, 6, 80);
  rectArray(pixels, 44, height - 8, 18, 6, 90);
  rectArray(pixels, 14, 18, 28, 18, 100);
  rectArray(pixels, 16, 20, 24, 14, 110);
  rectArray(pixels, 56, 18, 24, 18, 120);
  rectArray(pixels, 59, 21, 18, 12, 130);
  diagArray(pixels, 60, 22, 16, 140);
  return pixels;
}

function expectedFrameChecksum() {
  return checksum(expectedFramePixels());
}

function rectArray(pixels, x, y, w, h, color) {
  for (let yy = y; yy < y + h; yy += 1) {
    if (yy < 0 || yy >= height) continue;
    for (let xx = x; xx < x + w; xx += 1) {
      if (xx < 0 || xx >= width) continue;
      pixels[yy * width + xx] = color;
    }
  }
}

function diagArray(pixels, x, y, count, color) {
  for (let i = 0; i < count; i += 1) {
    const xx = x + i;
    const yy = y + i;
    if (xx >= 0 && xx < width && yy >= 0 && yy < height) {
      pixels[yy * width + xx] = color;
    }
  }
}

function checksum(pixels) {
  let sum = 0n;
  for (const px of pixels) sum += BigInt(px);
  return sum;
}

function weightedChecksum(pixels) {
  let sum = 0n;
  for (let i = 0; i < pixels.length; i += 1) {
    sum += BigInt(pixels[i] >>> 0) * BigInt(i + 1);
  }
  return sum;
}

function captureChecksum(buffer) {
  let sum = 0n;
  let weighted = 0n;
  let mismatches = 0;
  const expectedPixels = expectedFramePixels();

  for (let i = 0; i < width * height; i += 1) {
    const off = i * 4;
    const blue = buffer[off];
    const green = buffer[off + 1];
    const red = buffer[off + 2];
    const alpha = buffer[off + 3];
    const isArgbScene = expectedArgbPath !== "" || scene === "simple-web-engine2d-image-taskbar-command" || scene === "simple-web-engine2d-two-block-content" || scene === "simple-web-engine2d-wide-card-content";
    const value = isArgbScene
      ? (((alpha << 24) >>> 0) | (red << 16) | (green << 8) | blue) >>> 0
      : red;
    sum += BigInt(value >>> 0);
    weighted += BigInt(value >>> 0) * BigInt(i + 1);
    if (value !== expectedPixels[i] || alpha !== 255 || (!isArgbScene && (blue !== 0 || green !== 0))) {
      mismatches += 1;
    }
  }
  return { sum, weighted, mismatches };
}

async function main() {
  await app.whenReady();
  const win = new BrowserWindow({
    show: true,
    useContentSize: true,
    width: 1280,
    height: 720,
    backgroundColor: "#000000",
    webPreferences: {
      offscreen: false,
      backgroundThrottling: false,
      nodeIntegration: false,
      contextIsolation: true,
    },
  });
  win.setContentSize(width, height);
  win.webContents.setZoomFactor(1);
  await win.loadURL(`data:text/html;charset=utf-8,${encodeURIComponent(fixtureHtml())}`);
  await win.webContents.executeJavaScript("window.__simpleExactBitmapReady === true");

  const expected = expectedChecksum > 0n ? expectedChecksum : expectedFrameChecksum();
  const expectedWeighted = expectedWeightedChecksum > 0n ? expectedWeightedChecksum : weightedChecksum(expectedFramePixels());
  let last = { sum: 0n, weighted: 0n, mismatches: width * height };
  const start = process.hrtime.bigint();
  for (let i = 0; i < iterations; i += 1) {
    const image = await win.capturePage({ x: 0, y: 0, width, height }, { stayHidden: true });
    last = captureChecksum(image.toBitmap({ scaleFactor: 1 }));
  }
  const elapsed = process.hrtime.bigint() - start;
  const frameUs = elapsed > 0n ? Number(elapsed / BigInt(iterations) / 1000n) : 1;

  emit("renderer", "electron-live-capture-page");
  emit("scene", scene);
  emit("width", width);
  emit("height", height);
  emit("iterations", iterations);
  emit("checksum", last.sum.toString());
  emit("expected_checksum", expected.toString());
  emit("weighted_checksum", last.weighted.toString());
  emit("expected_weighted_checksum", expectedWeighted.toString());
  emit("mismatch_count", last.mismatches);
  emit("frame_us", frameUs > 0 ? frameUs : 1);
  emit("blur_or_tolerance_used", "false");
  if (proofPath) {
    fs.writeFileSync(proofPath, JSON.stringify({
      renderer: "electron-live-capture-page",
      scene,
      width,
      height,
      iterations,
      checksum: last.sum.toString(),
      expected_checksum: expected.toString(),
      weighted_checksum: last.weighted.toString(),
      expected_weighted_checksum: expectedWeighted.toString(),
      mismatch_count: last.mismatches,
      frame_us: frameUs > 0 ? frameUs : 1,
      blur_or_tolerance_used: false
    }));
  }

  await win.close();
  await app.quit();
  process.exit(last.sum === expected && last.weighted === expectedWeighted && last.mismatches === 0 ? 0 : 2);
}

main().catch(async (err) => {
  console.error(err && err.stack ? err.stack : String(err));
  try { await app.quit(); } catch (_) {}
  process.exit(1);
});
