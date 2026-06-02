#!/usr/bin/env node
"use strict";

const { app, BrowserWindow } = require("electron");
const fs = require("fs");

// Capture color exactness (no-tolerance policy):
// A windowed BrowserWindow.capturePage() is composited through the OS display
// server, which applies the monitor's ICC/color profile and shifts solid colors
// a few levels away from the raw CSS values (e.g. macOS: R+4, B-1) — breaking
// exact pixel equality. Offscreen rendering (webPreferences.offscreen=true,
// captured below) renders to an in-process buffer in the page's own color space,
// bypassing the display compositor, so captured pixels equal the CSS colors
// exactly and deterministically. Pinning the color profile to sRGB reinforces
// this. Must be set before app is ready.
app.commandLine.appendSwitch("force-color-profile", "srgb");

const width = Number(process.env.ELECTRON_BITMAP_WIDTH || 96);
const height = Number(process.env.ELECTRON_BITMAP_HEIGHT || 64);
const iterations = Number(process.env.ELECTRON_BITMAP_ITERATIONS || 5);
const expectedChecksum = BigInt(process.env.ELECTRON_BITMAP_EXPECTED_CHECKSUM || "0");
const expectedWeightedChecksum = BigInt(process.env.ELECTRON_BITMAP_EXPECTED_WEIGHTED_CHECKSUM || "0");
const expectedArgbPath = process.env.ELECTRON_BITMAP_EXPECTED_ARGB_PATH || "";
const capturedArgbPath = process.env.ELECTRON_BITMAP_CAPTURED_ARGB_PATH || "";
const proofPath = process.env.ELECTRON_BITMAP_PROOF_PATH || "";
const htmlPath = process.env.ELECTRON_BITMAP_HTML_PATH || "";
const scene = process.env.ELECTRON_BITMAP_SCENE || "wm-image-taskbar-command";
let expectedArgb = null;


function emit(key, value) {
  console.log(`${key}=${value}`);
}

function htmlFileFixtureHtml() {
  const body = fs.readFileSync(htmlPath, "utf8");
  const readyScript = `<script>
(function(){
  async function waitForExactBitmapReady(){
    if (document.fonts && document.fonts.ready) {
      try { await document.fonts.ready; } catch (_) {}
    }
    const images = Array.from(document.images || []);
    await Promise.all(images.map(async (img) => {
      if (img.complete) return;
      if (img.decode) {
        try { await img.decode(); return; } catch (_) {}
      }
      await new Promise((resolve) => {
        img.addEventListener("load", resolve, { once: true });
        img.addEventListener("error", resolve, { once: true });
      });
    }));
    await new Promise((resolve) => requestAnimationFrame(() => requestAnimationFrame(resolve)));
    window.__simpleExactBitmapReady=true;
  }
  if (document.readyState === "complete") {
    waitForExactBitmapReady();
  } else {
    window.addEventListener("load", waitForExactBitmapReady, { once: true });
  }
})();
</script>`;
  if (body.includes("__simpleExactBitmapReady")) return body;
  const closeBody = body.lastIndexOf("</body>");
  if (closeBody >= 0) {
    return `${body.substring(0, closeBody)}${readyScript}\n${body.substring(closeBody)}`;
  }
  return `${body}\n${readyScript}`;
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
  if (scene === "simple-web-engine2d-split-pane-status-list") {
    return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#101820}
.nav{position:absolute;left:0;top:0;width:12px;height:${height}px;background:#1f2937}
.i1{position:absolute;left:3px;top:8px;width:6px;height:6px;background:#ef4444}
.i2{position:absolute;left:3px;top:22px;width:6px;height:6px;background:#22c55e}
.i3{position:absolute;left:3px;top:36px;width:6px;height:6px;background:#3b82f6}
.top{position:absolute;left:12px;top:0;width:${width - 12}px;height:10px;background:#334155}
.pane1{position:absolute;left:16px;top:14px;width:34px;height:44px;background:#0f172a}
.pane2{position:absolute;left:54px;top:14px;width:36px;height:44px;background:#111827}
.bar{position:absolute;left:58px;width:28px;height:4px;background:#374151}
.p1{position:absolute;left:58px;top:18px;width:20px;height:4px;background:#22c55e}
.p2{position:absolute;left:58px;top:30px;width:14px;height:4px;background:#f59e0b}
.p3{position:absolute;left:58px;top:42px;width:24px;height:4px;background:#3b82f6}
</style>
<div class="nav"></div><div class="i1"></div><div class="i2"></div><div class="i3"></div>
<div class="top"></div><div class="pane1"></div><div class="pane2"></div>
<div class="bar" style="top:18px"></div><div class="p1"></div>
<div class="bar" style="top:30px"></div><div class="p2"></div>
<div class="bar" style="top:42px"></div><div class="p3"></div>
<script>window.__simpleExactBitmapReady=true;</script>`;
  }
  if (scene === "simple-web-engine2d-toolbar-modal-grid") {
    return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#0e1116}
.toolbar{position:absolute;left:0;top:0;width:${width}px;height:12px;background:#243447}
.cmd1{position:absolute;left:4px;top:2px;width:22px;height:8px;background:#22c55e}
.cmd2{position:absolute;left:30px;top:2px;width:18px;height:8px;background:#3b82f6}
.rail{position:absolute;left:0;top:12px;width:14px;height:${height - 20}px;background:#111827}
.image{position:absolute;left:18px;top:16px;width:26px;height:20px;background:#f59e0b}
.sw1{position:absolute;left:20px;top:18px;width:6px;height:6px;background:#ef4444}
.sw2{position:absolute;left:28px;top:18px;width:6px;height:6px;background:#22c55e}
.sw3{position:absolute;left:36px;top:18px;width:6px;height:6px;background:#3b82f6}
.caption{position:absolute;left:20px;top:26px;width:22px;height:6px;background:#e5e7eb}
.modal{position:absolute;left:50px;top:14px;width:38px;height:34px;background:#f8fafc}
.modalhead{position:absolute;left:50px;top:14px;width:38px;height:8px;background:#64748b}
.bar1{position:absolute;left:54px;top:26px;width:30px;height:4px;background:#cbd5e1}
.bar2{position:absolute;left:54px;top:36px;width:20px;height:4px;background:#94a3b8}
.taskbar{position:absolute;left:0;top:${height - 8}px;width:${width}px;height:8px;background:#1f2937}
.task1{position:absolute;left:6px;top:${height - 6}px;width:18px;height:4px;background:#8b5cf6}
.task2{position:absolute;left:28px;top:${height - 6}px;width:18px;height:4px;background:#06b6d4}
</style>
<div class="toolbar"></div><div class="cmd1"></div><div class="cmd2"></div><div class="rail"></div>
<div class="image"></div><div class="sw1"></div><div class="sw2"></div><div class="sw3"></div><div class="caption"></div>
<div class="modal"></div><div class="modalhead"></div><div class="bar1"></div><div class="bar2"></div>
<div class="taskbar"></div><div class="task1"></div><div class="task2"></div>
<script>window.__simpleExactBitmapReady=true;</script>`;
  }
  if (scene === "simple-web-engine2d-dashboard-command-list") {
    return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#0b1220}
.top{position:absolute;left:0;top:0;width:${width}px;height:10px;background:#111827}
.cmd1{position:absolute;left:4px;top:2px;width:18px;height:6px;background:#22c55e}
.cmd2{position:absolute;left:26px;top:2px;width:18px;height:6px;background:#f59e0b}
.cmd3{position:absolute;left:48px;top:2px;width:16px;height:6px;background:#3b82f6}
.rail{position:absolute;left:0;top:10px;width:16px;height:${height - 18}px;background:#0f172a}
.icon1{position:absolute;left:4px;top:16px;width:8px;height:8px;background:#8b5cf6}
.icon2{position:absolute;left:4px;top:30px;width:8px;height:8px;background:#06b6d4}
.chart{position:absolute;left:20px;top:14px;width:30px;height:20px;background:#1e293b}
.bar1{position:absolute;left:24px;top:18px;width:6px;height:12px;background:#22c55e}
.bar2{position:absolute;left:34px;top:22px;width:6px;height:8px;background:#f59e0b}
.bar3{position:absolute;left:44px;top:16px;width:6px;height:14px;background:#3b82f6}
.list{position:absolute;left:54px;top:14px;width:34px;height:38px;background:#f8fafc}
.row1{position:absolute;left:58px;top:18px;width:24px;height:4px;background:#cbd5e1}
.row2{position:absolute;left:58px;top:28px;width:20px;height:4px;background:#94a3b8}
.row3{position:absolute;left:58px;top:38px;width:26px;height:4px;background:#cbd5e1}
.taskbar{position:absolute;left:0;top:${height - 8}px;width:${width}px;height:8px;background:#1f2937}
.status{position:absolute;left:68px;top:${height - 6}px;width:20px;height:4px;background:#10b981}
</style>
<div class="top"></div><div class="cmd1"></div><div class="cmd2"></div><div class="cmd3"></div>
<div class="rail"></div><div class="icon1"></div><div class="icon2"></div>
<div class="chart"></div><div class="bar1"></div><div class="bar2"></div><div class="bar3"></div>
<div class="list"></div><div class="row1"></div><div class="row2"></div><div class="row3"></div>
<div class="taskbar"></div><div class="status"></div>
<script>window.__simpleExactBitmapReady=true;</script>`;
  }
  if (scene === "simple-web-engine2d-form-sidebar-validation") {
    return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#0a0f1a}
.sidebar{position:absolute;left:0;top:0;width:18px;height:${height}px;background:#111827}
.nav1{position:absolute;left:4px;top:6px;width:10px;height:8px;background:#2563eb}
.nav2{position:absolute;left:4px;top:20px;width:10px;height:8px;background:#475569}
.header{position:absolute;left:18px;top:0;width:${width - 18}px;height:10px;background:#1f2937}
.form{position:absolute;left:22px;top:14px;width:44px;height:38px;background:#f8fafc}
.input{position:absolute;left:26px;top:20px;width:34px;height:6px;background:#e5e7eb}
.error{position:absolute;left:26px;top:30px;width:34px;height:6px;background:#ef4444}
.valid{position:absolute;left:26px;top:42px;width:22px;height:5px;background:#22c55e}
.preview{position:absolute;left:70px;top:14px;width:20px;height:20px;background:#0f172a}
.avatar{position:absolute;left:74px;top:18px;width:8px;height:8px;background:#f59e0b}
.chip{position:absolute;left:72px;top:38px;width:16px;height:5px;background:#06b6d4}
.taskbar{position:absolute;left:0;top:${height - 8}px;width:${width}px;height:8px;background:#334155}
.status{position:absolute;left:54px;top:${height - 6}px;width:18px;height:4px;background:#8b5cf6}
</style>
<div class="sidebar"></div><div class="nav1"></div><div class="nav2"></div><div class="header"></div>
<div class="form"></div><div class="input"></div><div class="error"></div><div class="valid"></div>
<div class="preview"></div><div class="avatar"></div><div class="chip"></div>
<div class="taskbar"></div><div class="status"></div>
<script>window.__simpleExactBitmapReady=true;</script>`;
  }
  if (scene === "simple-web-engine2d-settings-inspector-tree") {
    return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#0b1020}
.top{position:absolute;left:0;top:0;width:${width}px;height:9px;background:#111827}
.cmd1{position:absolute;left:4px;top:2px;width:16px;height:5px;background:#38bdf8}
.cmd2{position:absolute;left:24px;top:2px;width:14px;height:5px;background:#22c55e}
.tree{position:absolute;left:0;top:9px;width:22px;height:${height - 17}px;background:#1e293b}
.node1{position:absolute;left:4px;top:15px;width:14px;height:4px;background:#e2e8f0}
.node2{position:absolute;left:6px;top:25px;width:12px;height:4px;background:#94a3b8}
.node3{position:absolute;left:8px;top:35px;width:10px;height:4px;background:#475569}
.settings{position:absolute;left:26px;top:13px;width:34px;height:36px;background:#f8fafc}
.row1{position:absolute;left:30px;top:18px;width:22px;height:5px;background:#cbd5e1}
.row2{position:absolute;left:30px;top:28px;width:26px;height:5px;background:#bfdbfe}
.row3{position:absolute;left:30px;top:38px;width:18px;height:5px;background:#bbf7d0}
.inspector{position:absolute;left:64px;top:13px;width:28px;height:36px;background:#111827}
.prop1{position:absolute;left:68px;top:18px;width:20px;height:4px;background:#f59e0b}
.prop2{position:absolute;left:68px;top:28px;width:16px;height:4px;background:#8b5cf6}
.prop3{position:absolute;left:68px;top:38px;width:20px;height:4px;background:#06b6d4}
.taskbar{position:absolute;left:0;top:${height - 8}px;width:${width}px;height:8px;background:#334155}
.alert{position:absolute;left:76px;top:${height - 6}px;width:14px;height:4px;background:#ef4444}
</style>
<div class="top"></div><div class="cmd1"></div><div class="cmd2"></div>
<div class="tree"></div><div class="node1"></div><div class="node2"></div><div class="node3"></div>
<div class="settings"></div><div class="row1"></div><div class="row2"></div><div class="row3"></div>
<div class="inspector"></div><div class="prop1"></div><div class="prop2"></div><div class="prop3"></div>
<div class="taskbar"></div><div class="alert"></div>
	<script>window.__simpleExactBitmapReady=true;</script>`;
  }
  if (scene === "simple-web-engine2d-media-gallery-command") {
    return `<!doctype html>
	<meta charset="utf-8">
	<style>
	html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#0f172a}
	.top{position:absolute;left:0;top:0;width:${width}px;height:10px;background:#1f2937}
	.cmd1{position:absolute;left:4px;top:2px;width:18px;height:6px;background:#14b8a6}
	.cmd2{position:absolute;left:26px;top:2px;width:16px;height:6px;background:#f97316}
	.cmd3{position:absolute;left:46px;top:2px;width:18px;height:6px;background:#6366f1}
	.tile1{position:absolute;left:4px;top:14px;width:26px;height:18px;background:#111827}
	.img1{position:absolute;left:7px;top:17px;width:20px;height:12px;background:#38bdf8}
	.tile2{position:absolute;left:34px;top:14px;width:26px;height:18px;background:#111827}
	.img2{position:absolute;left:37px;top:17px;width:20px;height:12px;background:#facc15}
	.tile3{position:absolute;left:64px;top:14px;width:26px;height:18px;background:#111827}
	.img3{position:absolute;left:67px;top:17px;width:20px;height:12px;background:#22c55e}
	.meta{position:absolute;left:4px;top:36px;width:38px;height:12px;background:#f8fafc}
	.metaLine{position:absolute;left:8px;top:40px;width:28px;height:4px;background:#cbd5e1}
	.side{position:absolute;left:50px;top:36px;width:40px;height:12px;background:#1e293b}
	.sideLine{position:absolute;left:54px;top:40px;width:30px;height:4px;background:#a78bfa}
	.taskbar{position:absolute;left:0;top:${height - 8}px;width:${width}px;height:8px;background:#334155}
	.ready{position:absolute;left:6px;top:${height - 6}px;width:22px;height:4px;background:#10b981}
	.alert{position:absolute;left:70px;top:${height - 6}px;width:20px;height:4px;background:#ef4444}
	</style>
	<div class="top"></div><div class="cmd1"></div><div class="cmd2"></div><div class="cmd3"></div>
	<div class="tile1"></div><div class="img1"></div><div class="tile2"></div><div class="img2"></div><div class="tile3"></div><div class="img3"></div>
	<div class="meta"></div><div class="metaLine"></div><div class="side"></div><div class="sideLine"></div>
	<div class="taskbar"></div><div class="ready"></div><div class="alert"></div>
	<script>window.__simpleExactBitmapReady=true;</script>`;
  }
  if (scene === "simple-web-engine2d-report-table-command") {
    return `<!doctype html>
<meta charset="utf-8">
<style>
html,body{margin:0;padding:0;width:${width}px;height:${height}px;overflow:hidden;background:#f8fafc}
.top{position:absolute;left:0;top:0;width:${width}px;height:10px;background:#0f172a}
.cmd1{position:absolute;left:4px;top:2px;width:18px;height:6px;background:#2563eb}
.cmd2{position:absolute;left:26px;top:2px;width:16px;height:6px;background:#10b981}
.cmd3{position:absolute;left:46px;top:2px;width:16px;height:6px;background:#f59e0b}
.rail{position:absolute;left:0;top:10px;width:14px;height:${height - 18}px;background:#e2e8f0}
.nav1{position:absolute;left:4px;top:16px;width:6px;height:6px;background:#64748b}
.nav2{position:absolute;left:4px;top:28px;width:6px;height:6px;background:#94a3b8}
.head{position:absolute;left:18px;top:14px;width:72px;height:8px;background:#dbeafe}
.h1{position:absolute;left:22px;top:17px;width:14px;height:3px;background:#1d4ed8}
.h2{position:absolute;left:42px;top:17px;width:16px;height:3px;background:#1d4ed8}
.h3{position:absolute;left:64px;top:17px;width:18px;height:3px;background:#1d4ed8}
.row1{position:absolute;left:18px;top:24px;width:72px;height:8px;background:#fff}
.r1a{position:absolute;left:22px;top:27px;width:18px;height:3px;background:#94a3b8}
.r1b{position:absolute;left:46px;top:27px;width:10px;height:3px;background:#22c55e}
.r1c{position:absolute;left:66px;top:27px;width:16px;height:3px;background:#cbd5e1}
.row2{position:absolute;left:18px;top:34px;width:72px;height:8px;background:#f1f5f9}
.r2a{position:absolute;left:22px;top:37px;width:20px;height:3px;background:#64748b}
.r2b{position:absolute;left:46px;top:37px;width:10px;height:3px;background:#ef4444}
.r2c{position:absolute;left:66px;top:37px;width:18px;height:3px;background:#cbd5e1}
.filter{position:absolute;left:18px;top:46px;width:30px;height:8px;background:#0f172a}
.filterLine{position:absolute;left:22px;top:49px;width:20px;height:3px;background:#38bdf8}
.summary{position:absolute;left:54px;top:46px;width:36px;height:8px;background:#ecfccb}
.summaryLine{position:absolute;left:58px;top:49px;width:24px;height:3px;background:#65a30d}
.taskbar{position:absolute;left:0;top:${height - 8}px;width:${width}px;height:8px;background:#334155}
.status{position:absolute;left:68px;top:${height - 6}px;width:20px;height:4px;background:#7c3aed}
</style>
<div class="top"></div><div class="cmd1"></div><div class="cmd2"></div><div class="cmd3"></div>
<div class="rail"></div><div class="nav1"></div><div class="nav2"></div>
<div class="head"></div><div class="h1"></div><div class="h2"></div><div class="h3"></div>
<div class="row1"></div><div class="r1a"></div><div class="r1b"></div><div class="r1c"></div>
<div class="row2"></div><div class="r2a"></div><div class="r2b"></div><div class="r2c"></div>
<div class="filter"></div><div class="filterLine"></div><div class="summary"></div><div class="summaryLine"></div>
<div class="taskbar"></div><div class="status"></div>
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

function isSimpleWebEngine2DScene() {
  return scene === "simple-web-engine2d-image-taskbar-command" || scene === "simple-web-engine2d-two-block-content" || scene === "simple-web-engine2d-wide-card-content" || scene === "simple-web-engine2d-split-pane-status-list" || scene === "simple-web-engine2d-toolbar-modal-grid" || scene === "simple-web-engine2d-dashboard-command-list" || scene === "simple-web-engine2d-form-sidebar-validation" || scene === "simple-web-engine2d-settings-inspector-tree" || scene === "simple-web-engine2d-media-gallery-command" || scene === "simple-web-engine2d-report-table-command";
}

function fixtureHtml() {
  if (htmlPath) {
    return htmlFileFixtureHtml();
  }
  // Render the REAL scene HTML/CSS for simple-web-engine2d-* scenes so Chromium
  // actually lays it out, even when an expected-ARGB path is supplied. The
  // expected ARGB is then used ONLY as the comparison reference (loadExpectedArgb),
  // not as the render source — otherwise Chromium would just redraw Simple's own
  // pixels and the "parity" would be a tautology.
  if (isSimpleWebEngine2DScene()) {
    return simpleWebEngine2DFixtureHtml();
  }
  if (expectedArgbPath) {
    return expectedArgbCanvasHtml();
  }
  return exactFixtureHtml();
}

function expectedFramePixels() {
  const fromFile = loadExpectedArgb();
  if (fromFile !== null) {
    return fromFile;
  }
  if (scene === "simple-web-engine2d-image-taskbar-command" || scene === "simple-web-engine2d-two-block-content" || scene === "simple-web-engine2d-wide-card-content" || scene === "simple-web-engine2d-split-pane-status-list" || scene === "simple-web-engine2d-toolbar-modal-grid" || scene === "simple-web-engine2d-dashboard-command-list" || scene === "simple-web-engine2d-form-sidebar-validation" || scene === "simple-web-engine2d-settings-inspector-tree" || scene === "simple-web-engine2d-media-gallery-command" || scene === "simple-web-engine2d-report-table-command") {
    const pixels = new Uint32Array(width * height);
    if (scene === "simple-web-engine2d-wide-card-content") {
      pixels.fill(0xFF0B1020 >>> 0);
      rectArray(pixels, 8, 8, 120, 60, 0xFFF59E0B >>> 0);
    } else if (scene === "simple-web-engine2d-split-pane-status-list") {
      pixels.fill(0xFF101820 >>> 0);
      rectArray(pixels, 0, 0, 12, height, 0xFF1F2937 >>> 0);
      rectArray(pixels, 3, 8, 6, 6, 0xFFEF4444 >>> 0);
      rectArray(pixels, 3, 22, 6, 6, 0xFF22C55E >>> 0);
      rectArray(pixels, 3, 36, 6, 6, 0xFF3B82F6 >>> 0);
      rectArray(pixels, 12, 0, width - 12, 10, 0xFF334155 >>> 0);
      rectArray(pixels, 16, 14, 34, 44, 0xFF0F172A >>> 0);
      rectArray(pixels, 54, 14, 36, 44, 0xFF111827 >>> 0);
      rectArray(pixels, 58, 18, 28, 4, 0xFF374151 >>> 0);
      rectArray(pixels, 58, 18, 20, 4, 0xFF22C55E >>> 0);
      rectArray(pixels, 58, 30, 28, 4, 0xFF374151 >>> 0);
      rectArray(pixels, 58, 30, 14, 4, 0xFFF59E0B >>> 0);
      rectArray(pixels, 58, 42, 28, 4, 0xFF374151 >>> 0);
      rectArray(pixels, 58, 42, 24, 4, 0xFF3B82F6 >>> 0);
    } else if (scene === "simple-web-engine2d-toolbar-modal-grid") {
      pixels.fill(0xFF0E1116 >>> 0);
      rectArray(pixels, 0, 0, width, 12, 0xFF243447 >>> 0);
      rectArray(pixels, 4, 2, 22, 8, 0xFF22C55E >>> 0);
      rectArray(pixels, 30, 2, 18, 8, 0xFF3B82F6 >>> 0);
      rectArray(pixels, 0, 12, 14, height - 20, 0xFF111827 >>> 0);
      rectArray(pixels, 18, 16, 26, 20, 0xFFF59E0B >>> 0);
      rectArray(pixels, 20, 18, 6, 6, 0xFFEF4444 >>> 0);
      rectArray(pixels, 28, 18, 6, 6, 0xFF22C55E >>> 0);
      rectArray(pixels, 36, 18, 6, 6, 0xFF3B82F6 >>> 0);
      rectArray(pixels, 20, 26, 22, 6, 0xFFE5E7EB >>> 0);
      rectArray(pixels, 50, 14, 38, 34, 0xFFF8FAFC >>> 0);
      rectArray(pixels, 50, 14, 38, 8, 0xFF64748B >>> 0);
      rectArray(pixels, 54, 26, 30, 4, 0xFFCBD5E1 >>> 0);
      rectArray(pixels, 54, 36, 20, 4, 0xFF94A3B8 >>> 0);
      rectArray(pixels, 0, height - 8, width, 8, 0xFF1F2937 >>> 0);
      rectArray(pixels, 6, height - 6, 18, 4, 0xFF8B5CF6 >>> 0);
      rectArray(pixels, 28, height - 6, 18, 4, 0xFF06B6D4 >>> 0);
    } else if (scene === "simple-web-engine2d-dashboard-command-list") {
      pixels.fill(0xFF0B1220 >>> 0);
      rectArray(pixels, 0, 0, width, 10, 0xFF111827 >>> 0);
      rectArray(pixels, 4, 2, 18, 6, 0xFF22C55E >>> 0);
      rectArray(pixels, 26, 2, 18, 6, 0xFFF59E0B >>> 0);
      rectArray(pixels, 48, 2, 16, 6, 0xFF3B82F6 >>> 0);
      rectArray(pixels, 0, 10, 16, height - 18, 0xFF0F172A >>> 0);
      rectArray(pixels, 4, 16, 8, 8, 0xFF8B5CF6 >>> 0);
      rectArray(pixels, 4, 30, 8, 8, 0xFF06B6D4 >>> 0);
      rectArray(pixels, 20, 14, 30, 20, 0xFF1E293B >>> 0);
      rectArray(pixels, 24, 18, 6, 12, 0xFF22C55E >>> 0);
      rectArray(pixels, 34, 22, 6, 8, 0xFFF59E0B >>> 0);
      rectArray(pixels, 44, 16, 6, 14, 0xFF3B82F6 >>> 0);
      rectArray(pixels, 54, 14, 34, 38, 0xFFF8FAFC >>> 0);
      rectArray(pixels, 58, 18, 24, 4, 0xFFCBD5E1 >>> 0);
      rectArray(pixels, 58, 28, 20, 4, 0xFF94A3B8 >>> 0);
      rectArray(pixels, 58, 38, 26, 4, 0xFFCBD5E1 >>> 0);
      rectArray(pixels, 0, height - 8, width, 8, 0xFF1F2937 >>> 0);
      rectArray(pixels, 68, height - 6, 20, 4, 0xFF10B981 >>> 0);
    } else if (scene === "simple-web-engine2d-form-sidebar-validation") {
      pixels.fill(0xFF0A0F1A >>> 0);
      rectArray(pixels, 0, 0, 18, height, 0xFF111827 >>> 0);
      rectArray(pixels, 4, 6, 10, 8, 0xFF2563EB >>> 0);
      rectArray(pixels, 4, 20, 10, 8, 0xFF475569 >>> 0);
      rectArray(pixels, 18, 0, width - 18, 10, 0xFF1F2937 >>> 0);
      rectArray(pixels, 22, 14, 44, 38, 0xFFF8FAFC >>> 0);
      rectArray(pixels, 26, 20, 34, 6, 0xFFE5E7EB >>> 0);
      rectArray(pixels, 26, 30, 34, 6, 0xFFEF4444 >>> 0);
      rectArray(pixels, 26, 42, 22, 5, 0xFF22C55E >>> 0);
      rectArray(pixels, 70, 14, 20, 20, 0xFF0F172A >>> 0);
      rectArray(pixels, 74, 18, 8, 8, 0xFFF59E0B >>> 0);
      rectArray(pixels, 72, 38, 16, 5, 0xFF06B6D4 >>> 0);
      rectArray(pixels, 0, height - 8, width, 8, 0xFF334155 >>> 0);
      rectArray(pixels, 54, height - 6, 18, 4, 0xFF8B5CF6 >>> 0);
    } else if (scene === "simple-web-engine2d-settings-inspector-tree") {
      pixels.fill(0xFF0B1020 >>> 0);
      rectArray(pixels, 0, 0, width, 9, 0xFF111827 >>> 0);
      rectArray(pixels, 4, 2, 16, 5, 0xFF38BDF8 >>> 0);
      rectArray(pixels, 24, 2, 14, 5, 0xFF22C55E >>> 0);
      rectArray(pixels, 0, 9, 22, height - 17, 0xFF1E293B >>> 0);
      rectArray(pixels, 4, 15, 14, 4, 0xFFE2E8F0 >>> 0);
      rectArray(pixels, 6, 25, 12, 4, 0xFF94A3B8 >>> 0);
      rectArray(pixels, 8, 35, 10, 4, 0xFF475569 >>> 0);
      rectArray(pixels, 26, 13, 34, 36, 0xFFF8FAFC >>> 0);
      rectArray(pixels, 30, 18, 22, 5, 0xFFCBD5E1 >>> 0);
      rectArray(pixels, 30, 28, 26, 5, 0xFFBFDBFE >>> 0);
      rectArray(pixels, 30, 38, 18, 5, 0xFFBBF7D0 >>> 0);
      rectArray(pixels, 64, 13, 28, 36, 0xFF111827 >>> 0);
      rectArray(pixels, 68, 18, 20, 4, 0xFFF59E0B >>> 0);
      rectArray(pixels, 68, 28, 16, 4, 0xFF8B5CF6 >>> 0);
      rectArray(pixels, 68, 38, 20, 4, 0xFF06B6D4 >>> 0);
      rectArray(pixels, 0, height - 8, width, 8, 0xFF334155 >>> 0);
      rectArray(pixels, 76, height - 6, 14, 4, 0xFFEF4444 >>> 0);
    } else if (scene === "simple-web-engine2d-media-gallery-command") {
      pixels.fill(0xFF0F172A >>> 0);
      rectArray(pixels, 0, 0, width, 10, 0xFF1F2937 >>> 0);
      rectArray(pixels, 4, 2, 18, 6, 0xFF14B8A6 >>> 0);
      rectArray(pixels, 26, 2, 16, 6, 0xFFF97316 >>> 0);
      rectArray(pixels, 46, 2, 18, 6, 0xFF6366F1 >>> 0);
      rectArray(pixels, 4, 14, 26, 18, 0xFF111827 >>> 0);
      rectArray(pixels, 7, 17, 20, 12, 0xFF38BDF8 >>> 0);
      rectArray(pixels, 34, 14, 26, 18, 0xFF111827 >>> 0);
      rectArray(pixels, 37, 17, 20, 12, 0xFFFACC15 >>> 0);
      rectArray(pixels, 64, 14, 26, 18, 0xFF111827 >>> 0);
      rectArray(pixels, 67, 17, 20, 12, 0xFF22C55E >>> 0);
      rectArray(pixels, 4, 36, 38, 12, 0xFFF8FAFC >>> 0);
      rectArray(pixels, 8, 40, 28, 4, 0xFFCBD5E1 >>> 0);
      rectArray(pixels, 50, 36, 40, 12, 0xFF1E293B >>> 0);
      rectArray(pixels, 54, 40, 30, 4, 0xFFA78BFA >>> 0);
      rectArray(pixels, 0, height - 8, width, 8, 0xFF334155 >>> 0);
      rectArray(pixels, 6, height - 6, 22, 4, 0xFF10B981 >>> 0);
      rectArray(pixels, 70, height - 6, 20, 4, 0xFFEF4444 >>> 0);
    } else if (scene === "simple-web-engine2d-report-table-command") {
      pixels.fill(0xFFF8FAFC >>> 0);
      rectArray(pixels, 0, 0, width, 10, 0xFF0F172A >>> 0);
      rectArray(pixels, 4, 2, 18, 6, 0xFF2563EB >>> 0);
      rectArray(pixels, 26, 2, 16, 6, 0xFF10B981 >>> 0);
      rectArray(pixels, 46, 2, 16, 6, 0xFFF59E0B >>> 0);
      rectArray(pixels, 0, 10, 14, height - 18, 0xFFE2E8F0 >>> 0);
      rectArray(pixels, 4, 16, 6, 6, 0xFF64748B >>> 0);
      rectArray(pixels, 4, 28, 6, 6, 0xFF94A3B8 >>> 0);
      rectArray(pixels, 18, 14, 72, 8, 0xFFDBEAFE >>> 0);
      rectArray(pixels, 22, 17, 14, 3, 0xFF1D4ED8 >>> 0);
      rectArray(pixels, 42, 17, 16, 3, 0xFF1D4ED8 >>> 0);
      rectArray(pixels, 64, 17, 18, 3, 0xFF1D4ED8 >>> 0);
      rectArray(pixels, 18, 24, 72, 8, 0xFFFFFFFF >>> 0);
      rectArray(pixels, 22, 27, 18, 3, 0xFF94A3B8 >>> 0);
      rectArray(pixels, 46, 27, 10, 3, 0xFF22C55E >>> 0);
      rectArray(pixels, 66, 27, 16, 3, 0xFFCBD5E1 >>> 0);
      rectArray(pixels, 18, 34, 72, 8, 0xFFF1F5F9 >>> 0);
      rectArray(pixels, 22, 37, 20, 3, 0xFF64748B >>> 0);
      rectArray(pixels, 46, 37, 10, 3, 0xFFEF4444 >>> 0);
      rectArray(pixels, 66, 37, 18, 3, 0xFFCBD5E1 >>> 0);
      rectArray(pixels, 18, 46, 30, 8, 0xFF0F172A >>> 0);
      rectArray(pixels, 22, 49, 20, 3, 0xFF38BDF8 >>> 0);
      rectArray(pixels, 54, 46, 36, 8, 0xFFECFCCB >>> 0);
      rectArray(pixels, 58, 49, 24, 3, 0xFF65A30D >>> 0);
      rectArray(pixels, 0, height - 8, width, 8, 0xFF334155 >>> 0);
      rectArray(pixels, 68, height - 6, 20, 4, 0xFF7C3AED >>> 0);
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
  const capturedPixels = capturedArgbPath ? new Uint32Array(width * height) : null;

  for (let i = 0; i < width * height; i += 1) {
    const off = i * 4;
    const blue = buffer[off];
    const green = buffer[off + 1];
    const red = buffer[off + 2];
    const alpha = buffer[off + 3];
    const isArgbScene = expectedArgbPath !== "" || scene === "simple-web-engine2d-image-taskbar-command" || scene === "simple-web-engine2d-two-block-content" || scene === "simple-web-engine2d-wide-card-content" || scene === "simple-web-engine2d-split-pane-status-list" || scene === "simple-web-engine2d-toolbar-modal-grid" || scene === "simple-web-engine2d-dashboard-command-list" || scene === "simple-web-engine2d-form-sidebar-validation" || scene === "simple-web-engine2d-settings-inspector-tree" || scene === "simple-web-engine2d-media-gallery-command" || scene === "simple-web-engine2d-report-table-command";
    const value = isArgbScene
      ? (((alpha << 24) >>> 0) | (red << 16) | (green << 8) | blue) >>> 0
      : red;
    if (capturedPixels !== null) {
      capturedPixels[i] = isArgbScene
        ? value
        : (((alpha << 24) >>> 0) | (red << 16) | (green << 8) | blue) >>> 0;
    }
    sum += BigInt(value >>> 0);
    weighted += BigInt(value >>> 0) * BigInt(i + 1);
    if (value !== expectedPixels[i] || alpha !== 255 || (!isArgbScene && (blue !== 0 || green !== 0))) {
      mismatches += 1;
    }
  }
  return { sum, weighted, mismatches, capturedPixels };
}

function writeCapturedArgb(pixels) {
  if (!capturedArgbPath || !pixels) return false;
  const payload = {
    width,
    height,
    format: "argb-u32",
    producer: "electron-live-capture-page",
    pixels: Array.from(pixels, (v) => v >>> 0),
  };
  fs.writeFileSync(capturedArgbPath, JSON.stringify(payload));
  return true;
}

// Resolution-convert layer for Electron capture.
//
// On HiDPI/Retina displays, BrowserWindow.capturePage({width,height}) returns a
// NativeImage whose backing store is the physical resolution: image.getSize()
// reports scaleFactor*{width,height} and image.toBitmap() is a BGRA buffer at
// that native size. Reading it at the logical `width` stride mislabels a
// top-left slice as the whole frame (scanline garbage) and forces ~100% pixel
// mismatch independent of rendering fidelity. This layer normalizes ANY capture
// resolution down to the logical comparison resolution by box-averaging each
// native block into one logical pixel, so the comparison is resolution-agnostic.
function bitmapToLogicalBgra(image) {
  const size = image.getSize();
  const native = image.toBitmap({ scaleFactor: 1 }); // BGRA at size.width x size.height
  const nw = size.width;
  const nh = size.height;
  if (native.length !== nw * nh * 4) {
    throw new Error(`Electron capture bitmap size mismatch: ${native.length} bytes for ${nw}x${nh}`);
  }
  if (nw === width && nh === height) {
    return { buffer: native, nativeWidth: nw, nativeHeight: nh, downsampled: false };
  }
  if (nw <= 0 || nh <= 0 || nw % width !== 0 || nh % height !== 0) {
    throw new Error(`Electron capture size is not an integer logical scale: native=${nw}x${nh} logical=${width}x${height}`);
  }
  const out = Buffer.alloc(width * height * 4);
  const kx = nw / width;
  const ky = nh / height;
  for (let y = 0; y < height; y += 1) {
    const sy0 = Math.floor(y * ky);
    const sy1 = Math.min(nh, Math.max(sy0 + 1, Math.floor((y + 1) * ky)));
    for (let x = 0; x < width; x += 1) {
      const sx0 = Math.floor(x * kx);
      const sx1 = Math.min(nw, Math.max(sx0 + 1, Math.floor((x + 1) * kx)));
      let b = 0;
      let g = 0;
      let r = 0;
      let a = 0;
      let n = 0;
      for (let sy = sy0; sy < sy1; sy += 1) {
        for (let sx = sx0; sx < sx1; sx += 1) {
          const o = (sy * nw + sx) * 4;
          b += native[o];
          g += native[o + 1];
          r += native[o + 2];
          a += native[o + 3];
          n += 1;
        }
      }
      if (n === 0) n = 1;
      const o = (y * width + x) * 4;
      out[o] = Math.round(b / n);
      out[o + 1] = Math.round(g / n);
      out[o + 2] = Math.round(r / n);
      out[o + 3] = Math.round(a / n);
    }
  }
  return { buffer: out, nativeWidth: nw, nativeHeight: nh, downsampled: true };
}

async function main() {
  await app.whenReady();
  const win = new BrowserWindow({
    show: false,
    useContentSize: true,
    width: 1280,
    height: 720,
    backgroundColor: "#000000",
    webPreferences: {
      offscreen: true,
      backgroundThrottling: false,
      nodeIntegration: false,
      contextIsolation: true,
    },
  });
  win.setContentSize(width, height);
  win.webContents.setZoomFactor(1);
  // Drive the offscreen rendering pipeline (a consumer for paint frames keeps it
  // producing, which also lets requestAnimationFrame-based readiness fire).
  win.webContents.setFrameRate(30);
  win.webContents.on("paint", () => {});
  await win.loadURL(`data:text/html;charset=utf-8,${encodeURIComponent(fixtureHtml())}`);
  const ready = await win.webContents.executeJavaScript(`
    new Promise((resolve) => {
      if (window.__simpleExactBitmapReady === true) {
        resolve(true);
        return;
      }
      const start = performance.now();
      const tick = () => {
        if (window.__simpleExactBitmapReady === true || performance.now() - start > 10000) {
          resolve(window.__simpleExactBitmapReady === true);
          return;
        }
        setTimeout(tick, 10);
      };
      tick();
    })
  `);
  if (ready !== true) {
    throw new Error("generated HTML did not reach exact bitmap readiness");
  }

  const expected = expectedChecksum > 0n ? expectedChecksum : expectedFrameChecksum();
  const expectedWeighted = expectedWeightedChecksum > 0n ? expectedWeightedChecksum : weightedChecksum(expectedFramePixels());
  let last = { sum: 0n, weighted: 0n, mismatches: width * height };
  let capture = { nativeWidth: width, nativeHeight: height, downsampled: false };
  const start = process.hrtime.bigint();
  for (let i = 0; i < iterations; i += 1) {
    const image = await win.capturePage({ x: 0, y: 0, width, height }, { stayHidden: true });
    capture = bitmapToLogicalBgra(image);
    last = captureChecksum(capture.buffer);
  }
  const elapsed = process.hrtime.bigint() - start;
  const frameUs = elapsed > 0n ? Number(elapsed / BigInt(iterations) / 1000n) : 1;
  const wroteCapturedArgb = writeCapturedArgb(last.capturedPixels);

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
  emit("capture_native_width", capture.nativeWidth);
  emit("capture_native_height", capture.nativeHeight);
  emit("capture_downsampled", String(capture.downsampled));
  emit("captured_argb_path", capturedArgbPath);
  emit("captured_argb_written", String(wroteCapturedArgb));
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
      capture_native_width: capture.nativeWidth,
      capture_native_height: capture.nativeHeight,
      capture_downsampled: capture.downsampled,
      html_path: htmlPath,
      captured_argb_path: capturedArgbPath,
      captured_argb_written: wroteCapturedArgb,
      blur_or_tolerance_used: false
    }));
  }

  const exitCode = last.sum === expected && last.weighted === expectedWeighted && last.mismatches === 0 ? 0 : 2;
  app.exit(exitCode);
  process.exit(exitCode);
}

main().catch(async (err) => {
  console.error(err && err.stack ? err.stack : String(err));
  try { app.exit(1); } catch (_) {}
  process.exit(1);
});
