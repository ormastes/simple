#!/usr/bin/env node
"use strict";

const { app, BrowserWindow } = require("electron");
const fs = require("fs");
const path = require("path");

const htmlPath = process.env.ELECTRON_CAPTURE_HTML || "";
const width = Number(process.env.ELECTRON_CAPTURE_WIDTH || 1280);
const height = Number(process.env.ELECTRON_CAPTURE_HEIGHT || 720);
const stageLogPath = process.env.ELECTRON_CAPTURE_STAGE_LOG || "";
const holdMs = Number(process.env.ELECTRON_RENDERDOC_HOLD_MS || 12000);
const loadTimeoutMs = Number(process.env.ELECTRON_CAPTURE_LOAD_TIMEOUT_MS || 3000);
const forceDataUrl = /^(1|true|yes)$/i.test(process.env.ELECTRON_CAPTURE_FORCE_DATA_URL || "");

app.commandLine.appendSwitch("force-device-scale-factor", "1");
app.commandLine.appendSwitch("force-color-profile", "srgb");

function stage(name) {
  if (!stageLogPath) return;
  fs.mkdirSync(path.dirname(stageLogPath), { recursive: true });
  fs.appendFileSync(stageLogPath, `electron_renderdoc_display_stage=${name}\n`);
}

function withTimeout(promise, ms, label) {
  let timer = null;
  const timeout = new Promise((_, reject) => {
    timer = setTimeout(() => reject(new Error(label + "-timeout")), ms);
  });
  return Promise.race([promise, timeout]).finally(() => {
    if (timer) clearTimeout(timer);
  });
}

async function main() {
  stage("main-start");
  if (!htmlPath) throw new Error("ELECTRON_CAPTURE_HTML is required");
  const absHtml = path.resolve(htmlPath);
  stage("before-app-ready");
  await app.whenReady();
  stage("after-app-ready");
  const win = new BrowserWindow({
    show: true,
    useContentSize: true,
    width,
    height,
    backgroundColor: "#ffffff",
    webPreferences: {
      backgroundThrottling: false,
      nodeIntegration: false,
      contextIsolation: true,
    },
  });
  win.setContentSize(width, height);
  if (forceDataUrl) {
    stage("before-load-data-url");
    const html = fs.readFileSync(absHtml, "utf8");
    await withTimeout(
      win.loadURL("data:text/html;charset=utf-8," + encodeURIComponent(html)),
      loadTimeoutMs,
      "load-data-url"
    ).catch(err => {
      stage("load-data-url-failed");
      console.error(err && err.message ? err.message : err);
    });
    stage("after-load-data-url");
  } else {
    stage("before-load-file");
    await withTimeout(win.loadFile(absHtml), loadTimeoutMs, "load-file").catch(err => {
      stage("load-file-failed");
      console.error(err && err.message ? err.message : err);
    });
    stage("after-load-file");
  }
  stage("before-hold");
  await new Promise(resolve => setTimeout(resolve, holdMs));
  stage("after-hold");
  app.quit();
}

main().catch(err => {
  stage("error");
  console.error(err && err.stack ? err.stack : err);
  process.exit(1);
});
