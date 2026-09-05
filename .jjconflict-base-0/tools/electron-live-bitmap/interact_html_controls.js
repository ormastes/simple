#!/usr/bin/env node
"use strict";

const { app, BrowserWindow } = require("electron");
const fs = require("fs");
const path = require("path");

const htmlPath = process.env.ELECTRON_INTERACT_HTML || "";
const width = Number(process.env.ELECTRON_INTERACT_WIDTH || 1360);
const height = Number(process.env.ELECTRON_INTERACT_HEIGHT || 840);
const outputPath = process.env.ELECTRON_INTERACT_OUTPUT || "build/test-artifacts/electron_interaction.json";
const pngOutputPath = process.env.ELECTRON_INTERACT_PNG_OUTPUT || "";
const settleMs = Number(process.env.ELECTRON_INTERACT_SETTLE_MS || 800);

app.commandLine.appendSwitch("force-device-scale-factor", "1");
app.commandLine.appendSwitch("force-color-profile", "srgb");

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function ensureDir(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

async function centerOf(win, selector) {
  return win.webContents.executeJavaScript(`
    (() => {
      const selector = ${JSON.stringify(selector)};
      const candidates = Array.from(document.querySelectorAll(selector));
      for (const el of candidates) {
        const rect = el.getBoundingClientRect();
        const x = Math.round(rect.left + rect.width / 2);
        const y = Math.round(rect.top + rect.height / 2);
        if (rect.width <= 0 || rect.height <= 0) continue;
        const hit = document.elementFromPoint(x, y);
        if (hit === el || el.contains(hit) || (hit && hit.closest(selector) === el)) {
          return {
            x,
            y,
            width: Math.round(rect.width),
            height: Math.round(rect.height)
          };
        }
      }
      return null;
    })()
  `);
}

async function clickSelector(win, selector) {
  const point = await centerOf(win, selector);
  if (!point || point.width <= 0 || point.height <= 0) return false;
  win.webContents.sendInputEvent({ type: "mouseMove", x: point.x, y: point.y });
  win.webContents.sendInputEvent({ type: "mouseDown", x: point.x, y: point.y, button: "left", clickCount: 1 });
  win.webContents.sendInputEvent({ type: "mouseUp", x: point.x, y: point.y, button: "left", clickCount: 1 });
  await sleep(80);
  return true;
}

async function run() {
  if (!htmlPath) throw new Error("ELECTRON_INTERACT_HTML is required");

  const win = new BrowserWindow({
    width,
    height,
    show: true,
    backgroundColor: "#0a0a0f",
    webPreferences: {
      sandbox: false,
      contextIsolation: false,
      nodeIntegration: false
    }
  });

  await win.loadFile(path.resolve(htmlPath));
  await sleep(settleMs);

  await win.webContents.executeJavaScript(`
    (() => {
      window.__wmInteractionLog = [];
      const interesting = [
        ".wm-command-palette-input",
        ".wm-effect-control",
        ".wm-quality-mode",
        ".wm-top-menu-item",
        ".wm-taskbar-item",
        ".wm-command-item"
      ];
      function labelFor(el) {
        if (!el) return "";
        if (el.closest(".wm-traffic-lights")) return ".wm-traffic-lights button";
        for (const selector of interesting) {
          const match = el.closest(selector);
          if (match) return selector;
        }
        return el.tagName ? el.tagName.toLowerCase() : "";
      }
      function record(type, ev) {
        window.__wmInteractionLog.push({
          type,
          target: labelFor(ev.target),
          key: ev.key || "",
          value: ev.target && "value" in ev.target ? String(ev.target.value) : "",
          trusted: ev.isTrusted === true
        });
      }
      ["focusin", "keydown", "input", "pointerdown", "click"].forEach(type => {
        document.addEventListener(type, ev => record(type, ev), true);
      });
      window.__wmInteractionReady = true;
    })()
  `);

  await clickSelector(win, ".wm-command-palette-input");
  await win.webContents.insertText(" Browser");
  await sleep(100);
  const controlClicked = await clickSelector(win, ".wm-effect-control[data-effect-value='reduced']") ||
    await clickSelector(win, ".wm-quality-mode[data-quality-mode='compact']") ||
    await clickSelector(win, ".wm-top-menu-item[data-menu-action='command_palette']");
  await clickSelector(win, ".wm-taskbar-item[aria-label^='Focus Browser']");
  const trafficClicked = await clickSelector(win, ".wm-traffic-lights .wm-btn-minimize") ||
    await clickSelector(win, ".wm-taskbar-preview-action[data-preview-action='minimize']");

  const result = await win.webContents.executeJavaScript(`
    (() => {
      const log = window.__wmInteractionLog || [];
      const input = document.querySelector(".wm-command-palette-input");
      const active = document.activeElement;
      const has = (type, target) => log.some(entry => entry.type === type && entry.target === target);
      const keyboardInput = !!input && String(input.value).includes("Browser");
      const focusDelivered = log.some(entry => entry.type === "focusin" && entry.target === ".wm-command-palette-input");
      const inputDelivered = log.some(entry => entry.type === "input" && entry.target === ".wm-command-palette-input");
      const controlClickDelivered = ${JSON.stringify(controlClicked)} &&
        (has("click", ".wm-effect-control") || has("click", ".wm-quality-mode") || has("click", ".wm-top-menu-item"));
      const taskbarClickDelivered = has("click", ".wm-taskbar-item");
      const trafficClickDelivered = ${JSON.stringify(trafficClicked)} &&
        (has("click", ".wm-traffic-lights button") || log.some(entry => entry.type === "click" && entry.target === "button"));
      const pointerDelivered = log.some(entry => entry.type === "pointerdown" && entry.trusted === true);
      const pass = focusDelivered && inputDelivered && keyboardInput &&
        controlClickDelivered && taskbarClickDelivered && trafficClickDelivered && pointerDelivered;
      return {
        pass,
        reason: pass ? "pass" : "missing-event",
        focusDelivered,
        inputDelivered,
        keyboardInput,
        controlClickDelivered,
        taskbarClickDelivered,
        trafficClickDelivered,
        pointerDelivered,
        activeElement: active ? active.className || active.tagName.toLowerCase() : "",
        inputValue: input ? input.value : "",
        eventCount: log.length,
        events: log
      };
    })()
  `);

  if (pngOutputPath) {
    ensureDir(pngOutputPath);
    const image = await win.webContents.capturePage();
    fs.writeFileSync(pngOutputPath, image.toPNG());
  }
  ensureDir(outputPath);
  fs.writeFileSync(outputPath, JSON.stringify(result, null, 2));
  console.log(`interaction_pass=${result.pass}`);
  console.log(`event_count=${result.eventCount}`);
  if (!result.pass) process.exitCode = 2;
  win.close();
}

app.whenReady().then(run).catch(err => {
  console.error(err && err.stack ? err.stack : String(err));
  process.exitCode = 1;
}).finally(() => {
  setTimeout(() => app.quit(), 50);
});
