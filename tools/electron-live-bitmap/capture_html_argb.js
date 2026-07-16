#!/usr/bin/env node
"use strict";
// Capture arbitrary HTML through real Chromium and export ARGB pixel buffer.
//
// Usage:
//   ELECTRON_CAPTURE_HTML=path.html \
//   ELECTRON_CAPTURE_WIDTH=320 \
//   ELECTRON_CAPTURE_HEIGHT=240 \
//   ELECTRON_CAPTURE_OUTPUT=build/pixel_compare/captured.json \
//   ELECTRON_CAPTURE_AUDIT_SELECTORS="#app,.widget-panel" \
//   ELECTRON_CAPTURE_AUDIT_OUTPUT=build/pixel_compare/audit.json \
//   ELECTRON_CAPTURE_MEDIA_FEATURES="prefers-contrast=more" \
//   ELECTRON_CAPTURE_FAIL_ON_AUDIT=1 \
//   xvfb-run --auto-servernum electron --no-sandbox --disable-gpu capture_html_argb.js

const { app, BrowserWindow } = require("electron");
const crypto = require("crypto");
const fs = require("fs");
const net = require("net");
const path = require("path");

const htmlPath = process.env.ELECTRON_CAPTURE_HTML || "";
const width = Number(process.env.ELECTRON_CAPTURE_WIDTH || 320);
const height = Number(process.env.ELECTRON_CAPTURE_HEIGHT || 240);
const outputPath = process.env.ELECTRON_CAPTURE_OUTPUT || "build/pixel_compare/captured.json";
const pngOutputPath = process.env.ELECTRON_CAPTURE_PNG_OUTPUT || "";
const stageLogPath = process.env.ELECTRON_CAPTURE_STAGE_LOG || "";
const settleMs = Number(process.env.ELECTRON_CAPTURE_SETTLE_MS || 1500);
const loadTimeoutMs = Number(process.env.ELECTRON_CAPTURE_LOAD_TIMEOUT_MS || 10000);
const forceDataUrl = /^(1|true|yes)$/i.test(process.env.ELECTRON_CAPTURE_FORCE_DATA_URL || "");
const continueAfterLoadTimeout = /^(1|true|yes)$/i.test(process.env.ELECTRON_CAPTURE_CONTINUE_AFTER_LOAD_TIMEOUT || "");
const useOffscreenPaint = /^(1|true|yes)$/i.test(process.env.ELECTRON_CAPTURE_OFFSCREEN_PAINT || "");
const showWindow = /^(1|true|yes)$/i.test(process.env.ELECTRON_CAPTURE_SHOW_WINDOW || "");
const auditSelectors = (process.env.ELECTRON_CAPTURE_AUDIT_SELECTORS || "")
  .split(",")
  .map(s => s.trim())
  .filter(Boolean);
const auditOutputPath = process.env.ELECTRON_CAPTURE_AUDIT_OUTPUT || "";
const geometryOutputPath = process.env.ELECTRON_CAPTURE_GEOMETRY_OUTPUT || "";
const proofPath = process.env.ELECTRON_CAPTURE_PROOF_PATH || "";
const remoteDebuggingPort = process.env.ELECTRON_CAPTURE_REMOTE_DEBUGGING_PORT || "";
const contrastMinX100 = Number(process.env.ELECTRON_CAPTURE_CONTRAST_MIN_X100 || 450);
const touchMinPx = Number(process.env.ELECTRON_CAPTURE_TOUCH_MIN_PX || 44);
const failOnAudit = /^(1|true|yes)$/i.test(process.env.ELECTRON_CAPTURE_FAIL_ON_AUDIT || "");
const emulatedMediaFeatures = parseMediaFeatures(process.env.ELECTRON_CAPTURE_MEDIA_FEATURES || "");

app.commandLine.appendSwitch("force-device-scale-factor", "1");
app.commandLine.appendSwitch("force-color-profile", "srgb");
if (remoteDebuggingPort) app.commandLine.appendSwitch("remote-debugging-port", remoteDebuggingPort);

function stage(name) {
  if (!stageLogPath) return;
  fs.mkdirSync(path.dirname(stageLogPath), { recursive: true });
  fs.appendFileSync(stageLogPath, `electron_capture_stage=${name}\n`);
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

function websocketAcceptKey(key) {
  return crypto
    .createHash("sha1")
    .update(key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11")
    .digest("base64");
}

function encodeWebSocketFrame(text) {
  const payload = Buffer.from(text, "utf8");
  const len = payload.length;
  let headerLen = 2;
  if (len >= 126 && len <= 65535) headerLen = 4;
  else if (len > 65535) headerLen = 10;
  const out = Buffer.alloc(headerLen + 4 + len);
  out[0] = 0x81;
  if (len < 126) {
    out[1] = 0x80 | len;
  } else if (len <= 65535) {
    out[1] = 0x80 | 126;
    out.writeUInt16BE(len, 2);
  } else {
    out[1] = 0x80 | 127;
    out.writeUInt32BE(0, 2);
    out.writeUInt32BE(len, 6);
  }
  const maskOffset = headerLen;
  const payloadOffset = headerLen + 4;
  const mask = crypto.randomBytes(4);
  mask.copy(out, maskOffset);
  for (let i = 0; i < len; i++) out[payloadOffset + i] = payload[i] ^ mask[i % 4];
  return out;
}

function readWebSocketFrame(socket, state) {
  return new Promise((resolve, reject) => {
    const tryParse = () => {
      if (state.buffer.length < 2) return false;
      const b0 = state.buffer[0];
      const opcode = b0 & 0x0f;
      let len = state.buffer[1] & 0x7f;
      let offset = 2;
      if (len === 126) {
        if (state.buffer.length < 4) return false;
        len = state.buffer.readUInt16BE(2);
        offset = 4;
      } else if (len === 127) {
        if (state.buffer.length < 10) return false;
        const hi = state.buffer.readUInt32BE(2);
        const lo = state.buffer.readUInt32BE(6);
        if (hi !== 0) return reject(new Error("websocket-frame-too-large"));
        len = lo;
        offset = 10;
      }
      const masked = (state.buffer[1] & 0x80) !== 0;
      const maskOffset = offset;
      if (masked) offset += 4;
      if (state.buffer.length < offset + len) return false;
      let payload = state.buffer.subarray(offset, offset + len);
      if (masked) {
        const mask = state.buffer.subarray(maskOffset, maskOffset + 4);
        const copy = Buffer.alloc(len);
        for (let i = 0; i < len; i++) copy[i] = payload[i] ^ mask[i % 4];
        payload = copy;
      }
      state.buffer = state.buffer.subarray(offset + len);
      if (opcode === 0x8) return reject(new Error("websocket-closed"));
      if (opcode === 0x1) return resolve(payload.toString("utf8"));
      return false;
    };
    const cleanup = () => {
      socket.off("data", onData);
      socket.off("error", onError);
    };
    const onData = chunk => {
      state.buffer = Buffer.concat([state.buffer, chunk]);
      const parsed = tryParse();
      if (parsed !== false) cleanup();
    };
    const onError = err => {
      cleanup();
      reject(err);
    };
    socket.on("data", onData);
    socket.on("error", onError);
    const parsed = tryParse();
    if (parsed !== false) cleanup();
  });
}

function connectWebSocket(wsUrl) {
  const parsed = new URL(wsUrl);
  const host = parsed.hostname;
  const port = Number(parsed.port || 80);
  const pathAndQuery = parsed.pathname + (parsed.search || "");
  const key = crypto.randomBytes(16).toString("base64");
  const expectedAccept = websocketAcceptKey(key);
  return new Promise((resolve, reject) => {
    const socket = net.createConnection({ host, port });
    let handshake = Buffer.alloc(0);
    socket.setTimeout(Number(process.env.ELECTRON_CAPTURE_CDP_TIMEOUT_MS || 5000));
    socket.on("connect", () => {
      socket.write([
        `GET ${pathAndQuery} HTTP/1.1`,
        `Host: ${host}:${port}`,
        "Upgrade: websocket",
        "Connection: Upgrade",
        `Sec-WebSocket-Key: ${key}`,
        "Sec-WebSocket-Version: 13",
        "",
        "",
      ].join("\r\n"));
    });
    socket.on("data", chunk => {
      handshake = Buffer.concat([handshake, chunk]);
      const headerEnd = handshake.indexOf("\r\n\r\n");
      if (headerEnd < 0) return;
      const header = handshake.subarray(0, headerEnd).toString("utf8");
      if (!/^HTTP\/1\.1 101/.test(header) || !header.toLowerCase().includes(expectedAccept.toLowerCase())) {
        socket.destroy();
        reject(new Error("websocket-handshake-failed"));
        return;
      }
      const state = { buffer: handshake.subarray(headerEnd + 4) };
      socket.removeAllListeners("data");
      resolve({ socket, state });
    });
    socket.on("timeout", () => {
      socket.destroy();
      reject(new Error("websocket-timeout"));
    });
    socket.on("error", reject);
  });
}

async function cdpSend(conn, id, method, params) {
  conn.socket.write(encodeWebSocketFrame(JSON.stringify({ id, method, params: params || {} })));
  while (true) {
    const msg = JSON.parse(await readWebSocketFrame(conn.socket, conn.state));
    if (msg.id === id) {
      if (msg.error) throw new Error(`cdp-${method}:${msg.error.message || msg.error.code}`);
      return msg.result || {};
    }
  }
}

async function collectBrowserTargetGpuInfo() {
  if (!remoteDebuggingPort) return null;
  try {
    const version = await (await fetch(`http://127.0.0.1:${remoteDebuggingPort}/json/version`)).json();
    if (!version.webSocketDebuggerUrl) return { error: "electron-browser-devtools-missing" };
    const conn = await connectWebSocket(version.webSocketDebuggerUrl);
    try {
      return await cdpSend(conn, 1, "SystemInfo.getInfo");
    } finally {
      conn.socket.destroy();
    }
  } catch (err) {
    return { error: err && err.message ? err.message : "electron-browser-cdp-unavailable" };
  }
}

function parseMediaFeatures(value) {
  return String(value || "")
    .split(",")
    .map(part => part.trim())
    .filter(Boolean)
    .map(part => {
      const eq = part.indexOf("=");
      if (eq < 1) return null;
      const name = part.slice(0, eq).trim();
      const featureValue = part.slice(eq + 1).trim();
      if (!name || !featureValue) return null;
      return { name, value: featureValue };
    })
    .filter(Boolean);
}

async function applyEmulatedMediaFeatures(win, features) {
  if (!features.length) return;
  const dbg = win.webContents.debugger;
  if (!dbg.isAttached()) dbg.attach("1.3");
  await dbg.sendCommand("Emulation.setEmulatedMedia", { features });
}

async function collectEventProof(win) {
  const setup = await win.webContents.executeJavaScript(`
    (() => {
      const button = document.querySelector("button");
      const input = document.querySelector("input, textarea, [contenteditable='true']");
      const state = {
        proof_source: "tools/electron-live-bitmap/capture_html_argb.js",
        focus_count: 0,
        keyboard_count: 0,
        input_count: 0,
        pointer_down_count: 0,
        pointer_up_count: 0,
        click_count: 0,
        sequence: [],
        button_rect: null,
        input_rect: null,
        input_value_before: input ? String(input.value || input.textContent || "") : "",
        input_value_after: "",
      };
      const record = name => {
        state.sequence.push(name);
        if (name === "focus") state.focus_count += 1;
        if (name === "keydown" || name === "keyup") state.keyboard_count += 1;
        if (name === "input") state.input_count += 1;
        if (name === "pointerdown" || name === "mousedown") state.pointer_down_count += 1;
        if (name === "pointerup" || name === "mouseup") state.pointer_up_count += 1;
        if (name === "click") state.click_count += 1;
      };
      for (const name of ["focus", "keydown", "keyup", "input", "pointerdown", "pointerup", "mousedown", "mouseup", "click"]) {
        document.addEventListener(name, () => record(name), true);
      }
      if (button) {
        const rect = button.getBoundingClientRect();
        state.button_rect = { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2, width: rect.width, height: rect.height };
      }
      if (input) {
        const rect = input.getBoundingClientRect();
        state.input_rect = { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2, width: rect.width, height: rect.height };
      }
      window.__simpleCaptureEventProof = state;
      return {
        button_found: Boolean(button),
        input_found: Boolean(input),
        button_rect: state.button_rect,
        input_rect: state.input_rect,
      };
    })()
  `);
  if (!setup || !setup.button_found || !setup.input_found || !setup.button_rect || !setup.input_rect) {
    return {
      status: "fail",
      reason: "missing-visible-button-or-input",
      button_found: Boolean(setup && setup.button_found),
      input_found: Boolean(setup && setup.input_found),
    };
  }
  win.focus();
  win.webContents.focus();
  win.webContents.sendInputEvent({ type: "mouseMove", x: Math.round(setup.button_rect.x), y: Math.round(setup.button_rect.y) });
  win.webContents.sendInputEvent({ type: "mouseDown", x: Math.round(setup.button_rect.x), y: Math.round(setup.button_rect.y), button: "left", clickCount: 1 });
  win.webContents.sendInputEvent({ type: "mouseUp", x: Math.round(setup.button_rect.x), y: Math.round(setup.button_rect.y), button: "left", clickCount: 1 });
  await win.webContents.executeJavaScript(`document.querySelector("input, textarea, [contenteditable='true']").focus()`);
  win.webContents.sendInputEvent({ type: "keyDown", keyCode: "X" });
  win.webContents.sendInputEvent({ type: "char", keyCode: "X" });
  win.webContents.sendInputEvent({ type: "keyUp", keyCode: "X" });
  await win.webContents.insertText("X");
  await new Promise(r => setTimeout(r, 100));
  const proof = await win.webContents.executeJavaScript(`
    (() => {
      const state = window.__simpleCaptureEventProof || {};
      const input = document.querySelector("input, textarea, [contenteditable='true']");
      state.input_value_after = input ? String(input.value || input.textContent || "") : "";
      return state;
    })()
  `);
  const focusPass = Number(proof.focus_count || 0) >= 1;
  const keyboardPass = Number(proof.keyboard_count || 0) >= 2;
  const inputPass = Number(proof.input_count || 0) >= 1 && String(proof.input_value_after || "").includes("X");
  const pointerPass = Number(proof.pointer_down_count || 0) >= 1 && Number(proof.pointer_up_count || 0) >= 1;
  const clickPass = Number(proof.click_count || 0) >= 1;
  return {
    ...proof,
    button_found: true,
    input_found: true,
    focus_pass: focusPass,
    keyboard_pass: keyboardPass,
    input_pass: inputPass,
    pointer_pass: pointerPass,
    click_pass: clickPass,
    status: focusPass && keyboardPass && inputPass && pointerPass && clickPass ? "pass" : "fail",
    reason: focusPass && keyboardPass && inputPass && pointerPass && clickPass ? "pass" : "event-contract-missing",
  };
}

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

function sha256File(filePath) {
  return crypto.createHash("sha256").update(fs.readFileSync(filePath)).digest("hex");
}

async function collectAudit(win, selectors, mediaFeatures) {
  if (!selectors.length) return null;
  return win.webContents.executeJavaScript(`
    (() => {
      const selectors = ${JSON.stringify(selectors)};
      const mediaFeatures = ${JSON.stringify(mediaFeatures)};
      const contrastMinX100 = ${JSON.stringify(contrastMinX100)};
      const touchMinPx = ${JSON.stringify(touchMinPx)};
      const viewport = { width: window.innerWidth, height: window.innerHeight };
      const items = [];
      const entries = [];
      const rootStyle = window.getComputedStyle(document.documentElement);
      const mediaPreferenceResults = mediaFeatures.map(feature => {
        const query = "(" + feature.name + ": " + feature.value + ")";
        return {
          name: feature.name,
          value: feature.value,
          query,
          matches: window.matchMedia(query).matches
        };
      });
      const rootQualityTokens = {
        contrastPolicy: rootStyle.getPropertyValue("--ui-contrast-policy").trim(),
        text: rootStyle.getPropertyValue("--ui-text").trim(),
        dim: rootStyle.getPropertyValue("--ui-dim").trim(),
        accent: rootStyle.getPropertyValue("--ui-accent").trim(),
        glassOpacityFloorX100: rootStyle.getPropertyValue("--ui-glass-opacity-floor-x100").trim(),
        windowAlphaX100: rootStyle.getPropertyValue("--ui-window-alpha-x100").trim(),
        commandAlphaX100: rootStyle.getPropertyValue("--ui-command-alpha-x100").trim(),
        taskbarAlphaX100: rootStyle.getPropertyValue("--ui-taskbar-alpha-x100").trim(),
        widgetAlphaX100: rootStyle.getPropertyValue("--ui-widget-alpha-x100").trim(),
        motionOpenMs: rootStyle.getPropertyValue("--ui-motion-open-ms").trim(),
        motionCloseMs: rootStyle.getPropertyValue("--ui-motion-close-ms").trim(),
        motionMinimizeMs: rootStyle.getPropertyValue("--ui-motion-minimize-ms").trim(),
        wallpaperMotionMs: rootStyle.getPropertyValue("--ui-wallpaper-motion-ms").trim(),
        backdropDurationMs: rootStyle.getPropertyValue("--ui-backdrop-duration-ms").trim(),
        wallpaperState: rootStyle.getPropertyValue("--ui-wallpaper-state").trim()
      };
      function parseRgb(value) {
        const match = String(value || "").match(/rgba?\\((\\d+),\\s*(\\d+),\\s*(\\d+)(?:,\\s*([0-9.]+))?\\)/);
        if (!match) return null;
        return {
          r: Number(match[1]),
          g: Number(match[2]),
          b: Number(match[3]),
          a: match[4] === undefined ? 1 : Number(match[4])
        };
      }
      function luminance(c) {
        function channel(v) {
          const s = v / 255;
          return s <= 0.03928 ? s / 12.92 : Math.pow((s + 0.055) / 1.055, 2.4);
        }
        return 0.2126 * channel(c.r) + 0.7152 * channel(c.g) + 0.0722 * channel(c.b);
      }
      function composite(fg, bg) {
        if (!fg) return bg;
        if (!bg) return fg;
        const a = fg.a + bg.a * (1 - fg.a);
        if (a <= 0) return { r: 0, g: 0, b: 0, a: 0 };
        return {
          r: Math.round((fg.r * fg.a + bg.r * bg.a * (1 - fg.a)) / a),
          g: Math.round((fg.g * fg.a + bg.g * bg.a * (1 - fg.a)) / a),
          b: Math.round((fg.b * fg.a + bg.b * bg.a * (1 - fg.a)) / a),
          a
        };
      }
      function effectiveBackground(el, style) {
        let bg = parseRgb(style.backgroundColor);
        let parent = el.parentElement;
        while ((!bg || bg.a < 1) && parent) {
          const parentBg = parseRgb(window.getComputedStyle(parent).backgroundColor);
          if (parentBg && parentBg.a > 0) bg = composite(bg || { r: 0, g: 0, b: 0, a: 0 }, parentBg);
          parent = parent.parentElement;
        }
        if (!bg || bg.a < 1) bg = composite(bg || { r: 0, g: 0, b: 0, a: 0 }, parseRgb(window.getComputedStyle(document.body).backgroundColor) || { r: 10, g: 10, b: 15, a: 1 });
        return bg;
      }
      function contrastRatioX100(fg, bg) {
        if (!fg || !bg || fg.a === 0 || bg.a === 0) return null;
        const a = luminance(fg);
        const b = luminance(bg);
        const hi = Math.max(a, b);
        const lo = Math.min(a, b);
        return Math.round(((hi + 0.05) / (lo + 0.05)) * 100);
      }
      function isInteractive(el) {
        const tag = el.tagName.toLowerCase();
        const role = String(el.getAttribute("role") || "");
        return tag === "button" || tag === "input" || tag === "select" || tag === "textarea" ||
          role === "button" || role === "option" || role === "menuitem" || el.hasAttribute("tabindex");
      }
      function rectOf(el) {
        const r = el.getBoundingClientRect();
        return {
          left: Math.round(r.left),
          top: Math.round(r.top),
          right: Math.round(r.right),
          bottom: Math.round(r.bottom),
          width: Math.round(r.width),
          height: Math.round(r.height)
        };
      }
      function intersectsRect(a, b) {
        const left = Math.max(a.left, b.left);
        const top = Math.max(a.top, b.top);
        const right = Math.min(a.right, b.right);
        const bottom = Math.min(a.bottom, b.bottom);
        return {
          left,
          top,
          right,
          bottom,
          width: Math.max(0, right - left),
          height: Math.max(0, bottom - top)
        };
      }
      function clipsOverflow(style) {
        const clips = value => value === "hidden" || value === "auto" || value === "scroll" || value === "clip";
        return clips(style.overflowX) || clips(style.overflowY);
      }
      function visibleRectOf(el, rect) {
        let visible = intersectsRect(rect, { left: 0, top: 0, right: viewport.width, bottom: viewport.height });
        let parent = el.parentElement;
        while (visible.width > 0 && visible.height > 0 && parent && parent !== document.documentElement) {
          const parentStyle = window.getComputedStyle(parent);
          if (clipsOverflow(parentStyle)) visible = intersectsRect(visible, rectOf(parent));
          parent = parent.parentElement;
        }
        return visible;
      }
      function overlaps(a, b) {
        return a.left < b.right && a.right > b.left && a.top < b.bottom && a.bottom > b.top;
      }
      function containsElement(a, b) {
        return a !== b && a.contains(b);
      }
      function hasClass(item, name) {
        return String(item.className || "").split(/\\s+/).includes(name);
      }
      function isOverlay(item) {
        return hasClass(item, "wm-command-palette") ||
          hasClass(item, "wm-effect-controls") ||
          hasClass(item, "wm-quality-inspector");
      }
      function isOverlayContent(item) {
        return isOverlay(item) ||
          hasClass(item, "wm-command-item") ||
          hasClass(item, "wm-effect-control") ||
          hasClass(item, "wm-command-palette-input") ||
          hasClass(item, "wm-title-input");
      }
      function isWindowChrome(item) {
        return hasClass(item, "wm-window") ||
          hasClass(item, "wm-titlebar") ||
          hasClass(item, "wm-taskbar-item") ||
          hasClass(item, "wm-btn-close") ||
          hasClass(item, "wm-btn-minimize") ||
          hasClass(item, "wm-btn-maximize");
      }
      function allowedOverlayOverlap(a, b) {
        if (a.selector === "#wm-desktop" && hasClass(b, "wm-taskbar-item")) return true;
        if (b.selector === "#wm-desktop" && hasClass(a, "wm-taskbar-item")) return true;
        return (isOverlayContent(a) && isWindowChrome(b)) || (isOverlayContent(b) && isWindowChrome(a));
      }
      function isTextClipped(el, style) {
        const overflowedX = el.scrollWidth > el.clientWidth + 1;
        const overflowedY = el.scrollHeight > el.clientHeight + 1;
        if (!overflowedX && !overflowedY) return false;
        const visibleOrScrollable = value => value === "visible" || value === "auto" || value === "scroll";
        if ((overflowedX && visibleOrScrollable(style.overflowX)) || (overflowedY && visibleOrScrollable(style.overflowY))) return false;
        if (style.textOverflow === "ellipsis") return false;
        return Array.from(el.childNodes).some(node => node.nodeType === Node.TEXT_NODE && node.textContent.trim().length > 0) ||
          (el.children.length === 0 && String(el.textContent || "").trim().length > 0);
      }
      for (const selector of selectors) {
        const nodes = Array.from(document.querySelectorAll(selector));
        nodes.slice(0, 12).forEach((el, index) => {
          const style = window.getComputedStyle(el);
          const rawRect = rectOf(el);
          const rect = visibleRectOf(el, rawRect);
          if (rect.width <= 0 || rect.height <= 0) return;
          const effectiveBg = effectiveBackground(el, style);
          const contrastX100 = contrastRatioX100(parseRgb(style.color), effectiveBg);
          const interactive = isInteractive(el);
          const item = {
            selector,
            index,
            tag: el.tagName.toLowerCase(),
            className: String(el.className || ""),
            rect,
            rawRect,
            display: style.display,
            position: style.position,
            opacity: style.opacity,
            transform: style.transform,
            borderRadius: style.borderRadius,
            backgroundColor: style.backgroundColor,
            effectiveBackgroundColor: effectiveBg ? "rgba(" + effectiveBg.r + ", " + effectiveBg.g + ", " + effectiveBg.b + ", " + effectiveBg.a + ")" : "",
            color: style.color,
            overflowX: style.overflowX,
            overflowY: style.overflowY,
            contrastX100,
            contrastOk: contrastX100 === null ? null : contrastX100 >= contrastMinX100,
            interactive,
            touchOk: interactive ? rect.height >= touchMinPx && rect.width >= touchMinPx : null,
            clipped: isTextClipped(el, style)
          };
          items.push(item);
          entries.push({ el, item });
        });
      }
      const overlapPairs = [];
      const containedOverlapPairs = [];
      const allowedOverlayOverlapPairs = [];
      const unexpectedOverlapPairs = [];
      for (let i = 0; i < items.length; i++) {
        for (let j = i + 1; j < items.length; j++) {
          if (overlaps(items[i].rect, items[j].rect)) {
            const pair = {
              a: items[i].selector + "[" + items[i].index + "]",
              b: items[j].selector + "[" + items[j].index + "]"
            };
            overlapPairs.push(pair);
            if (containsElement(entries[i].el, entries[j].el) || containsElement(entries[j].el, entries[i].el)) {
              containedOverlapPairs.push(pair);
            } else if (allowedOverlayOverlap(items[i], items[j])) {
              allowedOverlayOverlapPairs.push(pair);
            } else {
              unexpectedOverlapPairs.push(pair);
            }
          }
        }
      }
      const clippedCount = items.filter(item => item.clipped).length;
      const unexpectedOverlapCount = unexpectedOverlapPairs.length;
      const contrastChecked = items.filter(item => item.contrastX100 !== null).length;
      const contrastFailures = items.filter(item => item.contrastOk === false).length;
      const touchChecked = items.filter(item => item.interactive).length;
      const touchFailures = items.filter(item => item.touchOk === false).length;
      const failureReasons = [];
      if (unexpectedOverlapCount > 0) failureReasons.push("unexpected-overlap");
      if (clippedCount > 0) failureReasons.push("text-clipping");
      if (contrastFailures > 0) failureReasons.push("contrast");
      if (touchFailures > 0) failureReasons.push("touch-target");
      const mediaPreferenceFailures = [];
      mediaPreferenceResults.forEach(result => {
        if (!result.matches) mediaPreferenceFailures.push(result.name + "=" + result.value + ":no-match");
        if ((result.name === "prefers-contrast" && result.value === "more") ||
            (result.name === "forced-colors" && result.value === "active")) {
          if (rootQualityTokens.contrastPolicy !== "os-high") {
            mediaPreferenceFailures.push(result.name + "=" + result.value + ":contrast-policy-" + rootQualityTokens.contrastPolicy);
          }
        }
        if (result.name === "prefers-reduced-motion" && result.value === "reduce") {
          if (rootQualityTokens.motionOpenMs !== "0" ||
              rootQualityTokens.motionCloseMs !== "0" ||
              rootQualityTokens.motionMinimizeMs !== "0") {
            mediaPreferenceFailures.push("prefers-reduced-motion=reduce:lifecycle-motion-" +
              rootQualityTokens.motionOpenMs + "-" +
              rootQualityTokens.motionCloseMs + "-" +
              rootQualityTokens.motionMinimizeMs);
          }
          if (rootQualityTokens.wallpaperMotionMs !== "0" ||
              rootQualityTokens.backdropDurationMs !== "0" ||
              rootQualityTokens.wallpaperState !== "wallpaper_static") {
            mediaPreferenceFailures.push("prefers-reduced-motion=reduce:backdrop-motion-" +
              rootQualityTokens.wallpaperMotionMs + "-" +
              rootQualityTokens.backdropDurationMs + "-" +
              rootQualityTokens.wallpaperState);
          }
        }
      });
      if (mediaPreferenceFailures.length > 0) failureReasons.push("media-preference");
      return {
        producer: "electron-chromium-dom-audit",
        viewport,
        selectors,
        emulatedMediaFeatures: mediaFeatures,
        mediaPreferenceResults,
        rootQualityTokens,
        thresholds: {
          contrastMinX100,
          touchMinPx
        },
        items,
        overlapPairs,
        containedOverlapPairs,
        allowedOverlayOverlapPairs,
        unexpectedOverlapPairs,
        clippedCount,
        unexpectedOverlapCount,
        contrastChecked,
        contrastFailures,
        touchChecked,
        touchFailures,
        mediaPreferenceFailures,
        failureReasons,
        pass: failureReasons.length === 0
      };
    })()
  `);
}

async function collectGeometry(win) {
  return win.webContents.executeJavaScript(`
    (() => {
      const nodes = Array.from(document.querySelectorAll("[data-geom-label]"));
      const px = value => Math.round(Number.parseFloat(String(value || "0"))) || 0;
      const rectPx = value => Number(value).toFixed(3);
      return {
        producer: "electron-chromium-geometry",
        viewport: { width: window.innerWidth, height: window.innerHeight },
        items: nodes.map((el, index) => {
          const rect = el.getBoundingClientRect();
          const style = window.getComputedStyle(el);
          const text = String(el.textContent || "").replace(/\\s+/g, " ").trim();
          return {
            index,
            label: String(el.getAttribute("data-geom-label") || ""),
            tag: el.tagName.toLowerCase(),
            x: Math.round(rect.left),
            y: Math.round(rect.top),
            width: Math.round(rect.width),
            height: Math.round(rect.height),
            rectLeft: rectPx(rect.left),
            rectTop: rectPx(rect.top),
            rectWidth: rectPx(rect.width),
            rectHeight: rectPx(rect.height),
            paddingLeft: px(style.paddingLeft),
            paddingTop: px(style.paddingTop),
            paddingRight: px(style.paddingRight),
            paddingBottom: px(style.paddingBottom),
            borderLeft: px(style.borderLeftWidth),
            borderTop: px(style.borderTopWidth),
            borderRight: px(style.borderRightWidth),
            borderBottom: px(style.borderBottomWidth),
            backgroundColor: style.backgroundColor,
            color: style.color,
            display: style.display,
            alignItems: style.alignItems,
            fontSize: style.fontSize,
            lineHeight: style.lineHeight,
            fontFamily: style.fontFamily,
            fontWeight: style.fontWeight,
            text
          };
        })
      };
    })()
  `);
}

async function main() {
  stage("main-start");
  if (!htmlPath) {
    console.error("ELECTRON_CAPTURE_HTML is required");
    process.exit(1);
  }

  stage("before-app-ready");
  await app.whenReady();
  stage("after-app-ready");
  let latestPaintImage = null;
  const win = new BrowserWindow({
    show: showWindow,
    useContentSize: true,
    width,
    height,
    backgroundColor: "#ffffff",
    webPreferences: {
      offscreen: useOffscreenPaint,
      backgroundThrottling: false,
      nodeIntegration: false,
      contextIsolation: true,
    },
  });
  if (useOffscreenPaint) {
    win.webContents.setFrameRate(30);
    win.webContents.on("paint", (_event, _dirty, image) => {
      latestPaintImage = image;
    });
  }
  win.setContentSize(width, height);

  const absHtml = path.resolve(htmlPath);
  const htmlSha256 = sha256File(absHtml);
  try {
    if (forceDataUrl) {
      stage("before-load-data-url");
      const html = fs.readFileSync(absHtml, "utf8");
      await withTimeout(
        win.loadURL("data:text/html;charset=utf-8," + encodeURIComponent(html)),
        loadTimeoutMs,
        "load-data-url"
      );
      stage("after-load-data-url");
    } else {
      stage("before-load-file");
      await withTimeout(win.loadFile(absHtml), loadTimeoutMs, "load-file");
      stage("after-load-file");
    }
  } catch (err) {
    if (continueAfterLoadTimeout && err && String(err.message || "").includes("timeout")) {
      stage("load-timeout-continue");
    } else {
    stage("load-file-failed");
    const html = fs.readFileSync(absHtml, "utf8");
    stage("before-stop-load");
    try {
      win.webContents.stop();
      stage("after-stop-load");
    } catch (_) {
      stage("stop-load-failed");
    }
    stage("before-document-write");
    await win.webContents.executeJavaScript(`
      document.open();
      document.write(${JSON.stringify(html)});
      document.close();
    `);
    stage("after-document-write");
    console.log("load_fallback=document-write");
    }
  }
  stage("before-media-features");
  await applyEmulatedMediaFeatures(win, emulatedMediaFeatures);
  stage("after-media-features");
  stage("before-settle");
  await new Promise(r => setTimeout(r, settleMs));
  stage("after-settle");

  stage("before-audit");
  const audit = await collectAudit(win, auditSelectors, emulatedMediaFeatures);
  stage("after-audit");
  stage("before-geometry");
  const geometry = geometryOutputPath ? await collectGeometry(win) : null;
  stage("after-geometry");
  stage("before-event-proof");
  const eventProof = await collectEventProof(win);
  stage("after-event-proof");
  let image = null;
  if (useOffscreenPaint && latestPaintImage) {
    stage("using-offscreen-paint");
    image = latestPaintImage;
  } else if (useOffscreenPaint) {
    stage("missing-offscreen-paint");
    throw new Error("missing-offscreen-paint");
  } else {
    stage("before-capture-page");
    image = await win.capturePage({ x: 0, y: 0, width, height });
    stage("after-capture-page");
  }
  stage("before-bitmap");
  const result = bitmapToLogicalArgb(image);
  stage("after-bitmap");
  stage("before-gpu-feature-status");
  const gpuFeatureStatus = app.getGPUFeatureStatus();
  stage("after-gpu-feature-status");
  let gpuInfo = null;
  try {
    stage("before-gpu-info");
    gpuInfo = await app.getGPUInfo("complete");
    stage("after-gpu-info");
  } catch (err) {
    stage("gpu-info-failed");
    gpuInfo = { error: err && err.message ? err.message : "gpu-info-unavailable" };
  }
  const browserTargetGpuInfo = await collectBrowserTargetGpuInfo();

  const payload = {
    width,
    height,
    format: "argb-u32",
    producer: "electron-chromium-capture",
    capture_compositor_mode: useOffscreenPaint ? "offscreen-osr-exact-srgb" : "window-capture-page",
    offscreen_paint: useOffscreenPaint,
    nativeWidth: result.nativeWidth,
    nativeHeight: result.nativeHeight,
    downsampled: result.downsampled,
    gpuFeatureStatus,
    gpuInfo,
    browserTargetGpuInfo,
    pixels: Array.from(result.pixels, v => v >>> 0),
  };
  if (audit) payload.audit = audit;
  if (geometry) payload.geometry = geometry;
  payload.event_proof = eventProof;

  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  stage("before-write-argb");
  fs.writeFileSync(outputPath, JSON.stringify(payload));
  stage("after-write-argb");
  if (pngOutputPath) {
    fs.mkdirSync(path.dirname(pngOutputPath), { recursive: true });
    fs.writeFileSync(pngOutputPath, image.toPNG());
  }
  if (audit && auditOutputPath) {
    fs.mkdirSync(path.dirname(auditOutputPath), { recursive: true });
    fs.writeFileSync(auditOutputPath, JSON.stringify(audit, null, 2));
  }
  if (geometry && geometryOutputPath) {
    fs.mkdirSync(path.dirname(geometryOutputPath), { recursive: true });
    fs.writeFileSync(geometryOutputPath, JSON.stringify(geometry, null, 2));
  }
  if (proofPath) {
    fs.mkdirSync(path.dirname(proofPath), { recursive: true });
    fs.writeFileSync(proofPath, JSON.stringify({
      status: "pass",
      reason: "pass",
      proof_source: "tools/electron-live-bitmap/capture_html_argb.js",
      html_path: absHtml,
      html_sha256: htmlSha256,
      captured_argb_path: outputPath,
      captured_argb_sha256: outputPath ? sha256File(outputPath) : "",
      width,
      height,
      native_width: result.nativeWidth,
      native_height: result.nativeHeight,
      downsampled: result.downsampled,
      capture_compositor_mode: useOffscreenPaint ? "offscreen-osr-exact-srgb" : "window-capture-page",
      offscreen_paint: useOffscreenPaint,
      captured_argb_written: Boolean(outputPath),
      png_output_path: pngOutputPath,
      png_written: Boolean(pngOutputPath),
      png_sha256: pngOutputPath ? sha256File(pngOutputPath) : "",
      geometry_written: Boolean(geometryOutputPath && geometry),
      blur_or_tolerance_used: false,
      gpu_feature_status: gpuFeatureStatus,
      gpu_info: gpuInfo,
      browser_target_gpu_info: browserTargetGpuInfo,
      browser_target_gpu_info_status: browserTargetGpuInfo && !browserTargetGpuInfo.error ? "pass" : (remoteDebuggingPort ? "fail" : "not-run"),
      remote_debugging_port: remoteDebuggingPort,
      event_proof: eventProof,
      event_status: eventProof.status,
      event_reason: eventProof.reason,
      event_sequence: Array.isArray(eventProof.sequence) ? eventProof.sequence.join(",") : "",
      focus_event_count: eventProof.focus_count || 0,
      keyboard_event_count: eventProof.keyboard_count || 0,
      input_event_count: eventProof.input_count || 0,
      pointer_down_event_count: eventProof.pointer_down_count || 0,
      pointer_up_event_count: eventProof.pointer_up_count || 0,
      click_event_count: eventProof.click_count || 0,
    }));
  }
  console.log("captured=" + outputPath);
  if (pngOutputPath) console.log("png=" + pngOutputPath);
  console.log("size=" + width + "x" + height);
  console.log("native=" + result.nativeWidth + "x" + result.nativeHeight);
  console.log("downsampled=" + result.downsampled);
  console.log("pixels=" + result.pixels.length);
  if (geometry) {
    console.log("geometry_items=" + geometry.items.length);
    if (geometryOutputPath) console.log("geometry=" + geometryOutputPath);
  }
  if (audit) {
    console.log("audit_items=" + audit.items.length);
    console.log("audit_overlaps=" + audit.overlapPairs.length);
    console.log("audit_contained_overlaps=" + audit.containedOverlapPairs.length);
    console.log("audit_allowed_overlaps=" + audit.allowedOverlayOverlapPairs.length);
    console.log("audit_unexpected_overlaps=" + audit.unexpectedOverlapCount);
    console.log("audit_clipped=" + audit.clippedCount);
    console.log("audit_contrast_checked=" + audit.contrastChecked);
    console.log("audit_contrast_failures=" + audit.contrastFailures);
    console.log("audit_touch_checked=" + audit.touchChecked);
    console.log("audit_touch_failures=" + audit.touchFailures);
    console.log("audit_media_features=" + audit.emulatedMediaFeatures.map(feature => feature.name + "=" + feature.value).join(","));
    console.log("audit_media_preference_failures=" + audit.mediaPreferenceFailures.join(","));
    console.log("audit_pass=" + audit.pass);
    console.log("audit_failure_reasons=" + audit.failureReasons.join(","));
    console.log("audit_fail_on_audit=" + failOnAudit);
    if (auditOutputPath) console.log("audit=" + auditOutputPath);
    if (failOnAudit && !audit.pass) {
      console.error("audit_failed=" + audit.failureReasons.join(","));
      process.exitCode = 2;
      app.exit(2);
      return;
    }
  }

  stage("before-quit");
  app.quit();
  stage("after-quit");
}

main().catch(e => {
  stage("error");
  console.error(e);
  process.exit(1);
});
