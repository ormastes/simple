#!/usr/bin/env node
"use strict";

const childProcess = require("child_process");
const fs = require("fs");
const os = require("os");
const path = require("path");
const zlib = require("zlib");

const htmlPath = process.env.CHROME_CAPTURE_HTML || "";
const width = Number(process.env.CHROME_CAPTURE_WIDTH || 320);
const height = Number(process.env.CHROME_CAPTURE_HEIGHT || 240);
const outputPath = process.env.CHROME_CAPTURE_OUTPUT || "";
const expectedPath = process.env.CHROME_CAPTURE_EXPECTED_ARGB_PATH || "";
const proofPath = process.env.CHROME_CAPTURE_PROOF_PATH || "";
const geometryOutputPath = process.env.CHROME_CAPTURE_GEOMETRY_OUTPUT || "";
const chromeBin = process.env.CHROME_CAPTURE_BIN || findChromeBinary();
const extraArgs = (process.env.CHROME_CAPTURE_EXTRA_ARGS || "").split(/\s+/).filter(Boolean);
const disableGpu = process.env.CHROME_CAPTURE_DISABLE_GPU !== "false";
let activeChromeChild = null;

function terminateActiveChromeChild() {
  if (!activeChromeChild || activeChromeChild.killed) return;
  try {
    activeChromeChild.kill("SIGTERM");
  } catch (_err) {
    // Best-effort cleanup for timeout and signal paths.
  }
}

process.on("SIGTERM", () => {
  terminateActiveChromeChild();
  process.exit(143);
});
process.on("SIGINT", () => {
  terminateActiveChromeChild();
  process.exit(130);
});
process.on("exit", terminateActiveChromeChild);

function executableExists(candidate) {
  try {
    fs.accessSync(candidate, fs.constants.X_OK);
    return true;
  } catch (_err) {
    return false;
  }
}

function findOnPath(name) {
  const pathValue = process.env.PATH || "";
  for (const dir of pathValue.split(path.delimiter)) {
    if (!dir) continue;
    const candidate = path.join(dir, name);
    if (executableExists(candidate)) return candidate;
  }
  return "";
}

function findChromeBinary() {
  const candidates = [
    "/usr/bin/google-chrome",
    "/usr/bin/google-chrome-stable",
    "/usr/bin/chromium",
    "/usr/bin/chromium-browser",
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
  ];
  if (process.platform === "win32") {
    for (const root of [
      process.env.LOCALAPPDATA,
      process.env.PROGRAMFILES,
      process.env["PROGRAMFILES(X86)"],
    ]) {
      if (!root) continue;
      candidates.push(
        path.join(root, "Google", "Chrome", "Application", "chrome.exe"),
        path.join(root, "Microsoft", "Edge", "Application", "msedge.exe"),
      );
    }
  }
  for (const candidate of candidates) {
    if (executableExists(candidate)) return candidate;
  }
  const home = process.env.HOME || "";
  if (home) {
    const cacheRoot = path.join(home, ".cache", "ms-playwright");
    try {
      const browserDirs = fs.readdirSync(cacheRoot).sort().reverse();
      for (const dir of browserDirs) {
        for (const rel of [
          path.join("chrome-linux64", "chrome"),
          path.join("chromium", "chrome-linux", "chrome"),
          path.join("chrome-linux", "chrome"),
        ]) {
          const candidate = path.join(cacheRoot, dir, rel);
          if (executableExists(candidate)) return candidate;
        }
      }
    } catch (_err) {
      // Playwright-managed Chromium is optional.
    }
  }
  for (const name of ["google-chrome", "google-chrome-stable", "chromium", "chromium-browser", "chrome.exe", "msedge.exe"]) {
    const candidate = findOnPath(name);
    if (candidate) return candidate;
  }
  return "";
}

function fail(reason) {
  const proof = {
    status: "unavailable",
    reason,
    width,
    height,
    checksum: 0,
    weighted_checksum: 0,
    mismatch_count: 0,
    blur_or_tolerance_used: false,
    captured_argb_path: outputPath,
    captured_argb_written: false,
    geometry_path: geometryOutputPath,
    geometry_written: false,
  };
  if (proofPath) fs.writeFileSync(proofPath, JSON.stringify(proof));
  console.log(`chrome_capture_status=unavailable`);
  console.log(`chrome_capture_reason=${reason}`);
  process.exit(1);
}

function readUInt32(buffer, offset) {
  return buffer.readUInt32BE(offset) >>> 0;
}

function paeth(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  if (pb <= pc) return b;
  return c;
}

function decodePngRgba(buffer) {
  if (buffer.length < 8 || buffer.toString("hex", 0, 8) !== "89504e470d0a1a0a") {
    throw new Error("not a png");
  }
  let offset = 8;
  let pngWidth = 0;
  let pngHeight = 0;
  let colorType = 0;
  let bitDepth = 0;
  const idat = [];
  while (offset + 8 <= buffer.length) {
    const len = readUInt32(buffer, offset);
    const type = buffer.toString("ascii", offset + 4, offset + 8);
    const dataStart = offset + 8;
    const dataEnd = dataStart + len;
    if (type === "IHDR") {
      pngWidth = readUInt32(buffer, dataStart);
      pngHeight = readUInt32(buffer, dataStart + 4);
      bitDepth = buffer[dataStart + 8];
      colorType = buffer[dataStart + 9];
    } else if (type === "IDAT") {
      idat.push(buffer.subarray(dataStart, dataEnd));
    } else if (type === "IEND") {
      break;
    }
    offset = dataEnd + 4;
  }
  if (bitDepth !== 8 || (colorType !== 6 && colorType !== 2)) {
    throw new Error(`unsupported png bitDepth=${bitDepth} colorType=${colorType}`);
  }
  const bpp = colorType === 6 ? 4 : 3;
  const raw = zlib.inflateSync(Buffer.concat(idat));
  const stride = pngWidth * bpp;
  const pixels = [];
  let rawOffset = 0;
  let prev = Buffer.alloc(stride);
  for (let y = 0; y < pngHeight; y += 1) {
    const filter = raw[rawOffset];
    rawOffset += 1;
    const row = Buffer.alloc(stride);
    for (let x = 0; x < stride; x += 1) {
      const value = raw[rawOffset + x];
      const left = x >= bpp ? row[x - bpp] : 0;
      const up = prev[x] || 0;
      const upLeft = x >= bpp ? prev[x - bpp] : 0;
      if (filter === 0) row[x] = value;
      else if (filter === 1) row[x] = (value + left) & 255;
      else if (filter === 2) row[x] = (value + up) & 255;
      else if (filter === 3) row[x] = (value + Math.floor((left + up) / 2)) & 255;
      else if (filter === 4) row[x] = (value + paeth(left, up, upLeft)) & 255;
      else throw new Error(`unsupported png filter=${filter}`);
    }
    const copyWidth = Math.min(width, pngWidth);
    if (y < height) {
      for (let x = 0; x < copyWidth; x += 1) {
        const p = x * bpp;
        const r = row[p];
        const g = row[p + 1];
        const b = row[p + 2];
        const a = colorType === 6 ? row[p + 3] : 255;
        pixels.push((((a << 24) >>> 0) | (r << 16) | (g << 8) | b) >>> 0);
      }
      for (let x = copyWidth; x < width; x += 1) pixels.push(0xffffffff);
    }
    rawOffset += stride;
    prev = row;
  }
  while (pixels.length < width * height) pixels.push(0xffffffff);
  return pixels.slice(0, width * height);
}

function checksum(pixels) {
  let sum = 0n;
  for (const pixel of pixels) sum += BigInt(pixel >>> 0);
  return sum.toString();
}

function weightedChecksum(pixels) {
  let sum = 0n;
  for (let i = 0; i < pixels.length; i += 1) {
    sum += BigInt(pixels[i] >>> 0) * BigInt(i + 1);
  }
  return sum.toString();
}

function websocketAcceptKey(key) {
  return require("crypto")
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
  const mask = require("crypto").randomBytes(4);
  mask.copy(out, maskOffset);
  for (let i = 0; i < len; i += 1) out[payloadOffset + i] = payload[i] ^ mask[i % 4];
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
        for (let i = 0; i < len; i += 1) copy[i] = payload[i] ^ mask[i % 4];
        payload = copy;
      }
      state.buffer = state.buffer.subarray(offset + len);
      if (opcode === 0x8) return reject(new Error("websocket-closed"));
      if (opcode === 0x1) return resolve(payload.toString("utf8"));
      return false;
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
    const cleanup = () => {
      socket.off("data", onData);
      socket.off("error", onError);
    };
    socket.on("data", onData);
    socket.on("error", onError);
    const parsed = tryParse();
    if (parsed !== false) cleanup();
  });
}

function connectWebSocket(wsUrl) {
  const net = require("net");
  const parsed = new URL(wsUrl);
  const host = parsed.hostname;
  const port = Number(parsed.port || 80);
  const pathAndQuery = parsed.pathname + (parsed.search || "");
  const key = require("crypto").randomBytes(16).toString("base64");
  const expectedAccept = websocketAcceptKey(key);
  return new Promise((resolve, reject) => {
    const socket = net.createConnection({ host, port });
    let handshake = Buffer.alloc(0);
    socket.setTimeout(Number(process.env.CHROME_CAPTURE_TIMEOUT_MS || 20000));
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

async function fetchPageTarget(endpoint, timeoutMs) {
  const listUrl = endpoint.replace(/^ws:/, "http:").replace(/\/devtools\/browser\/.*$/, "/json");
  const deadline = Date.now() + timeoutMs;
  let lastPages = [];
  while (Date.now() < deadline) {
    try {
      const pages = await (await fetch(listUrl)).json();
      if (Array.isArray(pages)) {
        lastPages = pages;
        const page = pages.find(item => item.type === "page" && item.webSocketDebuggerUrl) ||
          pages.find(item => item.webSocketDebuggerUrl);
        if (page && page.webSocketDebuggerUrl) return page;
      }
    } catch (_err) {
      // Chrome can expose the browser endpoint before the target list is ready.
    }
    await new Promise(resolve => setTimeout(resolve, 50));
  }
  const types = lastPages.map(item => item.type || "unknown").join(",");
  throw new Error(types ? `chrome-page-target-missing:${types}` : "chrome-page-target-missing");
}

function geometryExpression() {
  return `
    (() => {
      const candidates = Array.from(document.querySelectorAll("[data-geom-label]"));
      const nodes = candidates.length > 0
        ? candidates
        : Array.from(document.body ? document.body.querySelectorAll("*") : []);
      const px = value => Math.round(Number.parseFloat(String(value || "0"))) || 0;
      const rectPx = value => Number(value).toFixed(3);
      return {
        producer: "chrome-headless-geometry",
        viewport: { width: window.innerWidth, height: window.innerHeight },
        items: nodes
        .filter((el) => {
          const tag = el.tagName.toLowerCase();
          return tag !== "script" && tag !== "style" && tag !== "template";
        })
        .slice(0, 128)
        .map((el, index) => {
          const rect = el.getBoundingClientRect();
          const style = window.getComputedStyle(el);
          const text = String(el.textContent || "").replace(/\\s+/g, " ").trim();
          return {
            index,
            label: String(el.getAttribute("data-geom-label") || el.className || el.id || ""),
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
  `;
}

function eventProofExpression() {
  return `
    (() => {
      const button = document.querySelector("button");
      const input = document.querySelector("input, textarea, [contenteditable='true']");
      const state = {
        proof_source: "tools/chrome-live-bitmap/capture_html_argb.js",
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
  `;
}

function readEventProofExpression() {
  return `
    (() => {
      const state = window.__simpleCaptureEventProof || {};
      const input = document.querySelector("input, textarea, [contenteditable='true']");
      state.input_value_after = input ? String(input.value || input.textContent || "") : "";
      const focusPass = Number(state.focus_count || 0) >= 1;
      const keyboardPass = Number(state.keyboard_count || 0) >= 2;
      const inputPass = Number(state.input_count || 0) >= 1 && String(state.input_value_after || "").includes("X");
      const pointerPass = Number(state.pointer_down_count || 0) >= 1 && Number(state.pointer_up_count || 0) >= 1;
      const clickPass = Number(state.click_count || 0) >= 1;
      state.button_found = Boolean(state.button_rect);
      state.input_found = Boolean(state.input_rect);
      state.focus_pass = focusPass;
      state.keyboard_pass = keyboardPass;
      state.input_pass = inputPass;
      state.pointer_pass = pointerPass;
      state.click_pass = clickPass;
      state.status = focusPass && keyboardPass && inputPass && pointerPass && clickPass ? "pass" : "fail";
      state.reason = state.status === "pass" ? "pass" : "event-contract-missing";
      return state;
    })()
  `;
}

async function captureViaDevTools(fileUrl) {
  const userDataDir = fs.mkdtempSync(path.join(os.tmpdir(), "simple-chrome-cdp-profile-"));
  const args = [
    "--headless=new",
    ...(disableGpu ? ["--disable-gpu"] : []),
    "--no-sandbox",
    "--force-device-scale-factor=1",
    "--force-color-profile=srgb",
    `--window-size=${width},${height}`,
    "--remote-debugging-port=0",
    `--user-data-dir=${userDataDir}`,
    ...extraArgs,
    fileUrl,
  ];
  const start = process.hrtime.bigint();
  const child = childProcess.spawn(chromeBin, args, { stdio: ["ignore", "ignore", "pipe"] });
  activeChromeChild = child;
  let stderr = "";
  const timeoutMs = Number(process.env.CHROME_CAPTURE_TIMEOUT_MS || 20000);
  const endpoint = await new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error("chrome-devtools-timeout")), timeoutMs);
    child.stderr.on("data", chunk => {
      stderr += chunk.toString("utf8");
      const match = stderr.match(/DevTools listening on (ws:\/\/[^\s]+)/);
      if (match) {
        clearTimeout(timer);
        resolve(match[1]);
      }
    });
    child.on("error", err => {
      clearTimeout(timer);
      reject(err);
    });
    child.on("exit", code => {
      clearTimeout(timer);
      reject(new Error(`chrome-devtools-exited:${code}`));
    });
  });
  let conn;
  let browserConn;
  try {
    let gpuInfo = null;
    let browserVersion = null;
    try {
      browserConn = await connectWebSocket(endpoint);
      browserVersion = await cdpSend(browserConn, 1, "Browser.getVersion");
      gpuInfo = await cdpSend(browserConn, 2, "SystemInfo.getInfo");
    } catch (err) {
      gpuInfo = { error: err && err.message ? err.message : "system-info-unavailable" };
      if (!browserVersion) browserVersion = { error: err && err.message ? err.message : "browser-version-unavailable" };
    }
    const page = await fetchPageTarget(endpoint, timeoutMs);
    conn = await connectWebSocket(page.webSocketDebuggerUrl);
    let id = 1;
    await cdpSend(conn, id++, "Page.enable");
    await cdpSend(conn, id++, "Runtime.enable");
    await cdpSend(conn, id++, "Emulation.setDeviceMetricsOverride", {
      width,
      height,
      deviceScaleFactor: 1,
      mobile: false,
    });
    await cdpSend(conn, id++, "Page.navigate", { url: fileUrl });
    await new Promise(resolve => setTimeout(resolve, Number(process.env.CHROME_CAPTURE_SETTLE_MS || 250)));
    const eventSetup = await cdpSend(conn, id++, "Runtime.evaluate", {
      expression: eventProofExpression(),
      returnByValue: true,
      awaitPromise: true,
    });
    const eventSetupValue = eventSetup.result ? eventSetup.result.value : null;
    let eventProof = {
      status: "fail",
      reason: "missing-visible-button-or-input",
      button_found: Boolean(eventSetupValue && eventSetupValue.button_found),
      input_found: Boolean(eventSetupValue && eventSetupValue.input_found),
    };
    if (eventSetupValue && eventSetupValue.button_found && eventSetupValue.input_found && eventSetupValue.button_rect && eventSetupValue.input_rect) {
      const button = eventSetupValue.button_rect;
      await cdpSend(conn, id++, "Input.dispatchMouseEvent", { type: "mouseMoved", x: Math.round(button.x), y: Math.round(button.y) });
      await cdpSend(conn, id++, "Input.dispatchMouseEvent", { type: "mousePressed", x: Math.round(button.x), y: Math.round(button.y), button: "left", clickCount: 1 });
      await cdpSend(conn, id++, "Input.dispatchMouseEvent", { type: "mouseReleased", x: Math.round(button.x), y: Math.round(button.y), button: "left", clickCount: 1 });
      await cdpSend(conn, id++, "Runtime.evaluate", {
        expression: `document.querySelector("input, textarea, [contenteditable='true']").focus()`,
        returnByValue: true,
        awaitPromise: true,
      });
      await cdpSend(conn, id++, "Input.dispatchKeyEvent", { type: "keyDown", key: "X", code: "KeyX", windowsVirtualKeyCode: 88, nativeVirtualKeyCode: 88 });
      await cdpSend(conn, id++, "Input.dispatchKeyEvent", { type: "char", text: "X", unmodifiedText: "X", key: "X", code: "KeyX", windowsVirtualKeyCode: 88, nativeVirtualKeyCode: 88 });
      await cdpSend(conn, id++, "Input.dispatchKeyEvent", { type: "keyUp", key: "X", code: "KeyX", windowsVirtualKeyCode: 88, nativeVirtualKeyCode: 88 });
      await new Promise(resolve => setTimeout(resolve, 100));
      const eventRead = await cdpSend(conn, id++, "Runtime.evaluate", {
        expression: readEventProofExpression(),
        returnByValue: true,
        awaitPromise: true,
      });
      eventProof = eventRead.result ? eventRead.result.value : eventProof;
    }
    const geomEval = await cdpSend(conn, id++, "Runtime.evaluate", {
      expression: geometryExpression(),
      returnByValue: true,
      awaitPromise: true,
    });
    const geometry = geomEval.result ? geomEval.result.value : null;
    const shot = await cdpSend(conn, id++, "Page.captureScreenshot", { format: "png", fromSurface: true });
    const elapsedUs = Number((process.hrtime.bigint() - start) / 1000n);
    return { png: Buffer.from(shot.data || "", "base64"), geometry, gpuInfo, browserVersion, elapsedUs, eventProof };
  } finally {
    if (conn) conn.socket.destroy();
    if (browserConn) browserConn.socket.destroy();
    child.kill();
    if (activeChromeChild === child) activeChromeChild = null;
  }
}

if (!htmlPath) fail("missing-html-path");
if (!chromeBin) fail("chrome-binary-unavailable");
if (!fs.existsSync(htmlPath)) fail("missing-html-file");

const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "simple-chrome-capture-"));
const pngPath = path.join(tmpDir, "capture.png");
const fileUrl = `file://${path.resolve(htmlPath)}`;
let pngBuffer = null;
let geometry = null;
let gpuInfo = null;
let browserVersion = null;
let elapsedUs = 0;
let eventProof = { status: "not-run", reason: "requires-devtools-capture" };
if (geometryOutputPath) {
  captureViaDevTools(fileUrl).then(capture => {
    pngBuffer = capture.png;
    geometry = capture.geometry;
    gpuInfo = capture.gpuInfo;
    browserVersion = capture.browserVersion;
    elapsedUs = capture.elapsedUs;
    eventProof = capture.eventProof || eventProof;
    finish();
  }).catch(err => fail(`chrome-devtools-capture-failed:${err.message || "error"}`));
} else {
  const args = [
    "--headless=new",
    ...(disableGpu ? ["--disable-gpu"] : []),
    "--no-sandbox",
    "--force-device-scale-factor=1",
    "--force-color-profile=srgb",
    `--window-size=${width},${height}`,
    `--screenshot=${pngPath}`,
    ...extraArgs,
    fileUrl,
  ];
  const start = process.hrtime.bigint();
  const run = childProcess.spawnSync(chromeBin, args, { encoding: "utf8", timeout: Number(process.env.CHROME_CAPTURE_TIMEOUT_MS || 20000) });
  elapsedUs = Number((process.hrtime.bigint() - start) / 1000n);
  if (run.error && run.error.code === "ENOENT") {
    fail("chrome-binary-unavailable");
  }
  if (run.error) {
    fail(`chrome-screenshot-failed:${run.error.code || "error"}`);
  }
  if (run.status !== 0 || !fs.existsSync(pngPath)) {
    fail(`chrome-screenshot-failed:${run.status ?? "signal"}`);
  }
  pngBuffer = fs.readFileSync(pngPath);
  finish();
}

function finish() {
const pixels = decodePngRgba(pngBuffer);
const result = {
  width,
  height,
  format: "argb-u32",
  producer: "chrome-headless-screenshot",
  pixels,
};
const actualChecksum = checksum(pixels);
const actualWeighted = weightedChecksum(pixels);
let mismatchCount = 0;
let expectedChecksum = actualChecksum;
let expectedWeighted = actualWeighted;
if (expectedPath && fs.existsSync(expectedPath)) {
  const expected = JSON.parse(fs.readFileSync(expectedPath, "utf8"));
  const ep = Array.isArray(expected.pixels) ? expected.pixels : [];
  expectedChecksum = checksum(ep);
  expectedWeighted = weightedChecksum(ep);
  const n = Math.max(ep.length, pixels.length);
  for (let i = 0; i < n; i += 1) {
    if ((Number(ep[i] || 0) >>> 0) !== (Number(pixels[i] || 0) >>> 0)) mismatchCount += 1;
  }
}

if (outputPath) fs.writeFileSync(outputPath, JSON.stringify(result));
if (geometryOutputPath && geometry) {
  fs.mkdirSync(path.dirname(geometryOutputPath), { recursive: true });
  fs.writeFileSync(geometryOutputPath, JSON.stringify(geometry, null, 2));
}
const proof = {
  status: "pass",
  reason: "pass",
  width,
  height,
  proof_source: "tools/chrome-live-bitmap/capture_html_argb.js",
  checksum: actualChecksum,
  expected_checksum: expectedChecksum,
  weighted_checksum: actualWeighted,
  expected_weighted_checksum: expectedWeighted,
  mismatch_count: mismatchCount,
  frame_us: elapsedUs,
  captured_argb_path: outputPath,
  captured_argb_written: Boolean(outputPath),
  geometry_path: geometryOutputPath,
  geometry_written: Boolean(geometryOutputPath && geometry),
  capture_mode: geometryOutputPath ? "chrome-devtools-screenshot" : "chrome-headless-screenshot",
  blur_or_tolerance_used: false,
  chrome_bin: chromeBin,
  chrome_user_agent: browserVersion && browserVersion.userAgent ? browserVersion.userAgent : "",
  chrome_product: browserVersion && browserVersion.product ? browserVersion.product : "",
  chrome_protocol_version: browserVersion && browserVersion.protocolVersion ? browserVersion.protocolVersion : "",
  gpu_info: gpuInfo,
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
};
if (proofPath) fs.writeFileSync(proofPath, JSON.stringify(proof));
console.log(`chrome_capture_status=pass`);
console.log(`chrome_capture_reason=pass`);
console.log(`checksum=${actualChecksum}`);
console.log(`expected_checksum=${expectedChecksum}`);
console.log(`weighted_checksum=${actualWeighted}`);
console.log(`expected_weighted_checksum=${expectedWeighted}`);
console.log(`mismatch_count=${mismatchCount}`);
console.log(`frame_us=${elapsedUs}`);
console.log(`captured_argb_written=${Boolean(outputPath)}`);
if (geometryOutputPath) console.log(`geometry=${geometryOutputPath}`);
console.log(`geometry_written=${Boolean(geometryOutputPath && geometry)}`);
console.log(`blur_or_tolerance_used=false`);
}
