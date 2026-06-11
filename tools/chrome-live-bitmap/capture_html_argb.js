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
  for (const name of ["google-chrome", "google-chrome-stable", "chromium", "chromium-browser"]) {
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
    captured_argb_written: false,
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
  return Number(sum);
}

function weightedChecksum(pixels) {
  let sum = 0n;
  for (let i = 0; i < pixels.length; i += 1) {
    sum += BigInt(pixels[i] >>> 0) * BigInt(i + 1);
  }
  return Number(sum);
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

function geometryExpression() {
  return `
    (() => {
      const nodes = Array.from(document.querySelectorAll("[data-geom-label]"));
      const px = value => Math.round(Number.parseFloat(String(value || "0"))) || 0;
      return {
        producer: "chrome-headless-geometry",
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
            paddingLeft: px(style.paddingLeft),
            paddingTop: px(style.paddingTop),
            paddingRight: px(style.paddingRight),
            paddingBottom: px(style.paddingBottom),
            borderLeft: px(style.borderLeftWidth),
            borderTop: px(style.borderTopWidth),
            borderRight: px(style.borderRightWidth),
            borderBottom: px(style.borderBottomWidth),
            backgroundColor: style.backgroundColor,
            text
          };
        })
      };
    })()
  `;
}

async function captureViaDevTools(fileUrl) {
  const userDataDir = fs.mkdtempSync(path.join(os.tmpdir(), "simple-chrome-cdp-profile-"));
  const args = [
    "--headless=new",
    "--disable-gpu",
    "--no-sandbox",
    "--force-device-scale-factor=1",
    "--force-color-profile=srgb",
    `--window-size=${width},${height}`,
    "--remote-debugging-port=0",
    `--user-data-dir=${userDataDir}`,
    fileUrl,
  ];
  const start = process.hrtime.bigint();
  const child = childProcess.spawn(chromeBin, args, { stdio: ["ignore", "ignore", "pipe"] });
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
  try {
    const listUrl = endpoint.replace(/^ws:/, "http:").replace(/\/devtools\/browser\/.*$/, "/json");
    const pages = await (await fetch(listUrl)).json();
    const page = pages.find(item => item.type === "page") || pages[0];
    if (!page || !page.webSocketDebuggerUrl) throw new Error("chrome-page-target-missing");
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
    const geomEval = await cdpSend(conn, id++, "Runtime.evaluate", {
      expression: geometryExpression(),
      returnByValue: true,
      awaitPromise: true,
    });
    const geometry = geomEval.result ? geomEval.result.value : null;
    const shot = await cdpSend(conn, id++, "Page.captureScreenshot", { format: "png", fromSurface: true });
    const elapsedUs = Number((process.hrtime.bigint() - start) / 1000n);
    return { png: Buffer.from(shot.data || "", "base64"), geometry, elapsedUs };
  } finally {
    if (conn) conn.socket.destroy();
    child.kill();
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
let elapsedUs = 0;
if (geometryOutputPath) {
  captureViaDevTools(fileUrl).then(capture => {
    pngBuffer = capture.png;
    geometry = capture.geometry;
    elapsedUs = capture.elapsedUs;
    finish();
  }).catch(err => fail(`chrome-devtools-capture-failed:${err.message || "error"}`));
} else {
  const args = [
    "--headless=new",
    "--disable-gpu",
    "--no-sandbox",
    "--force-device-scale-factor=1",
    "--force-color-profile=srgb",
    `--window-size=${width},${height}`,
    `--screenshot=${pngPath}`,
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
  checksum: actualChecksum,
  expected_checksum: expectedChecksum,
  weighted_checksum: actualWeighted,
  expected_weighted_checksum: expectedWeighted,
  mismatch_count: mismatchCount,
  frame_us: elapsedUs,
  captured_argb_written: Boolean(outputPath),
  geometry_written: Boolean(geometryOutputPath && geometry),
  blur_or_tolerance_used: false,
  chrome_bin: chromeBin,
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
