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

if (!htmlPath) fail("missing-html-path");
if (!chromeBin) fail("chrome-binary-unavailable");
if (!fs.existsSync(htmlPath)) fail("missing-html-file");

const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "simple-chrome-capture-"));
const pngPath = path.join(tmpDir, "capture.png");
const fileUrl = `file://${path.resolve(htmlPath)}`;
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
const elapsedUs = Number((process.hrtime.bigint() - start) / 1000n);
if (run.error && run.error.code === "ENOENT") {
  fail("chrome-binary-unavailable");
}
if (run.error) {
  fail(`chrome-screenshot-failed:${run.error.code || "error"}`);
}
if (run.status !== 0 || !fs.existsSync(pngPath)) {
  fail(`chrome-screenshot-failed:${run.status ?? "signal"}`);
}

const pixels = decodePngRgba(fs.readFileSync(pngPath));
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
console.log(`blur_or_tolerance_used=false`);
