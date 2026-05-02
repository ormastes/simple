#!/usr/bin/env node
// Dependency-free PNG pixel comparer for visual regression artifacts.
// Supports non-interlaced 8-bit RGB/RGBA/greyscale PNGs emitted by Playwright.

const fs = require('fs');
const path = require('path');
const zlib = require('zlib');

const PNG_SIG = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]);

function crc32(buf) {
  let c = ~0;
  for (let i = 0; i < buf.length; i++) {
    c ^= buf[i];
    for (let k = 0; k < 8; k++) c = (c >>> 1) ^ (0xedb88320 & -(c & 1));
  }
  return (~c) >>> 0;
}

function readPng(file) {
  const buf = fs.readFileSync(file);
  if (!buf.subarray(0, 8).equals(PNG_SIG)) throw new Error(`${file}: not a PNG`);

  let off = 8;
  let width = 0, height = 0, bitDepth = 0, colorType = 0, interlace = 0;
  const idat = [];
  while (off < buf.length) {
    const len = buf.readUInt32BE(off); off += 4;
    const type = buf.subarray(off, off + 4).toString('ascii'); off += 4;
    const data = buf.subarray(off, off + len); off += len + 4;
    if (type === 'IHDR') {
      width = data.readUInt32BE(0);
      height = data.readUInt32BE(4);
      bitDepth = data[8];
      colorType = data[9];
      interlace = data[12];
    } else if (type === 'IDAT') {
      idat.push(data);
    } else if (type === 'IEND') {
      break;
    }
  }
  if (bitDepth !== 8 || interlace !== 0) {
    throw new Error(`${file}: only non-interlaced 8-bit PNGs are supported`);
  }

  const channels = colorType === 6 ? 4 : colorType === 2 ? 3 : colorType === 0 ? 1 : 0;
  if (!channels) throw new Error(`${file}: unsupported PNG color type ${colorType}`);

  const raw = zlib.inflateSync(Buffer.concat(idat));
  const stride = width * channels;
  const pixels = Buffer.alloc(width * height * 4);
  let src = 0;
  let prev = Buffer.alloc(stride);
  let cur = Buffer.alloc(stride);

  for (let y = 0; y < height; y++) {
    const filter = raw[src++];
    raw.copy(cur, 0, src, src + stride);
    src += stride;
    unfilter(cur, prev, channels, filter);
    for (let x = 0; x < width; x++) {
      const si = x * channels;
      const di = (y * width + x) * 4;
      if (channels === 4) {
        pixels[di] = cur[si];
        pixels[di + 1] = cur[si + 1];
        pixels[di + 2] = cur[si + 2];
        pixels[di + 3] = cur[si + 3];
      } else if (channels === 3) {
        pixels[di] = cur[si];
        pixels[di + 1] = cur[si + 1];
        pixels[di + 2] = cur[si + 2];
        pixels[di + 3] = 255;
      } else {
        pixels[di] = cur[si];
        pixels[di + 1] = cur[si];
        pixels[di + 2] = cur[si];
        pixels[di + 3] = 255;
      }
    }
    const tmp = prev; prev = cur; cur = tmp; cur.fill(0);
  }
  return { width, height, pixels };
}

function unfilter(row, prev, bpp, filter) {
  for (let i = 0; i < row.length; i++) {
    const left = i >= bpp ? row[i - bpp] : 0;
    const up = prev[i] || 0;
    const upLeft = i >= bpp ? prev[i - bpp] || 0 : 0;
    if (filter === 1) row[i] = (row[i] + left) & 255;
    else if (filter === 2) row[i] = (row[i] + up) & 255;
    else if (filter === 3) row[i] = (row[i] + Math.floor((left + up) / 2)) & 255;
    else if (filter === 4) row[i] = (row[i] + paeth(left, up, upLeft)) & 255;
    else if (filter !== 0) throw new Error(`unsupported PNG filter ${filter}`);
  }
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

function chunk(type, data) {
  const typeBuf = Buffer.from(type, 'ascii');
  const len = Buffer.alloc(4);
  len.writeUInt32BE(data.length, 0);
  const crc = Buffer.alloc(4);
  crc.writeUInt32BE(crc32(Buffer.concat([typeBuf, data])), 0);
  return Buffer.concat([len, typeBuf, data, crc]);
}

function writePng(file, width, height, rgba) {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(width, 0);
  ihdr.writeUInt32BE(height, 4);
  ihdr[8] = 8;
  ihdr[9] = 6;
  ihdr[10] = 0;
  ihdr[11] = 0;
  ihdr[12] = 0;

  const stride = width * 4;
  const raw = Buffer.alloc((stride + 1) * height);
  for (let y = 0; y < height; y++) {
    const ro = y * (stride + 1);
    raw[ro] = 0;
    rgba.copy(raw, ro + 1, y * stride, y * stride + stride);
  }
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, Buffer.concat([
    PNG_SIG,
    chunk('IHDR', ihdr),
    chunk('IDAT', zlib.deflateSync(raw)),
    chunk('IEND', Buffer.alloc(0)),
  ]));
}

function compare(aPath, bPath, diffPath, jsonPath) {
  const a = readPng(aPath);
  const b = readPng(bPath);
  if (a.width !== b.width || a.height !== b.height) {
    throw new Error(`dimension mismatch: ${a.width}x${a.height} vs ${b.width}x${b.height}`);
  }
  const diff = Buffer.alloc(a.pixels.length);
  let changed = 0;
  let sumAbs = 0;
  let maxDelta = 0;
  for (let i = 0; i < a.pixels.length; i += 4) {
    const dr = Math.abs(a.pixels[i] - b.pixels[i]);
    const dg = Math.abs(a.pixels[i + 1] - b.pixels[i + 1]);
    const db = Math.abs(a.pixels[i + 2] - b.pixels[i + 2]);
    const da = Math.abs(a.pixels[i + 3] - b.pixels[i + 3]);
    const delta = Math.max(dr, dg, db, da);
    if (delta > 0) changed++;
    sumAbs += dr + dg + db + da;
    maxDelta = Math.max(maxDelta, delta);
    diff[i] = delta ? 255 : a.pixels[i] >> 2;
    diff[i + 1] = delta ? Math.max(32, 255 - delta) : a.pixels[i + 1] >> 2;
    diff[i + 2] = delta ? 0 : a.pixels[i + 2] >> 2;
    diff[i + 3] = 255;
  }
  const total = a.width * a.height;
  const stats = {
    a: aPath,
    b: bPath,
    width: a.width,
    height: a.height,
    total_pixels: total,
    changed_pixels: changed,
    changed_ratio: Number((changed / total).toFixed(6)),
    exact_match_ratio: Number(((total - changed) / total).toFixed(6)),
    mean_abs_channel_delta: Number((sumAbs / (total * 4)).toFixed(4)),
    max_channel_delta: maxDelta,
    diff: diffPath,
  };
  writePng(diffPath, a.width, a.height, diff);
  if (jsonPath) {
    fs.mkdirSync(path.dirname(jsonPath), { recursive: true });
    fs.writeFileSync(jsonPath, `${JSON.stringify(stats, null, 2)}\n`);
  }
  console.log(JSON.stringify(stats, null, 2));
}

const [aPath, bPath, diffPath, jsonPath] = process.argv.slice(2);
if (!aPath || !bPath || !diffPath) {
  console.error('Usage: node tools/visual/compare_png_pixels.js <a.png> <b.png> <diff.png> [stats.json]');
  process.exit(2);
}
compare(aPath, bPath, diffPath, jsonPath);
