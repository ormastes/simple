#!/usr/bin/env node
"use strict";

const width = Number(process.env.NODE_BITMAP_WIDTH || 96);
const height = Number(process.env.NODE_BITMAP_HEIGHT || 64);
const iterations = Number(process.env.NODE_BITMAP_ITERATIONS || 5);
const runtime = process.env.JS_RENDER_RUNTIME || "node";

function makeFrame() {
  const pixels = new Uint32Array(width * height);
  pixels.fill(10);
  rect(pixels, 0, 0, width, 8, 20);
  rect(pixels, 4, 2, 18, 6, 30);
  rect(pixels, 28, 2, 14, 4, 40);
  rect(pixels, 78, 2, 10, 4, 50);
  rect(pixels, 0, height - 10, width, 10, 60);
  rect(pixels, 5, height - 8, 10, 6, 70);
  rect(pixels, 20, height - 8, 18, 6, 80);
  rect(pixels, 44, height - 8, 18, 6, 90);
  rect(pixels, 14, 18, 28, 18, 100);
  rect(pixels, 16, 20, 24, 14, 110);
  rect(pixels, 56, 18, 24, 18, 120);
  rect(pixels, 59, 21, 18, 12, 130);
  diag(pixels, 60, 22, 16, 140);
  return pixels;
}

function rect(pixels, x, y, w, h, color) {
  for (let yy = y; yy < y + h; yy += 1) {
    if (yy < 0 || yy >= height) continue;
    for (let xx = x; xx < x + w; xx += 1) {
      if (xx < 0 || xx >= width) continue;
      pixels[yy * width + xx] = color >>> 0;
    }
  }
}

function diag(pixels, x, y, count, color) {
  for (let i = 0; i < count; i += 1) {
    const xx = x + i;
    const yy = y + i;
    if (xx >= 0 && xx < width && yy >= 0 && yy < height) {
      pixels[yy * width + xx] = color >>> 0;
    }
  }
}

function checksum(pixels) {
  let sum = 0n;
  for (const px of pixels) {
    sum += BigInt(px >>> 0);
  }
  return sum;
}

const warm = makeFrame();
let total = 0n;
const start = process.hrtime.bigint();
for (let i = 0; i < iterations; i += 1) {
  total += checksum(makeFrame());
}
const elapsed = process.hrtime.bigint() - start;
const frameUs = elapsed > 0n ? Number(elapsed / BigInt(iterations) / 1000n) : 1;

console.log(`renderer=${runtime}-exact-fixture`);
console.log(`width=${width}`);
console.log(`height=${height}`);
console.log(`iterations=${iterations}`);
console.log(`checksum=${checksum(warm).toString()}`);
console.log(`total_checksum=${total.toString()}`);
console.log(`frame_us=${frameUs > 0 ? frameUs : 1}`);
console.log(`blur_or_tolerance_used=false`);
