#!/usr/bin/env node

const fs = require('fs');

function usage() {
  console.error('Usage: node tools/electron-shell/analyze_ppm_delta.js <expected.ppm> <actual.ppm> [chrome_metrics.json]');
  process.exit(2);
}

function isWs(byte) {
  return byte === 9 || byte === 10 || byte === 13 || byte === 32;
}

function readPpm(path) {
  const bytes = fs.readFileSync(path);
  let pos = 0;

  function token() {
    while (pos < bytes.length && isWs(bytes[pos])) pos += 1;
    if (bytes[pos] === 35) {
      while (pos < bytes.length && bytes[pos] !== 10) pos += 1;
      return token();
    }
    let out = '';
    while (pos < bytes.length && !isWs(bytes[pos])) {
      out += String.fromCharCode(bytes[pos]);
      pos += 1;
    }
    return out;
  }

  const magic = token();
  const width = Number(token());
  const height = Number(token());
  const max = Number(token());
  if ((magic !== 'P6' && magic !== 'P3') || !width || !height || max !== 255) {
    throw new Error(`Unsupported PPM header in ${path}`);
  }

  const data = Buffer.alloc(width * height * 3);
  if (magic === 'P6') {
    if (pos < bytes.length && isWs(bytes[pos])) pos += 1;
    bytes.copy(data, 0, pos, pos + data.length);
  } else {
    for (let i = 0; i < data.length; i += 1) {
      data[i] = Number(token());
    }
  }
  return { path, width, height, data };
}

function readMetrics(path) {
  if (!path) return null;
  return JSON.parse(fs.readFileSync(path, 'utf8'));
}

function emptyBox() {
  return { minX: null, minY: null, maxX: null, maxY: null, pixels: 0 };
}

function addBox(box, x, y) {
  box.minX = box.minX === null ? x : Math.min(box.minX, x);
  box.minY = box.minY === null ? y : Math.min(box.minY, y);
  box.maxX = box.maxX === null ? x : Math.max(box.maxX, x);
  box.maxY = box.maxY === null ? y : Math.max(box.maxY, y);
  box.pixels += 1;
}

function classifyBoxes(img) {
  const boxes = {
    nonWhite: emptyBox(),
    dark: emptyBox(),
    blue: emptyBox(),
    gray: emptyBox(),
    chromatic: emptyBox(),
  };
  for (let y = 0; y < img.height; y += 1) {
    for (let x = 0; x < img.width; x += 1) {
      const p = (y * img.width + x) * 3;
      const r = img.data[p];
      const g = img.data[p + 1];
      const b = img.data[p + 2];
      const spread = Math.max(r, g, b) - Math.min(r, g, b);
      if (r !== 255 || g !== 255 || b !== 255) addBox(boxes.nonWhite, x, y);
      if (r < 100 && g < 100 && b < 100) addBox(boxes.dark, x, y);
      if (b > 150 && r < 100 && g < 150) addBox(boxes.blue, x, y);
      if ((r !== 255 || g !== 255 || b !== 255) && spread <= 2) addBox(boxes.gray, x, y);
      if ((r !== 255 || g !== 255 || b !== 255) && spread > 16) addBox(boxes.chromatic, x, y);
    }
  }
  return boxes;
}

function emptyChannelTotals() {
  return {
    absolute: { r: 0, g: 0, b: 0 },
    signed: { r: 0, g: 0, b: 0 },
  };
}

function nonWhiteBox(img, region) {
  const box = emptyBox();
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * img.width + x) * 3;
      if (img.data[p] !== 255 || img.data[p + 1] !== 255 || img.data[p + 2] !== 255) {
        addBox(box, x, y);
      }
    }
  }
  return box;
}

function dominantColor(img, region) {
  const counts = new Map();
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  let bestKey = '255,255,255';
  let bestCount = -1;
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * img.width + x) * 3;
      const key = `${img.data[p]},${img.data[p + 1]},${img.data[p + 2]}`;
      const next = (counts.get(key) || 0) + 1;
      counts.set(key, next);
      if (next > bestCount) {
        bestCount = next;
        bestKey = key;
      }
    }
  }
  const parts = bestKey.split(',').map(Number);
  return { r: parts[0], g: parts[1], b: parts[2], pixels: Math.max(0, bestCount) };
}

function dominantInkBox(img, region) {
  const bg = dominantColor(img, region);
  const box = emptyBox();
  const endY = Math.min(img.height, region.y + region.height);
  const endX = Math.min(img.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * img.width + x) * 3;
      if (img.data[p] !== bg.r || img.data[p + 1] !== bg.g || img.data[p + 2] !== bg.b) {
        addBox(box, x, y);
      }
    }
  }
  return { box, dominantColor: bg };
}

function summarizeRegion(expected, actual, region) {
  const expectedNonWhiteBox = nonWhiteBox(expected, region);
  const actualNonWhiteBox = nonWhiteBox(actual, region);
  const expectedInk = dominantInkBox(expected, region);
  const actualInk = dominantInkBox(actual, region);
  const out = {
    x: region.x,
    y: region.y,
    width: region.width,
    height: region.height,
    differentPixels: 0,
    sumAbsoluteChannelDiff: 0,
    channelDiff: emptyChannelTotals(),
    expectedNonWhiteBox,
    actualNonWhiteBox,
    expectedDominantColor: expectedInk.dominantColor,
    actualDominantColor: actualInk.dominantColor,
    expectedInkBox: expectedInk.box,
    actualInkBox: actualInk.box,
    nonWhiteCoverage: {
      expectedPixels: expectedNonWhiteBox.pixels,
      actualPixels: actualNonWhiteBox.pixels,
      missingPixels: Math.max(0, expectedNonWhiteBox.pixels - actualNonWhiteBox.pixels),
      actualPct10000: expectedNonWhiteBox.pixels > 0
        ? Math.floor((actualNonWhiteBox.pixels * 10000) / expectedNonWhiteBox.pixels)
        : 10000,
    },
    inkCoverage: {
      expectedPixels: expectedInk.box.pixels,
      actualPixels: actualInk.box.pixels,
      missingPixels: Math.max(0, expectedInk.box.pixels - actualInk.box.pixels),
      actualPct10000: expectedInk.box.pixels > 0
        ? Math.floor((actualInk.box.pixels * 10000) / expectedInk.box.pixels)
        : 10000,
    },
  };

  const endY = Math.min(expected.height, region.y + region.height);
  const endX = Math.min(expected.width, region.x + region.width);
  for (let y = Math.max(0, region.y); y < endY; y += 1) {
    for (let x = Math.max(0, region.x); x < endX; x += 1) {
      const p = (y * expected.width + x) * 3;
      const sr = actual.data[p] - expected.data[p];
      const sg = actual.data[p + 1] - expected.data[p + 1];
      const sb = actual.data[p + 2] - expected.data[p + 2];
      const dr = Math.abs(sr);
      const dg = Math.abs(sg);
      const db = Math.abs(sb);
      const pixelDiff = dr + dg + db;
      if (pixelDiff > 0) {
        out.differentPixels += 1;
        out.sumAbsoluteChannelDiff += pixelDiff;
        out.channelDiff.absolute.r += dr;
        out.channelDiff.absolute.g += dg;
        out.channelDiff.absolute.b += db;
        out.channelDiff.signed.r += sr;
        out.channelDiff.signed.g += sg;
        out.channelDiff.signed.b += sb;
      }
    }
  }
  return out;
}

function regionFromDomRect(rect, name) {
  return {
    name,
    x: Math.floor(rect.x),
    y: Math.floor(rect.y),
    width: Math.ceil(rect.width),
    height: Math.ceil(rect.height),
  };
}

function famousSiteRegionSpec(img, metricsDoc) {
  const metrics = metricsDoc && metricsDoc.metrics ? metricsDoc.metrics : null;
  if (!metrics || !metrics.div || !metrics.div.rect || !Array.isArray(metrics.textClientRects)) {
    return {
      divBox: { x: 8, y: 8, width: 120, height: 40 },
      overflowText: { x: 0, y: 48, width: img.width, height: 32 },
      belowOverflow: { x: 0, y: 80, width: img.width, height: img.height - 80 },
      lineRects: [
        { name: 'line1', x: 8, y: 8, width: 92, height: 17 },
        { name: 'line2', x: 8, y: 26, width: 84, height: 17 },
        { name: 'line3', x: 8, y: 44, width: 86, height: 17 },
        { name: 'line4', x: 8, y: 62, width: 43, height: 17 },
      ],
    };
  }

  const divBox = regionFromDomRect(metrics.div.rect);
  let maxBottom = divBox.y + divBox.height;
  const lineRects = [];
  metrics.textClientRects.forEach((rect, index) => {
    lineRects.push(regionFromDomRect(rect, `line${index + 1}`));
    maxBottom = Math.max(maxBottom, Math.ceil(rect.bottom) + 1);
  });
  const overflowY = divBox.y + divBox.height;
  return {
    divBox,
    overflowText: { x: 0, y: overflowY, width: img.width, height: Math.max(0, maxBottom - overflowY) },
    belowOverflow: { x: 0, y: maxBottom, width: img.width, height: Math.max(0, img.height - maxBottom) },
    lineRects,
  };
}

function famousSiteRegions(expected, actual, metricsDoc) {
  const spec = famousSiteRegionSpec(expected, metricsDoc);
  const textLines = {};
  const textLineSegments = {};
  for (const line of spec.lineRects) {
    textLines[line.name] = summarizeRegion(expected, actual, line);
    const lineBottom = line.y + line.height;
    const divBottom = spec.divBox.y + spec.divBox.height;
    const inDivHeight = Math.max(0, Math.min(lineBottom, divBottom) - line.y);
    const overflowHeight = Math.max(0, lineBottom - Math.max(line.y, divBottom));
    textLineSegments[line.name] = {
      inDiv: summarizeRegion(expected, actual, {
        x: line.x,
        y: line.y,
        width: line.width,
        height: inDivHeight,
      }),
      overflow: summarizeRegion(expected, actual, {
        x: line.x,
        y: Math.max(line.y, divBottom),
        width: line.width,
        height: overflowHeight,
      }),
    };
  }
  return {
    divBox: summarizeRegion(expected, actual, spec.divBox),
    overflowText: summarizeRegion(expected, actual, spec.overflowText),
    belowOverflow: summarizeRegion(expected, actual, spec.belowOverflow),
    textLines,
    textLineSegments,
  };
}

function compare(expected, actual, metricsDoc) {
  if (expected.width !== actual.width || expected.height !== actual.height) {
    throw new Error(`Dimension mismatch: ${expected.width}x${expected.height} vs ${actual.width}x${actual.height}`);
  }
  const diffBox = emptyBox();
  const rows = Array(expected.height).fill(0);
  const cols = Array(expected.width).fill(0);
  let sad = 0;
  const channelAbsoluteDiff = { r: 0, g: 0, b: 0 };
  const channelSignedDiff = { r: 0, g: 0, b: 0 };
  let maxChannelDiff = 0;

  for (let y = 0; y < expected.height; y += 1) {
    for (let x = 0; x < expected.width; x += 1) {
      const p = (y * expected.width + x) * 3;
      const dr = Math.abs(expected.data[p] - actual.data[p]);
      const dg = Math.abs(expected.data[p + 1] - actual.data[p + 1]);
      const db = Math.abs(expected.data[p + 2] - actual.data[p + 2]);
      const sr = actual.data[p] - expected.data[p];
      const sg = actual.data[p + 1] - expected.data[p + 1];
      const sb = actual.data[p + 2] - expected.data[p + 2];
      const pixelDiff = dr + dg + db;
      if (pixelDiff > 0) {
        addBox(diffBox, x, y);
        rows[y] += 1;
        cols[x] += 1;
        sad += pixelDiff;
        channelAbsoluteDiff.r += dr;
        channelAbsoluteDiff.g += dg;
        channelAbsoluteDiff.b += db;
        channelSignedDiff.r += sr;
        channelSignedDiff.g += sg;
        channelSignedDiff.b += sb;
        maxChannelDiff = Math.max(maxChannelDiff, dr, dg, db);
      }
    }
  }

  const topRows = rows
    .map((count, row) => ({ row, count }))
    .filter((item) => item.count > 0)
    .sort((a, b) => b.count - a.count)
    .slice(0, 10);
  const topCols = cols
    .map((count, col) => ({ col, count }))
    .filter((item) => item.count > 0)
    .sort((a, b) => b.count - a.count)
    .slice(0, 10);

  return {
    width: expected.width,
    height: expected.height,
    differentPixels: diffBox.pixels,
    matchPct10000: Math.floor(((expected.width * expected.height - diffBox.pixels) * 10000) / (expected.width * expected.height)),
    sumAbsoluteChannelDiff: sad,
    channelAbsoluteDiff,
    channelSignedDiff,
    maxChannelDiff,
    diffBox,
    expectedBoxes: classifyBoxes(expected),
    actualBoxes: classifyBoxes(actual),
    famousSiteRegions: famousSiteRegions(expected, actual, metricsDoc),
    topRows,
    topCols,
  };
}

if (process.argv.length !== 4 && process.argv.length !== 5) usage();

const expected = readPpm(process.argv[2]);
const actual = readPpm(process.argv[3]);
const metrics = readMetrics(process.argv[4]);
console.log(JSON.stringify(compare(expected, actual, metrics), null, 2));
