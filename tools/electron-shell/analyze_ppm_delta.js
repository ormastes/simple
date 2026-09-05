#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

function usage() {
  console.error("Usage: analyze_ppm_delta.js <expected.ppm> <actual.ppm> [chrome_metrics.json]");
}

function parsePpm(filePath) {
  if (!fs.existsSync(filePath)) throw new Error(`missing PPM: ${filePath}`);
  const bytes = fs.readFileSync(filePath);
  const headerEnd = bytes.indexOf(Buffer.from("\n255\n"));
  if (headerEnd < 0) throw new Error(`invalid PPM header: ${filePath}`);
  const header = bytes.slice(0, headerEnd).toString("ascii").trim().split(/\s+/);
  const format = header[0];
  const width = Number.parseInt(header[1], 10);
  const height = Number.parseInt(header[2], 10);
  const dataStart = headerEnd + 5;
  if (!Number.isFinite(width) || !Number.isFinite(height)) {
    throw new Error(`invalid PPM dimensions: ${filePath}`);
  }
  if (format === "P6") {
    return { width, height, data: bytes.slice(dataStart, dataStart + width * height * 3) };
  }
  if (format === "P3") {
    const values = bytes.slice(dataStart).toString("ascii").trim().split(/\s+/).map((v) => Number.parseInt(v, 10));
    return { width, height, data: Uint8Array.from(values.slice(0, width * height * 3)) };
  }
  throw new Error(`unsupported PPM format ${format}: ${filePath}`);
}

function pixelAt(image, x, y) {
  const offset = (y * image.width + x) * 3;
  return [image.data[offset], image.data[offset + 1], image.data[offset + 2]];
}

function clampRegion(region, width, height) {
  return {
    left: Math.max(0, Math.min(width, region.left)),
    top: Math.max(0, Math.min(height, region.top)),
    right: Math.max(0, Math.min(width, region.right)),
    bottom: Math.max(0, Math.min(height, region.bottom))
  };
}

function emptyStats(region = null) {
  return {
    region,
    differentPixels: 0,
    sumAbsoluteChannelDiff: 0,
    channelAbsoluteDiff: { r: 0, g: 0, b: 0 },
    channelSignedDiff: { r: 0, g: 0, b: 0 },
    diffBox: { minX: null, minY: null, maxX: null, maxY: null }
  };
}

function analyzeRegion(expected, actual, region) {
  const r = clampRegion(region, expected.width, expected.height);
  const stats = emptyStats(r);
  for (let y = r.top; y < r.bottom; y += 1) {
    for (let x = r.left; x < r.right; x += 1) {
      const e = pixelAt(expected, x, y);
      const a = pixelAt(actual, x, y);
      const dr = Math.abs(e[0] - a[0]);
      const dg = Math.abs(e[1] - a[1]);
      const db = Math.abs(e[2] - a[2]);
      if (dr === 0 && dg === 0 && db === 0) continue;
      stats.differentPixels += 1;
      stats.sumAbsoluteChannelDiff += dr + dg + db;
      stats.channelAbsoluteDiff.r += dr;
      stats.channelAbsoluteDiff.g += dg;
      stats.channelAbsoluteDiff.b += db;
      stats.channelSignedDiff.r += e[0] - a[0];
      stats.channelSignedDiff.g += e[1] - a[1];
      stats.channelSignedDiff.b += e[2] - a[2];
      if (stats.diffBox.minX === null || x < stats.diffBox.minX) stats.diffBox.minX = x;
      if (stats.diffBox.minY === null || y < stats.diffBox.minY) stats.diffBox.minY = y;
      if (stats.diffBox.maxX === null || x > stats.diffBox.maxX) stats.diffBox.maxX = x;
      if (stats.diffBox.maxY === null || y > stats.diffBox.maxY) stats.diffBox.maxY = y;
    }
  }
  return stats;
}

function readMetrics(metricsPath) {
  if (!metricsPath || !fs.existsSync(metricsPath)) return null;
  const parsed = JSON.parse(fs.readFileSync(metricsPath, "utf8"));
  return parsed.metrics || parsed;
}

function rectRegion(rect) {
  return {
    left: Math.floor(rect.left ?? rect.x),
    top: Math.floor(rect.top ?? rect.y),
    right: Math.ceil(rect.right ?? ((rect.x ?? 0) + (rect.width ?? 0))),
    bottom: Math.ceil(rect.bottom ?? ((rect.y ?? 0) + (rect.height ?? 0)))
  };
}

function unionRegions(regions) {
  const valid = regions.filter((r) => r && r.right > r.left && r.bottom > r.top);
  if (valid.length === 0) return null;
  return {
    left: Math.min(...valid.map((r) => r.left)),
    top: Math.min(...valid.map((r) => r.top)),
    right: Math.max(...valid.map((r) => r.right)),
    bottom: Math.max(...valid.map((r) => r.bottom))
  };
}

function metricRegions(metrics, width, height) {
  if (!metrics || !metrics.div || !metrics.div.rect) return null;
  const divBox = rectRegion(metrics.div.rect);
  const textRects = metrics.textClientRects || [];
  const overflowRects = [];
  const textLines = {};
  const textLineSegments = {};
  textRects.forEach((rect, index) => {
    const region = rectRegion(rect);
    textLines[`line${index + 1}`] = region;
    const inDiv = {
      left: region.left,
      top: region.top,
      right: region.right,
      bottom: Math.min(region.bottom, divBox.bottom)
    };
    const overflow = {
      left: region.left,
      top: Math.max(region.top, divBox.bottom),
      right: region.right,
      bottom: region.bottom
    };
    if (inDiv.bottom > inDiv.top) textLineSegments[`line${index + 1}InDiv`] = inDiv;
    if (overflow.bottom > overflow.top) {
      textLineSegments[`line${index + 1}Overflow`] = overflow;
      overflowRects.push(overflow);
    }
  });
  return {
    divBox,
    overflowText: unionRegions(overflowRects),
    belowOverflow: { left: 0, top: Math.max(...[0, ...overflowRects.map((r) => r.bottom)]), right: width, bottom: height },
    textLines,
    textLineSegments
  };
}

function compactStats(stats) {
  return {
    region: stats.region,
    differentPixels: stats.differentPixels,
    sumAbsoluteChannelDiff: stats.sumAbsoluteChannelDiff,
    channelAbsoluteDiff: stats.channelAbsoluteDiff,
    channelSignedDiff: stats.channelSignedDiff,
    diffBox: stats.diffBox
  };
}

function main() {
  const args = process.argv.slice(2).filter((arg) => !arg.startsWith("--"));
  if (args.length < 2) {
    usage();
    process.exit(2);
  }
  const expectedPath = args[0];
  const actualPath = args[1];
  const metricsPath = args[2] || "";
  const expected = parsePpm(expectedPath);
  const actual = parsePpm(actualPath);
  if (expected.width !== actual.width || expected.height !== actual.height) {
    throw new Error(`PPM dimensions differ: ${expected.width}x${expected.height} vs ${actual.width}x${actual.height}`);
  }
  const global = analyzeRegion(expected, actual, { left: 0, top: 0, right: expected.width, bottom: expected.height });
  const metrics = readMetrics(metricsPath);
  const regions = metricRegions(metrics, expected.width, expected.height);
  const result = {
    expected: path.normalize(expectedPath),
    actual: path.normalize(actualPath),
    metrics: metricsPath ? path.normalize(metricsPath) : "",
    width: expected.width,
    height: expected.height,
    differentPixels: global.differentPixels,
    sumAbsoluteChannelDiff: global.sumAbsoluteChannelDiff,
    diffBox: global.diffBox,
    channelAbsoluteDiff: global.channelAbsoluteDiff,
    channelSignedDiff: global.channelSignedDiff,
    famousSiteRegions: {},
    textLines: {},
    textLineSegments: {}
  };
  if (regions) {
    result.famousSiteRegions.divBox = compactStats(analyzeRegion(expected, actual, regions.divBox));
    result.famousSiteRegions.overflowText = regions.overflowText
      ? compactStats(analyzeRegion(expected, actual, regions.overflowText))
      : compactStats(emptyStats(null));
    result.famousSiteRegions.belowOverflow = compactStats(analyzeRegion(expected, actual, regions.belowOverflow));
    for (const [name, region] of Object.entries(regions.textLines)) {
      result.textLines[name] = compactStats(analyzeRegion(expected, actual, region));
    }
    for (const [name, region] of Object.entries(regions.textLineSegments)) {
      result.textLineSegments[name] = compactStats(analyzeRegion(expected, actual, region));
    }
  }
  console.log(JSON.stringify(result, null, 2));
}

try {
  main();
} catch (error) {
  console.error(error.message);
  process.exit(1);
}
