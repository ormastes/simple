#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const sampleArg = process.argv.find((arg) => arg.startsWith("--sample="));
const sample = sampleArg ? sampleArg.slice("--sample=".length) : "site_0_google";
const dropAcceptancePolicyFlagsForTest = process.argv.includes("--drop-acceptance-policy-flags-for-test");
const maxDifferentPixels = sample === "site_0_google" ? 2717 : 6000;
const dir = path.join(root, "test", "baselines", "famous_site_corpus", sample);
const reportPath = path.join(dir, "report.production.sdn");

function matchText(text, regex, fallback = "") {
  const match = text.match(regex);
  return match ? match[1] : fallback;
}

function parseBool(text, regex) {
  return matchText(text, regex, "false") === "true";
}

function parseIntField(text, regex) {
  return Number.parseInt(matchText(text, regex, "0"), 10);
}

function parsePpm(filePath) {
  if (!fs.existsSync(filePath)) return null;
  const bytes = fs.readFileSync(filePath);
  const headerEnd = bytes.indexOf(Buffer.from("\n255\n"));
  if (headerEnd < 0) return null;
  const header = bytes.slice(0, headerEnd).toString("ascii").trim().split(/\s+/);
  const width = Number.parseInt(header[1], 10);
  const height = Number.parseInt(header[2], 10);
  const dataStart = headerEnd + 5;
  if (header[0] === "P6") {
    return { width, height, data: bytes.slice(dataStart, dataStart + width * height * 3) };
  }
  if (header[0] === "P3") {
    const values = bytes.slice(dataStart).toString("ascii").trim().split(/\s+/).map((v) => Number.parseInt(v, 10));
    return { width, height, data: Uint8Array.from(values.slice(0, width * height * 3)) };
  }
  return null;
}

function differentPixelsFromPpm(aPath, bPath) {
  const a = parsePpm(aPath);
  const b = parsePpm(bPath);
  if (!a || !b || a.width !== b.width || a.height !== b.height) return null;
  let different = 0;
  for (let i = 0; i + 2 < a.data.length && i + 2 < b.data.length; i += 3) {
    if (a.data[i] !== b.data[i] || a.data[i + 1] !== b.data[i + 1] || a.data[i + 2] !== b.data[i + 2]) {
      different += 1;
    }
  }
  return different;
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

function regionDelta(expected, actual, region) {
  const r = clampRegion(region, expected.width, expected.height);
  let differentPixels = 0;
  let sad = 0;
  const channelAbsoluteDiff = { r: 0, g: 0, b: 0 };
  const channelSignedDiff = { r: 0, g: 0, b: 0 };
  for (let y = r.top; y < r.bottom; y += 1) {
    for (let x = r.left; x < r.right; x += 1) {
      const e = pixelAt(expected, x, y);
      const a = pixelAt(actual, x, y);
      const dr = Math.abs(e[0] - a[0]);
      const dg = Math.abs(e[1] - a[1]);
      const db = Math.abs(e[2] - a[2]);
      if (dr !== 0 || dg !== 0 || db !== 0) differentPixels += 1;
      sad += dr + dg + db;
      channelAbsoluteDiff.r += dr;
      channelAbsoluteDiff.g += dg;
      channelAbsoluteDiff.b += db;
      channelSignedDiff.r += e[0] - a[0];
      channelSignedDiff.g += e[1] - a[1];
      channelSignedDiff.b += e[2] - a[2];
    }
  }
  return {
    region: r,
    differentPixels,
    sad,
    channelAbsoluteDiff,
    channelSignedDiff
  };
}

function textRegionDelta(chromePath, simplePath, metricsPath) {
  if (!fs.existsSync(metricsPath)) return null;
  const chrome = parsePpm(chromePath);
  const simple = parsePpm(simplePath);
  if (!chrome || !simple || chrome.width !== simple.width || chrome.height !== simple.height) return null;
  const metricsRoot = JSON.parse(fs.readFileSync(metricsPath, "utf8"));
  const metrics = metricsRoot.metrics || {};
  const div = metrics.div && metrics.div.rect;
  const rects = metrics.textClientRects || [];
  if (!div || rects.length === 0) return null;
  const divRegion = {
    left: Math.floor(div.left),
    top: Math.floor(div.top),
    right: Math.ceil(div.right),
    bottom: Math.ceil(div.bottom)
  };
  const overflowRegion = { left: chrome.width, top: chrome.height, right: 0, bottom: 0 };
  for (const rect of rects) {
    const top = Math.floor(Math.max(rect.top, div.bottom));
    const bottom = Math.ceil(rect.bottom);
    if (bottom <= top) continue;
    overflowRegion.left = Math.min(overflowRegion.left, Math.floor(rect.left));
    overflowRegion.top = Math.min(overflowRegion.top, top);
    overflowRegion.right = Math.max(overflowRegion.right, Math.ceil(rect.right));
    overflowRegion.bottom = Math.max(overflowRegion.bottom, bottom);
  }
  const hasOverflow = overflowRegion.right > overflowRegion.left && overflowRegion.bottom > overflowRegion.top;
  return {
    metricsPath: path.relative(root, metricsPath),
    divBox: regionDelta(chrome, simple, divRegion),
    overflowText: hasOverflow ? regionDelta(chrome, simple, overflowRegion) : null
  };
}

const failures = [];
let result = {
  status: "FAIL",
  sample,
  report: path.relative(root, reportPath),
  rendererMode: "",
  exact: false,
  accepted: false,
  divergent: false,
  differentPixels: 0,
  maxDifferentPixels,
  computedDifferentPixels: null,
  reportFresh: false,
  hasSimpleLayoutLines: false,
  hasSimpleLayoutLineWidths: false,
  simpleLayoutLineCount: 0,
  hasTextGeometryDelta: false,
  chromeTextLineCount: 0,
  chromeCanvasMetricCount: 0,
  simpleGeometryLineCount: 0,
  textLineCountDelta: 0,
  layoutTextMatch: false,
  hasTextInkDelta: false,
  hasTextLineInkDelta: false,
  textLineInkDeltaCount: 0,
  textInkDelta: {
    divBoxDifferentPixels: 0,
    divBoxChromeExactBlackPixels: 0,
    divBoxSimpleBackgroundMismatchPixels: 0,
    overflowDifferentPixels: 0,
    overflowChromeExactBlackPixels: 0,
    overflowSimpleBackgroundMismatchPixels: 0
  },
  textRegionDelta: null,
  failures
};

if (!fs.existsSync(reportPath)) {
  failures.push("missing production report; run site_corpus_compat.spl with --production-renderer first");
} else {
  let text = fs.readFileSync(reportPath, "utf8");
  if (dropAcceptancePolicyFlagsForTest) {
    text = text.replace(" acceptance_policy_flags: (exact_required: true perceptual_diagnostic_only: true tolerance_acceptance_allowed: false)", "");
  }
  const chromeRel = matchText(text, /chrome_ppm:\s*"([^"]+)"/);
  const simpleRel = matchText(text, /simple_ppm:\s*"([^"]+)"/);
  const chromePath = path.join(root, chromeRel);
  const simplePath = path.join(root, simpleRel);
  result.rendererMode = matchText(text, /renderer_mode:\s*"([^"]+)"/);
  result.exact = parseBool(text, /exact:\s*(true|false)/);
  result.accepted = parseBool(text, /accepted:\s*(true|false)/);
  result.differentPixels = parseIntField(text, /different_pixels:\s*([0-9]+)/);
  result.computedDifferentPixels = differentPixelsFromPpm(chromePath, simplePath);
  result.textRegionDelta = textRegionDelta(chromePath, simplePath, path.join(dir, "chrome_metrics.json"));
  result.divergent = !result.exact && !result.accepted;
  result.reportFresh = result.computedDifferentPixels === result.differentPixels;
  result.hasSimpleLayoutLines = text.includes("simple_layout_lines:");
  result.hasSimpleLayoutLineWidths = text.includes("simple_layout_line_widths:");
  result.simpleLayoutLineCount = parseIntField(text, /simple_layout_lines:\s*\(text_lines count:\s*([0-9]+)/);
  result.hasTextGeometryDelta = text.includes("text_geometry_delta:");
  result.chromeTextLineCount = parseIntField(text, /chrome_text_line_count:\s*([0-9]+)/);
  result.chromeCanvasMetricCount = parseIntField(text, /chrome_canvas_metric_count:\s*([0-9]+)/);
  result.simpleGeometryLineCount = parseIntField(text, /simple_line_count:\s*([0-9]+)/);
  result.textLineCountDelta = Number.parseInt(matchText(text, /text_line_count_delta:\s*(-?[0-9]+)/, "0"), 10);
  result.layoutTextMatch = parseBool(text, /layout_text_match:\s*(true|false)/);
  result.hasTextInkDelta = text.includes("text_ink_delta:");
  result.hasTextLineInkDelta = text.includes("text_line_ink_delta:");
  result.hasExactAcceptancePolicyFlags = text.includes("acceptance_policy_flags: (exact_required: true perceptual_diagnostic_only: true tolerance_acceptance_allowed: false)");
  result.textLineInkDeltaCount = parseIntField(text, /text_line_ink_delta:\s*\(text_line_ink_delta count:\s*([0-9]+)/);
  result.textInkDelta.divBoxDifferentPixels = parseIntField(text, /div_box:\s*\(region[^\)]*different_pixels:\s*([0-9]+)/);
  result.textInkDelta.divBoxChromeExactBlackPixels = parseIntField(text, /div_box:\s*\(region[^\)]*chrome_exact_black_pixels:\s*([0-9]+)/);
  result.textInkDelta.divBoxSimpleBackgroundMismatchPixels = parseIntField(text, /div_box:\s*\(region[^\)]*simple_background_mismatch_pixels:\s*([0-9]+)/);
  result.textInkDelta.overflowDifferentPixels = parseIntField(text, /overflow_text:\s*\(region[^\)]*different_pixels:\s*([0-9]+)/);
  result.textInkDelta.overflowChromeExactBlackPixels = parseIntField(text, /overflow_text:\s*\(region[^\)]*chrome_exact_black_pixels:\s*([0-9]+)/);
  result.textInkDelta.overflowSimpleBackgroundMismatchPixels = parseIntField(text, /overflow_text:\s*\(region[^\)]*simple_background_mismatch_pixels:\s*([0-9]+)/);
  if (result.rendererMode !== "production") failures.push("report is not renderer_mode production");
  if (!simpleRel.endsWith("/simple.production.ppm")) failures.push("simple_ppm does not use production artifact path");
  if (!result.divergent) failures.push("production probe is not divergent");
  if (!result.reportFresh) failures.push("production report is stale or PPM parse failed");
  if (!result.hasSimpleLayoutLines) failures.push("missing Simple layout line diagnostics");
  if (!result.hasSimpleLayoutLineWidths) failures.push("missing Simple layout line width diagnostics");
  if (!result.hasExactAcceptancePolicyFlags) failures.push("missing structured exact-pixel acceptance policy flags");
  if (result.simpleLayoutLineCount <= 0) failures.push("Simple layout diagnostics did not report any text lines");
  if (!result.hasTextGeometryDelta) failures.push("missing Chrome-vs-Simple text geometry delta diagnostics");
  if (result.chromeTextLineCount <= 0) failures.push("text geometry delta did not report Chrome text lines");
  if (result.chromeCanvasMetricCount <= 0) failures.push("text geometry delta did not report Chrome canvas metrics");
  if (result.simpleGeometryLineCount <= 0) failures.push("text geometry delta did not report Simple text lines");
  if (result.differentPixels <= 1000 || result.differentPixels >= 6000) failures.push("production divergence is outside bounded evidence range");
  if (result.differentPixels > maxDifferentPixels) failures.push("production probe regressed above current focused baseline");
  if (!result.textRegionDelta) failures.push("missing production text region delta diagnostics");
  if (result.textRegionDelta && result.textRegionDelta.divBox.differentPixels <= 0) failures.push("production div-box text delta did not report differences");
  if (result.textRegionDelta && (!result.textRegionDelta.overflowText || result.textRegionDelta.overflowText.differentPixels <= 0)) failures.push("production overflow text delta did not report differences");
  if (!result.hasTextInkDelta) failures.push("missing production text ink delta diagnostics");
  if (!result.hasTextLineInkDelta) failures.push("missing production per-line text ink delta diagnostics");
  if (result.hasTextLineInkDelta && result.textLineInkDeltaCount !== result.simpleLayoutLineCount) failures.push("per-line text ink delta count does not match Simple layout line count");
  if (result.hasTextInkDelta && result.textInkDelta.divBoxChromeExactBlackPixels <= 0) failures.push("text ink delta did not report div-box exact black glyph pixels");
  if (result.hasTextInkDelta && result.textInkDelta.overflowChromeExactBlackPixels <= 0) failures.push("text ink delta did not report overflow exact black glyph pixels");
  if (result.hasTextInkDelta && result.textInkDelta.divBoxSimpleBackgroundMismatchPixels <= 0) failures.push("text ink delta did not report div-box background mismatches");
  if (result.hasTextInkDelta && result.textInkDelta.overflowSimpleBackgroundMismatchPixels <= 0) failures.push("text ink delta did not report overflow background mismatches");
}

result.status = failures.length === 0 ? "PASS" : "FAIL";
console.log(JSON.stringify(result, null, 2));
process.exit(result.status === "PASS" ? 0 : 1);
