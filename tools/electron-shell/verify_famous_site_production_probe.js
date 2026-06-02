#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const root = process.cwd();
const sampleArg = process.argv.find((arg) => arg.startsWith("--sample="));
const sample = sampleArg ? sampleArg.slice("--sample=".length) : "site_0_google";
const dropAcceptancePolicyFlagsForTest = process.argv.includes("--drop-acceptance-policy-flags-for-test");
const corruptTextLineInkForTest = process.argv.includes("--corrupt-text-line-ink-for-test");
const corruptTextLineInkPositionForTest = process.argv.includes("--corrupt-text-line-ink-position-for-test");
const dropTextLineInkDifferenceForTest = process.argv.includes("--drop-text-line-ink-difference-for-test");
const hideResidualDifferenceForTest = process.argv.includes("--hide-residual-difference-for-test");
const dir = path.join(root, "test", "baselines", "famous_site_corpus", sample);
const reportPath = path.join(dir, "report.production.sdn");
const baselinePath = path.join(dir, "production_probe_baseline.json");

function readProductionProbeBaseline() {
  if (!fs.existsSync(baselinePath)) return null;
  try {
    const baseline = JSON.parse(fs.readFileSync(baselinePath, "utf8"));
    if (baseline.sample !== sample) return null;
    if (!Number.isInteger(baseline.maxDifferentPixels) || baseline.maxDifferentPixels <= 0) return null;
    return baseline;
  } catch (_err) {
    return null;
  }
}

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

function parseSimpleLayoutLineWidths(text) {
  const lines = [];
  const regex = /\(line text:\s*"([^"]+)"\s+width:\s*([0-9]+)\)/g;
  let match;
  while ((match = regex.exec(text)) !== null) {
    lines.push({ text: match[1], width: Number.parseInt(match[2], 10) });
  }
  return lines;
}

function parseTextLineInkEntries(text) {
  const lines = [];
  const regex = /\(line index:\s*([0-9]+)\s+text:\s*"([^"]+)"\s+x:\s*(-?[0-9]+)\s+y:\s*(-?[0-9]+)\s+width:\s*([0-9]+)\s+region:\s*\(region name:\s*"([^"]+)"\s+different_pixels:\s*([0-9]+)\s+chrome_exact_black_pixels:\s*([0-9]+)\s+simple_background_mismatch_pixels:\s*([0-9]+)\)\)/g;
  let match;
  while ((match = regex.exec(text)) !== null) {
    lines.push({
      index: Number.parseInt(match[1], 10),
      text: match[2],
      x: Number.parseInt(match[3], 10),
      y: Number.parseInt(match[4], 10),
      width: Number.parseInt(match[5], 10),
      regionName: match[6],
      differentPixels: Number.parseInt(match[7], 10),
      chromeExactBlackPixels: Number.parseInt(match[8], 10),
      simpleBackgroundMismatchPixels: Number.parseInt(match[9], 10)
    });
  }
  return lines;
}

function compareTextLineInk(layoutLines, inkLines) {
  const differentPixelsTotal = inkLines.reduce((sum, line) => sum + line.differentPixels, 0);
  const detail = {
    detailCount: inkLines.length,
    differentPixelsTotal,
    textMatchesLayout: layoutLines.length > 0 && layoutLines.length === inkLines.length,
    widthMatchesLayout: layoutLines.length > 0 && layoutLines.length === inkLines.length,
    regionNamesSequential: inkLines.length > 0,
    allLinesHaveDifferences: inkLines.length > 0,
    allLinesHaveChromeBlackPixels: inkLines.length > 0
  };
  for (let i = 0; i < inkLines.length; i += 1) {
    const ink = inkLines[i];
    const layout = layoutLines[i];
    if (!layout || ink.index !== i || ink.text !== layout.text) detail.textMatchesLayout = false;
    if (!layout || ink.width !== layout.width) detail.widthMatchesLayout = false;
    if (ink.regionName !== `line_${i}`) detail.regionNamesSequential = false;
    if (ink.differentPixels <= 0) detail.allLinesHaveDifferences = false;
    if (ink.chromeExactBlackPixels <= 0) detail.allLinesHaveChromeBlackPixels = false;
  }
  return detail;
}

function pixelInLineInkRegion(x, y, inkLines) {
  for (const line of inkLines) {
    if (x >= line.x && x < line.x + line.width && y >= line.y && y < line.y + 18) return true;
  }
  return false;
}

function lineInkRegionPixelCounts(chromePath, simplePath, inkLines) {
  const chrome = parsePpm(chromePath);
  const simple = parsePpm(simplePath);
  const detail = {
    allRegionCountsMatch: inkLines.length > 0,
    counts: []
  };
  if (!chrome || !simple || chrome.width !== simple.width || chrome.height !== simple.height) {
    detail.allRegionCountsMatch = false;
    return detail;
  }
  for (const line of inkLines) {
    let actualDifferentPixels = 0;
    const right = Math.min(chrome.width, line.x + line.width);
    const bottom = Math.min(chrome.height, line.y + 18);
    for (let y = Math.max(0, line.y); y < bottom; y += 1) {
      for (let x = Math.max(0, line.x); x < right; x += 1) {
        const c = pixelAt(chrome, x, y);
        const s = pixelAt(simple, x, y);
        if (c[0] !== s[0] || c[1] !== s[1] || c[2] !== s[2]) actualDifferentPixels += 1;
      }
    }
    const matchesReported = actualDifferentPixels === line.differentPixels;
    if (!matchesReported) detail.allRegionCountsMatch = false;
    detail.counts.push({
      index: line.index,
      reportedDifferentPixels: line.differentPixels,
      actualDifferentPixels,
      matchesReported
    });
  }
  return detail;
}

function residualDifferenceDetails(chromePath, simplePath, inkLines) {
  const chrome = parsePpm(chromePath);
  const simple = parsePpm(simplePath);
  const detail = {
    count: 0,
    first: null
  };
  if (!chrome || !simple || chrome.width !== simple.width || chrome.height !== simple.height) return detail;
  for (let y = 0; y < chrome.height; y += 1) {
    for (let x = 0; x < chrome.width; x += 1) {
      if (pixelInLineInkRegion(x, y, inkLines)) continue;
      const c = pixelAt(chrome, x, y);
      const s = pixelAt(simple, x, y);
      if (c[0] === s[0] && c[1] === s[1] && c[2] === s[2]) continue;
      detail.count += 1;
      if (!detail.first) {
        detail.first = {
          x,
          y,
          chrome: { r: c[0], g: c[1], b: c[2] },
          simple: { r: s[0], g: s[1], b: s[2] },
          delta: { r: c[0] - s[0], g: c[1] - s[1], b: c[2] - s[2] }
        };
      }
    }
  }
  return detail;
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
  baseline: path.relative(root, baselinePath),
  rendererMode: "",
  exact: false,
  accepted: false,
  divergent: false,
  parityStatus: "unknown",
  boundedDivergenceOnly: false,
  chromeGlyphCompositingParity: false,
  promotionRequiredDifferentPixels: 0,
  differentPixels: 0,
  maxDifferentPixels: 0,
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
  textLineInkDetails: {
    detailCount: 0,
    differentPixelsTotal: 0,
    unexplainedDifferentPixels: 0,
    textMatchesLayout: false,
    widthMatchesLayout: false,
    regionNamesSequential: false,
    allLinesHaveDifferences: false,
    allLinesHaveChromeBlackPixels: false,
    allRegionCountsMatch: false,
    regionPixelCounts: []
  },
  residualDifference: {
    count: 0,
    first: null
  },
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
  const baseline = readProductionProbeBaseline();
  if (!baseline) failures.push("missing or invalid production probe baseline");
  let text = fs.readFileSync(reportPath, "utf8");
  if (dropAcceptancePolicyFlagsForTest) {
    text = text.replace(" acceptance_policy_flags: (exact_required: true perceptual_diagnostic_only: true tolerance_acceptance_allowed: false)", "");
  }
  if (corruptTextLineInkForTest) {
    const marker = text.indexOf("text_line_ink_delta:");
    if (marker >= 0) {
      text = text.slice(0, marker) + text.slice(marker).replace('(line index: 0 text: "Google search"', '(line index: 0 text: "mutated line"');
    }
  }
  if (dropTextLineInkDifferenceForTest) {
    const marker = text.indexOf("text_line_ink_delta:");
    if (marker >= 0) {
      text = text.slice(0, marker) + text.slice(marker).replace("different_pixels: 808", "different_pixels: 0");
    }
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
  result.maxDifferentPixels = baseline ? baseline.maxDifferentPixels : 0;
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
  const textLineInkEntries = parseTextLineInkEntries(text);
  if (corruptTextLineInkPositionForTest && textLineInkEntries.length > 0) {
    textLineInkEntries[0].x += 8;
  }
  result.textLineInkDetails = compareTextLineInk(parseSimpleLayoutLineWidths(text), textLineInkEntries);
  const regionPixelCounts = lineInkRegionPixelCounts(chromePath, simplePath, textLineInkEntries);
  result.textLineInkDetails.allRegionCountsMatch = regionPixelCounts.allRegionCountsMatch;
  result.textLineInkDetails.regionPixelCounts = regionPixelCounts.counts;
  result.textLineInkDetails.unexplainedDifferentPixels = result.differentPixels - result.textLineInkDetails.differentPixelsTotal;
  result.residualDifference = hideResidualDifferenceForTest ? { count: 0, first: null } : residualDifferenceDetails(chromePath, simplePath, textLineInkEntries);
  result.textInkDelta.divBoxDifferentPixels = parseIntField(text, /div_box:\s*\(region[^\)]*different_pixels:\s*([0-9]+)/);
  result.textInkDelta.divBoxChromeExactBlackPixels = parseIntField(text, /div_box:\s*\(region[^\)]*chrome_exact_black_pixels:\s*([0-9]+)/);
  result.textInkDelta.divBoxSimpleBackgroundMismatchPixels = parseIntField(text, /div_box:\s*\(region[^\)]*simple_background_mismatch_pixels:\s*([0-9]+)/);
  result.textInkDelta.overflowDifferentPixels = parseIntField(text, /overflow_text:\s*\(region[^\)]*different_pixels:\s*([0-9]+)/);
  result.textInkDelta.overflowChromeExactBlackPixels = parseIntField(text, /overflow_text:\s*\(region[^\)]*chrome_exact_black_pixels:\s*([0-9]+)/);
  result.textInkDelta.overflowSimpleBackgroundMismatchPixels = parseIntField(text, /overflow_text:\s*\(region[^\)]*simple_background_mismatch_pixels:\s*([0-9]+)/);
  result.parityStatus = result.exact && result.accepted && result.differentPixels === 0 ? "exact" : "divergent";
  result.boundedDivergenceOnly = result.parityStatus === "divergent" && result.differentPixels > 0 && result.differentPixels <= result.maxDifferentPixels;
  result.chromeGlyphCompositingParity = result.parityStatus === "exact";
  result.promotionRequiredDifferentPixels = result.parityStatus === "exact" ? 0 : result.differentPixels;
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
  if (result.differentPixels > result.maxDifferentPixels) failures.push("production probe regressed above current focused baseline");
  if (!result.textRegionDelta) failures.push("missing production text region delta diagnostics");
  if (result.textRegionDelta && result.textRegionDelta.divBox.differentPixels <= 0) failures.push("production div-box text delta did not report differences");
  if (result.textRegionDelta && (!result.textRegionDelta.overflowText || result.textRegionDelta.overflowText.differentPixels <= 0)) failures.push("production overflow text delta did not report differences");
  if (!result.hasTextInkDelta) failures.push("missing production text ink delta diagnostics");
  if (!result.hasTextLineInkDelta) failures.push("missing production per-line text ink delta diagnostics");
  if (result.hasTextLineInkDelta && result.textLineInkDeltaCount !== result.simpleLayoutLineCount) failures.push("per-line text ink delta count does not match Simple layout line count");
  if (result.hasTextLineInkDelta && result.textLineInkDetails.detailCount !== result.textLineInkDeltaCount) failures.push("per-line text ink detail count does not match declared count");
  if (result.hasTextLineInkDelta && !result.textLineInkDetails.textMatchesLayout) failures.push("per-line text ink entries do not match Simple layout line text");
  if (result.hasTextLineInkDelta && !result.textLineInkDetails.widthMatchesLayout) failures.push("per-line text ink entries do not match Simple layout line widths");
  if (result.hasTextLineInkDelta && !result.textLineInkDetails.regionNamesSequential) failures.push("per-line text ink regions are not sequential");
  if (result.hasTextLineInkDelta && !result.textLineInkDetails.allLinesHaveDifferences) failures.push("per-line text ink entries did not report differences for every line");
  if (result.hasTextLineInkDelta && !result.textLineInkDetails.allLinesHaveChromeBlackPixels) failures.push("per-line text ink entries did not report Chrome glyph pixels for every line");
  if (result.hasTextLineInkDelta && !result.textLineInkDetails.allRegionCountsMatch) failures.push("per-line text ink region geometry does not match production pixels");
  if (result.hasTextLineInkDelta && result.textLineInkDetails.unexplainedDifferentPixels < 0) failures.push("per-line text ink differences exceed production divergence");
  if (result.hasTextLineInkDelta && result.textLineInkDetails.unexplainedDifferentPixels > 1) failures.push("per-line text ink diagnostics do not account for production divergence");
  if (result.hasTextLineInkDelta && result.residualDifference.count !== result.textLineInkDetails.unexplainedDifferentPixels) failures.push("residual pixel diagnostics do not match unexplained production divergence");
  if (result.hasTextLineInkDelta && result.textLineInkDetails.unexplainedDifferentPixels > 0 && !result.residualDifference.first) failures.push("residual pixel diagnostics did not report the first residual pixel");
  if (result.hasTextInkDelta && result.textInkDelta.divBoxChromeExactBlackPixels <= 0) failures.push("text ink delta did not report div-box exact black glyph pixels");
  if (result.hasTextInkDelta && result.textInkDelta.overflowChromeExactBlackPixels <= 0) failures.push("text ink delta did not report overflow exact black glyph pixels");
  if (result.hasTextInkDelta && result.textInkDelta.divBoxSimpleBackgroundMismatchPixels <= 0) failures.push("text ink delta did not report div-box background mismatches");
  if (result.hasTextInkDelta && result.textInkDelta.overflowSimpleBackgroundMismatchPixels <= 0) failures.push("text ink delta did not report overflow background mismatches");
}

result.status = failures.length === 0 ? "PASS" : "FAIL";
console.log(JSON.stringify(result, null, 2));
process.exit(result.status === "PASS" ? 0 : 1);
