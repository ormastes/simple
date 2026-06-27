#!/usr/bin/env node
const fs = require('fs');
const path = require('path');

function clean(value) {
  if (value === undefined || value === null) return '';
  return String(value).replace(/[\r\n]/g, ' ');
}

function emit(key, value) {
  console.log(`${key}=${clean(value)}`);
}

function decimalIntegerText(value) {
  if (typeof value === 'number' && Number.isInteger(value)) return String(value);
  if (typeof value === 'bigint') return value.toString();
  if (typeof value === 'string' && /^-?[0-9]+$/.test(value.trim())) return value.trim();
  return null;
}

function jsonIntegerText(value) {
  if (typeof value === 'number' && Number.isInteger(value)) return String(value);
  return null;
}

function sameInteger(left, right) {
  const l = decimalIntegerText(left);
  const r = decimalIntegerText(right);
  if (l === null || r === null) return false;
  return BigInt(l) === BigInt(r);
}

function sameJsonInteger(left, right) {
  const l = jsonIntegerText(left);
  const r = jsonIntegerText(right);
  if (l === null || r === null) return false;
  return BigInt(l) === BigInt(r);
}

function integerAtLeast(value, min) {
  const text = decimalIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(min);
}

function jsonIntegerAtLeast(value, min) {
  const text = jsonIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(min);
}

function integerTextOrClean(value) {
  const text = decimalIntegerText(value);
  return text === null ? clean(value) : text;
}

function jsonIntegerTextOrBlank(value) {
  const text = jsonIntegerText(value);
  return text === null ? '' : text;
}

function artifactStat(value, proofPath) {
  if (typeof value !== 'string' || value.trim() === '') {
    return null;
  }
  const raw = value.trim();
  const candidates = path.isAbsolute(raw)
    ? [raw]
    : [raw, path.join(path.dirname(proofPath), raw)];
  for (const candidate of candidates) {
    if (path.resolve(candidate) === path.resolve(proofPath)) {
      continue;
    }
    try {
      const stat = fs.statSync(candidate);
      if (stat.isFile()) {
        return { stat, path: candidate };
      }
    } catch (_err) {
      // Try the next candidate.
    }
  }
  return null;
}

function readJsonArtifact(artifact, fallback) {
  if (!artifact) return { ok: false, value: null };
  try {
    return { ok: true, value: JSON.parse(fs.readFileSync(artifact.path, 'utf8')) };
  } catch (_err) {
    return { ok: false, value: fallback };
  }
}

function pixelCountMatches(pixels, width, height) {
  if (!Array.isArray(pixels)) return false;
  const w = jsonIntegerText(width);
  const h = jsonIntegerText(height);
  if (w === null || h === null) return false;
  return BigInt(pixels.length) === BigInt(w) * BigInt(h);
}

function argbPixelsAreUint32Numbers(pixels) {
  if (!Array.isArray(pixels)) return false;
  return pixels.every((pixel) =>
    typeof pixel === 'number' &&
    Number.isInteger(pixel) &&
    pixel >= 0 &&
    pixel <= 0xffffffff
  );
}

function nonzeroPixelCount(pixels) {
  if (!Array.isArray(pixels)) return '';
  let count = 0;
  for (const pixel of pixels) {
    if (pixel !== 0) count += 1;
  }
  return String(count);
}

const proofPath = process.argv[2];
if (!proofPath) {
  emit('chrome_simple_web_layout_validation_status', 'fail');
  emit('chrome_simple_web_layout_validation_reason', 'usage-proof-json');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('chrome_simple_web_layout_validation_status', 'fail');
  emit('chrome_simple_web_layout_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  process.exit(1);
}

const capturedArgbStat = artifactStat(proof.captured_argb_path, proofPath);
const capturedArgbJson = readJsonArtifact(capturedArgbStat, {});
const capturedArgb = capturedArgbJson.value || {};
const capturedArgbPixels = Array.isArray(capturedArgb.pixels) ? capturedArgb.pixels : null;
const capturedArgbNonzeroPixelCount = nonzeroPixelCount(capturedArgbPixels);
const geometryStat = artifactStat(proof.geometry_path, proofPath);
const geometryJson = readJsonArtifact(geometryStat, {});
const geometry = geometryJson.value || {};
const geometryViewport = geometry.viewport || {};
const geometryItems = Array.isArray(geometry.items) ? geometry.items : [];
const expectedProofSource = 'tools/chrome-live-bitmap/capture_html_argb.js';
const chromeUserAgent = typeof proof.chrome_user_agent === 'string' ? proof.chrome_user_agent : '';

let reason = 'pass';
if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
} else if (proof.proof_source !== expectedProofSource) {
  reason = 'unexpected-chrome-proof-source';
} else if (proof.capture_mode !== 'chrome-devtools-screenshot') {
  reason = 'unexpected-chrome-capture-mode';
} else if (!/(Chrome|Chromium)\/[0-9]/.test(chromeUserAgent)) {
  reason = 'missing-chrome-runtime-user-agent';
} else if (decimalIntegerText(proof.checksum) === null || decimalIntegerText(proof.expected_checksum) === null) {
  reason = 'missing-checksum-proof';
} else if (!sameInteger(proof.checksum, proof.expected_checksum)) {
  reason = 'checksum-mismatch';
} else if (decimalIntegerText(proof.weighted_checksum) === null || decimalIntegerText(proof.expected_weighted_checksum) === null) {
  reason = 'missing-weighted-checksum-proof';
} else if (!sameInteger(proof.weighted_checksum, proof.expected_weighted_checksum)) {
  reason = 'weighted-checksum-mismatch';
} else if (jsonIntegerText(proof.mismatch_count) === null) {
  reason = 'malformed-mismatch-count';
} else if (!sameJsonInteger(proof.mismatch_count, 0)) {
  reason = 'pixel-mismatch';
} else if (!jsonIntegerAtLeast(proof.width, 1) || !jsonIntegerAtLeast(proof.height, 1)) {
  reason = 'missing-capture-viewport';
} else if (proof.captured_argb_written !== true) {
  reason = 'missing-captured-argb';
} else if (capturedArgbStat === null) {
  reason = 'missing-captured-argb-file';
} else if (capturedArgbStat.stat.size <= 0) {
  reason = 'empty-captured-argb-file';
} else if (!capturedArgbJson.ok || !Array.isArray(capturedArgb.pixels)) {
  reason = 'malformed-captured-argb';
} else if (capturedArgb.format !== 'argb-u32') {
  reason = 'captured-argb-format-mismatch';
} else if (capturedArgb.producer !== 'chrome-headless-screenshot') {
  reason = 'captured-argb-producer-mismatch';
} else if (!sameJsonInteger(capturedArgb.width, proof.width) || !sameJsonInteger(capturedArgb.height, proof.height)) {
  reason = 'captured-argb-viewport-mismatch';
} else if (!argbPixelsAreUint32Numbers(capturedArgb.pixels)) {
  reason = 'captured-argb-pixel-type-mismatch';
} else if (!pixelCountMatches(capturedArgb.pixels, proof.width, proof.height)) {
  reason = 'captured-argb-pixel-count-mismatch';
} else if (!integerAtLeast(capturedArgbNonzeroPixelCount, 1)) {
  reason = 'blank-captured-argb';
} else if (proof.geometry_written !== true) {
  reason = 'missing-chrome-geometry';
} else if (geometryStat === null) {
  reason = 'missing-chrome-geometry-file';
} else if (geometryStat.stat.size <= 0) {
  reason = 'empty-chrome-geometry-file';
} else if (!geometryJson.ok || geometry.producer !== 'chrome-headless-geometry') {
  reason = 'malformed-chrome-geometry';
} else if (!sameJsonInteger(geometryViewport.width, proof.width) || !sameJsonInteger(geometryViewport.height, proof.height)) {
  reason = 'chrome-geometry-viewport-mismatch';
} else if (geometryItems.length < 1) {
  reason = 'missing-chrome-geometry-items';
} else if (!jsonIntegerAtLeast(proof.frame_us, 1)) {
  reason = 'missing-chrome-timing';
}

emit('chrome_simple_web_layout_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('chrome_simple_web_layout_validation_reason', reason);
emit('chrome_simple_web_layout_proof_source', proof.proof_source);
emit('chrome_simple_web_layout_capture_mode', proof.capture_mode);
emit('chrome_simple_web_layout_chrome_user_agent', proof.chrome_user_agent);
emit('chrome_simple_web_layout_chrome_product', proof.chrome_product);
emit('chrome_simple_web_layout_chrome_protocol_version', proof.chrome_protocol_version);
emit('chrome_simple_web_layout_simple_checksum', integerTextOrClean(proof.expected_checksum));
emit('chrome_simple_web_layout_chrome_checksum', integerTextOrClean(proof.checksum));
emit('chrome_simple_web_layout_simple_weighted_checksum', integerTextOrClean(proof.expected_weighted_checksum));
emit('chrome_simple_web_layout_chrome_weighted_checksum', integerTextOrClean(proof.weighted_checksum));
emit('chrome_simple_web_layout_mismatch_count', jsonIntegerTextOrBlank(proof.mismatch_count));
emit('chrome_simple_web_layout_blur_or_tolerance_used', proof.blur_or_tolerance_used === false ? 'false' : clean(proof.blur_or_tolerance_used));
emit('chrome_simple_web_layout_chrome_frame_us', jsonIntegerTextOrBlank(proof.frame_us));
emit('chrome_simple_web_layout_capture_width', jsonIntegerTextOrBlank(proof.width));
emit('chrome_simple_web_layout_capture_height', jsonIntegerTextOrBlank(proof.height));
emit('chrome_simple_web_layout_captured_argb_path', proof.captured_argb_path);
emit('chrome_simple_web_layout_captured_argb_written', proof.captured_argb_written === true ? 'true' : 'false');
emit('chrome_simple_web_layout_captured_argb_file_status', capturedArgbStat === null ? 'fail' : 'pass');
emit('chrome_simple_web_layout_captured_argb_size_bytes', capturedArgbStat === null ? '' : String(capturedArgbStat.stat.size));
emit('chrome_simple_web_layout_captured_argb_format', capturedArgb.format);
emit('chrome_simple_web_layout_captured_argb_producer', capturedArgb.producer);
emit('chrome_simple_web_layout_captured_argb_width', jsonIntegerTextOrBlank(capturedArgb.width));
emit('chrome_simple_web_layout_captured_argb_height', jsonIntegerTextOrBlank(capturedArgb.height));
emit('chrome_simple_web_layout_captured_argb_pixel_count', capturedArgbPixels === null ? '' : String(capturedArgbPixels.length));
emit('chrome_simple_web_layout_captured_argb_nonzero_pixel_count', capturedArgbNonzeroPixelCount);
emit('chrome_simple_web_layout_geometry_path', proof.geometry_path);
emit('chrome_simple_web_layout_geometry_written', proof.geometry_written === true ? 'true' : 'false');
emit('chrome_simple_web_layout_geometry_file_status', geometryStat === null ? 'fail' : 'pass');
emit('chrome_simple_web_layout_geometry_size_bytes', geometryStat === null ? '' : String(geometryStat.stat.size));
emit('chrome_simple_web_layout_geometry_producer', geometry.producer);
emit('chrome_simple_web_layout_geometry_viewport_width', jsonIntegerTextOrBlank(geometryViewport.width));
emit('chrome_simple_web_layout_geometry_viewport_height', jsonIntegerTextOrBlank(geometryViewport.height));
emit('chrome_simple_web_layout_geometry_item_count', String(geometryItems.length));
emit('chrome_simple_web_layout_chrome_bin', proof.chrome_bin);

if (reason !== 'pass') {
  process.exit(1);
}
