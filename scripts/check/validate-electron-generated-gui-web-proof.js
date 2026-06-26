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

function jsonIntegerTextOrClean(value) {
  const text = jsonIntegerText(value);
  return text === null ? clean(value) : text;
}

function booleanString(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return clean(value);
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

function readJsonArtifact(artifact) {
  if (!artifact) return { ok: false, value: null };
  try {
    return { ok: true, value: JSON.parse(fs.readFileSync(artifact.path, 'utf8')) };
  } catch (_err) {
    return { ok: false, value: null };
  }
}

function pixelCountMatches(pixels, width, height) {
  const w = jsonIntegerText(width);
  const h = jsonIntegerText(height);
  if (!Array.isArray(pixels) || w === null || h === null) return false;
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
  if (!Array.isArray(pixels)) return 0;
  let count = 0;
  for (const pixel of pixels) {
    if (pixel !== 0) count += 1;
  }
  return count;
}

const proofPath = process.argv[2];
if (!proofPath) {
  emit('electron_generated_gui_web_validation_status', 'fail');
  emit('electron_generated_gui_web_validation_reason', 'usage-proof-json');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('electron_generated_gui_web_validation_status', 'fail');
  emit('electron_generated_gui_web_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  process.exit(1);
}

const capturedArgbStat = artifactStat(proof.captured_argb_path, proofPath);
const capturedArgbJson = readJsonArtifact(capturedArgbStat);
const capturedArgb = capturedArgbJson.value || {};
const capturedArgbPixels = Array.isArray(capturedArgb.pixels) ? capturedArgb.pixels : [];
const capturedArgbNonzeroPixels = nonzeroPixelCount(capturedArgbPixels);

let reason = 'pass';
if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
} else if (proof.renderer !== 'electron-live-capture-page') {
  reason = 'unexpected-electron-renderer';
} else if (proof.scene !== 'generated-gui-widget-html') {
  reason = 'unexpected-electron-scene';
} else if (decimalIntegerText(proof.checksum) === null || decimalIntegerText(proof.expected_checksum) === null) {
  reason = 'missing-checksum-proof';
} else if (!sameInteger(proof.checksum, proof.expected_checksum)) {
  reason = 'checksum-mismatch';
} else if (decimalIntegerText(proof.weighted_checksum) === null || decimalIntegerText(proof.expected_weighted_checksum) === null) {
  reason = 'missing-weighted-checksum-proof';
} else if (!sameInteger(proof.weighted_checksum, proof.expected_weighted_checksum)) {
  reason = 'weighted-checksum-mismatch';
} else if (decimalIntegerText(proof.mismatch_count) === null) {
  reason = 'malformed-mismatch-count';
} else if (!sameInteger(proof.mismatch_count, 0)) {
  reason = 'pixel-mismatch';
} else if (!jsonIntegerAtLeast(proof.width, 1) || !jsonIntegerAtLeast(proof.height, 1)) {
  reason = 'missing-viewport-proof';
} else if (proof.captured_argb_written !== true) {
  reason = 'missing-captured-argb';
} else if (capturedArgbStat === null) {
  reason = 'missing-captured-argb-file';
} else if (capturedArgbStat.stat.size <= 0) {
  reason = 'empty-captured-argb-file';
} else if (!capturedArgbJson.ok || capturedArgb.format !== 'argb-u32' || capturedArgb.producer !== 'electron-live-capture-page') {
  reason = 'malformed-captured-argb';
} else if (!sameJsonInteger(capturedArgb.width, proof.width) || !sameJsonInteger(capturedArgb.height, proof.height)) {
  reason = 'captured-argb-viewport-mismatch';
} else if (!argbPixelsAreUint32Numbers(capturedArgbPixels)) {
  reason = 'captured-argb-pixel-type-mismatch';
} else if (!pixelCountMatches(capturedArgbPixels, proof.width, proof.height)) {
  reason = 'captured-argb-pixel-count-mismatch';
} else if (capturedArgbNonzeroPixels < 1) {
  reason = 'blank-captured-argb';
} else if (!jsonIntegerAtLeast(proof.capture_native_width, 1) || !jsonIntegerAtLeast(proof.capture_native_height, 1) || typeof proof.capture_downsampled !== 'boolean') {
  reason = 'missing-capture-provenance';
} else if (!sameJsonInteger(proof.capture_native_width, proof.width) || !sameJsonInteger(proof.capture_native_height, proof.height)) {
  reason = 'capture-viewport-mismatch';
} else if (!jsonIntegerAtLeast(proof.frame_us, 1)) {
  reason = 'missing-electron-timing';
} else if (!jsonIntegerAtLeast(proof.generated_gui_text_normalization_pixels ?? 0, 0)) {
  reason = 'malformed-text-normalization';
}

emit('electron_generated_gui_web_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('electron_generated_gui_web_validation_reason', reason);
emit('electron_generated_gui_web_renderer', proof.renderer);
emit('electron_generated_gui_web_scene', proof.scene);
emit('electron_generated_gui_web_simple_checksum', integerTextOrClean(proof.expected_checksum));
emit('electron_generated_gui_web_electron_checksum', integerTextOrClean(proof.checksum));
emit('electron_generated_gui_web_simple_weighted_checksum', integerTextOrClean(proof.expected_weighted_checksum));
emit('electron_generated_gui_web_electron_weighted_checksum', integerTextOrClean(proof.weighted_checksum));
emit('electron_generated_gui_web_mismatch_count', integerTextOrClean(proof.mismatch_count));
emit('electron_generated_gui_web_blur_or_tolerance_used', proof.blur_or_tolerance_used === false ? 'false' : clean(proof.blur_or_tolerance_used));
emit('electron_generated_gui_web_electron_frame_us', jsonIntegerTextOrClean(proof.frame_us));
emit('electron_generated_gui_web_requested_width', jsonIntegerTextOrClean(proof.width));
emit('electron_generated_gui_web_requested_height', jsonIntegerTextOrClean(proof.height));
emit('electron_generated_gui_web_capture_native_width', jsonIntegerTextOrClean(proof.capture_native_width));
emit('electron_generated_gui_web_capture_native_height', jsonIntegerTextOrClean(proof.capture_native_height));
emit('electron_generated_gui_web_capture_downsampled', booleanString(proof.capture_downsampled));
emit('electron_generated_gui_web_captured_argb_path', proof.captured_argb_path);
emit('electron_generated_gui_web_captured_argb_written', proof.captured_argb_written === true ? 'true' : 'false');
emit('electron_generated_gui_web_captured_argb_file_status', capturedArgbStat === null ? 'fail' : 'pass');
emit('electron_generated_gui_web_captured_argb_size_bytes', capturedArgbStat === null ? '' : String(capturedArgbStat.stat.size));
emit('electron_generated_gui_web_captured_argb_format', capturedArgb.format);
emit('electron_generated_gui_web_captured_argb_producer', capturedArgb.producer);
emit('electron_generated_gui_web_captured_argb_width', jsonIntegerTextOrClean(capturedArgb.width));
emit('electron_generated_gui_web_captured_argb_height', jsonIntegerTextOrClean(capturedArgb.height));
emit('electron_generated_gui_web_captured_argb_pixel_count', String(capturedArgbPixels.length));
emit('electron_generated_gui_web_captured_argb_nonzero_pixel_count', String(capturedArgbNonzeroPixels));
emit('electron_generated_gui_web_text_normalization_pixels', jsonIntegerTextOrClean(proof.generated_gui_text_normalization_pixels ?? 0));

if (reason !== 'pass') {
  process.exit(1);
}
