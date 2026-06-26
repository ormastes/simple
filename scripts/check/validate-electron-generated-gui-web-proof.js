#!/usr/bin/env node
const fs = require('fs');

function clean(value) {
  if (value === undefined || value === null) return '';
  return String(value).replace(/[\r\n]/g, ' ');
}

function emit(key, value) {
  console.log(`${key}=${clean(value)}`);
}

function numberValue(value) {
  if (typeof value === 'number') return Number.isFinite(value) ? value : NaN;
  if (typeof value === 'string' && value.trim() !== '') return Number(value);
  return NaN;
}

function integerAtLeast(value, min) {
  const n = numberValue(value);
  return Number.isInteger(n) && n >= min;
}

function booleanString(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return clean(value);
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

const checksum = numberValue(proof.checksum);
const expectedChecksum = numberValue(proof.expected_checksum);
const weighted = numberValue(proof.weighted_checksum);
const expectedWeighted = numberValue(proof.expected_weighted_checksum);
const mismatchCount = numberValue(proof.mismatch_count);
const frameUs = numberValue(proof.frame_us);
const nativeWidth = numberValue(proof.capture_native_width);
const nativeHeight = numberValue(proof.capture_native_height);
const textNormalizationPixels = numberValue(proof.generated_gui_text_normalization_pixels);

let reason = 'pass';
if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
} else if (!Number.isFinite(checksum) || !Number.isFinite(expectedChecksum)) {
  reason = 'missing-checksum-proof';
} else if (checksum !== expectedChecksum) {
  reason = 'checksum-mismatch';
} else if (!Number.isFinite(weighted) || !Number.isFinite(expectedWeighted)) {
  reason = 'missing-weighted-checksum-proof';
} else if (weighted !== expectedWeighted) {
  reason = 'weighted-checksum-mismatch';
} else if (!Number.isInteger(mismatchCount)) {
  reason = 'malformed-mismatch-count';
} else if (mismatchCount !== 0) {
  reason = 'pixel-mismatch';
} else if (proof.captured_argb_written !== true) {
  reason = 'missing-captured-argb';
} else if (!integerAtLeast(proof.capture_native_width, 1) || !integerAtLeast(proof.capture_native_height, 1) || typeof proof.capture_downsampled !== 'boolean') {
  reason = 'missing-capture-provenance';
} else if (!integerAtLeast(proof.frame_us, 1)) {
  reason = 'missing-electron-timing';
} else if (!integerAtLeast(proof.generated_gui_text_normalization_pixels ?? 0, 0)) {
  reason = 'malformed-text-normalization';
}

emit('electron_generated_gui_web_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('electron_generated_gui_web_validation_reason', reason);
emit('electron_generated_gui_web_simple_checksum', Number.isFinite(expectedChecksum) ? expectedChecksum : '');
emit('electron_generated_gui_web_electron_checksum', Number.isFinite(checksum) ? checksum : '');
emit('electron_generated_gui_web_simple_weighted_checksum', Number.isFinite(expectedWeighted) ? expectedWeighted : '');
emit('electron_generated_gui_web_electron_weighted_checksum', Number.isFinite(weighted) ? weighted : '');
emit('electron_generated_gui_web_mismatch_count', Number.isFinite(mismatchCount) ? mismatchCount : clean(proof.mismatch_count));
emit('electron_generated_gui_web_blur_or_tolerance_used', proof.blur_or_tolerance_used === false ? 'false' : clean(proof.blur_or_tolerance_used));
emit('electron_generated_gui_web_electron_frame_us', Number.isFinite(frameUs) ? frameUs : clean(proof.frame_us));
emit('electron_generated_gui_web_capture_native_width', Number.isFinite(nativeWidth) ? nativeWidth : clean(proof.capture_native_width));
emit('electron_generated_gui_web_capture_native_height', Number.isFinite(nativeHeight) ? nativeHeight : clean(proof.capture_native_height));
emit('electron_generated_gui_web_capture_downsampled', booleanString(proof.capture_downsampled));
emit('electron_generated_gui_web_captured_argb_written', proof.captured_argb_written === true ? 'true' : 'false');
emit('electron_generated_gui_web_text_normalization_pixels', Number.isFinite(textNormalizationPixels) ? textNormalizationPixels : clean(proof.generated_gui_text_normalization_pixels ?? 0));

if (reason !== 'pass') {
  process.exit(1);
}
