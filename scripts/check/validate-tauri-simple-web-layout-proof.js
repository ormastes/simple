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

const proofPath = process.argv[2];
if (!proofPath) {
  emit('tauri_simple_web_layout_validation_status', 'fail');
  emit('tauri_simple_web_layout_validation_reason', 'usage-proof-json');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('tauri_simple_web_layout_validation_status', 'fail');
  emit('tauri_simple_web_layout_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  process.exit(1);
}

const checksum = numberValue(proof.checksum);
const expectedChecksum = numberValue(proof.expected_checksum);
const weighted = numberValue(proof.weighted_checksum);
const expectedWeighted = numberValue(proof.expected_weighted_checksum);
const mismatchCount = numberValue(proof.mismatch_count);
const frameUs = numberValue(proof.frame_us);
const overlayPixelCount = numberValue(proof.expected_overlay_pixel_count);

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
} else if (!integerAtLeast(proof.frame_us, 1)) {
  reason = 'missing-tauri-timing';
} else if (typeof proof.expected_profile !== 'string' || proof.expected_profile === '') {
  reason = 'missing-expected-profile';
} else if (!Number.isInteger(overlayPixelCount) || overlayPixelCount < 0) {
  reason = 'malformed-expected-overlay-pixel-count';
}

emit('tauri_simple_web_layout_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('tauri_simple_web_layout_validation_reason', reason);
emit('tauri_simple_web_layout_simple_checksum', Number.isFinite(expectedChecksum) ? expectedChecksum : '');
emit('tauri_simple_web_layout_tauri_checksum', Number.isFinite(checksum) ? checksum : '');
emit('tauri_simple_web_layout_simple_weighted_checksum', Number.isFinite(expectedWeighted) ? expectedWeighted : '');
emit('tauri_simple_web_layout_tauri_weighted_checksum', Number.isFinite(weighted) ? weighted : '');
emit('tauri_simple_web_layout_mismatch_count', Number.isFinite(mismatchCount) ? mismatchCount : clean(proof.mismatch_count));
emit('tauri_simple_web_layout_blur_or_tolerance_used', proof.blur_or_tolerance_used === false ? 'false' : clean(proof.blur_or_tolerance_used));
emit('tauri_simple_web_layout_expected_profile', clean(proof.expected_profile));
emit('tauri_simple_web_layout_expected_overlay_pixel_count', Number.isFinite(overlayPixelCount) ? overlayPixelCount : clean(proof.expected_overlay_pixel_count));
emit('tauri_simple_web_layout_tauri_frame_us', Number.isFinite(frameUs) ? frameUs : clean(proof.frame_us));
emit('tauri_simple_web_layout_captured_argb_written', proof.captured_argb_written === true ? 'true' : 'false');

if (reason !== 'pass') {
  process.exit(1);
}
