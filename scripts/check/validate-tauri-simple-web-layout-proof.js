#!/usr/bin/env node
const fs = require('fs');

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

function sameInteger(left, right) {
  const l = decimalIntegerText(left);
  const r = decimalIntegerText(right);
  if (l === null || r === null) return false;
  return BigInt(l) === BigInt(r);
}

function integerAtLeast(value, min) {
  const text = decimalIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(min);
}

function integerTextOrClean(value) {
  const text = decimalIntegerText(value);
  return text === null ? clean(value) : text;
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

let reason = 'pass';
if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
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
} else if (proof.captured_argb_written !== true) {
  reason = 'missing-captured-argb';
} else if (!integerAtLeast(proof.frame_us, 1)) {
  reason = 'missing-tauri-timing';
} else if (typeof proof.expected_profile !== 'string' || proof.expected_profile === '') {
  reason = 'missing-expected-profile';
} else if (!integerAtLeast(proof.expected_overlay_pixel_count, 0)) {
  reason = 'malformed-expected-overlay-pixel-count';
}

emit('tauri_simple_web_layout_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('tauri_simple_web_layout_validation_reason', reason);
emit('tauri_simple_web_layout_simple_checksum', integerTextOrClean(proof.expected_checksum));
emit('tauri_simple_web_layout_tauri_checksum', integerTextOrClean(proof.checksum));
emit('tauri_simple_web_layout_simple_weighted_checksum', integerTextOrClean(proof.expected_weighted_checksum));
emit('tauri_simple_web_layout_tauri_weighted_checksum', integerTextOrClean(proof.weighted_checksum));
emit('tauri_simple_web_layout_mismatch_count', integerTextOrClean(proof.mismatch_count));
emit('tauri_simple_web_layout_blur_or_tolerance_used', proof.blur_or_tolerance_used === false ? 'false' : clean(proof.blur_or_tolerance_used));
emit('tauri_simple_web_layout_expected_profile', clean(proof.expected_profile));
emit('tauri_simple_web_layout_expected_overlay_pixel_count', integerTextOrClean(proof.expected_overlay_pixel_count));
emit('tauri_simple_web_layout_tauri_frame_us', integerTextOrClean(proof.frame_us));
emit('tauri_simple_web_layout_captured_argb_written', proof.captured_argb_written === true ? 'true' : 'false');

if (reason !== 'pass') {
  process.exit(1);
}
