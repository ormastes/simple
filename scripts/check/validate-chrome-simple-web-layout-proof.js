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
} else if (proof.geometry_written !== true) {
  reason = 'missing-chrome-geometry';
} else if (!integerAtLeast(proof.width, 1) || !integerAtLeast(proof.height, 1)) {
  reason = 'missing-capture-viewport';
} else if (!integerAtLeast(proof.frame_us, 1)) {
  reason = 'missing-chrome-timing';
}

emit('chrome_simple_web_layout_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('chrome_simple_web_layout_validation_reason', reason);
emit('chrome_simple_web_layout_simple_checksum', integerTextOrClean(proof.expected_checksum));
emit('chrome_simple_web_layout_chrome_checksum', integerTextOrClean(proof.checksum));
emit('chrome_simple_web_layout_simple_weighted_checksum', integerTextOrClean(proof.expected_weighted_checksum));
emit('chrome_simple_web_layout_chrome_weighted_checksum', integerTextOrClean(proof.weighted_checksum));
emit('chrome_simple_web_layout_mismatch_count', integerTextOrClean(proof.mismatch_count));
emit('chrome_simple_web_layout_blur_or_tolerance_used', proof.blur_or_tolerance_used === false ? 'false' : clean(proof.blur_or_tolerance_used));
emit('chrome_simple_web_layout_chrome_frame_us', integerTextOrClean(proof.frame_us));
emit('chrome_simple_web_layout_capture_width', integerTextOrClean(proof.width));
emit('chrome_simple_web_layout_capture_height', integerTextOrClean(proof.height));
emit('chrome_simple_web_layout_captured_argb_written', proof.captured_argb_written === true ? 'true' : 'false');
emit('chrome_simple_web_layout_geometry_written', proof.geometry_written === true ? 'true' : 'false');
emit('chrome_simple_web_layout_chrome_bin', proof.chrome_bin);

if (reason !== 'pass') {
  process.exit(1);
}
