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

const proofPath = process.argv[2];
if (!proofPath) {
  emit('electron_simple_web_engine2d_validation_status', 'fail');
  emit('electron_simple_web_engine2d_validation_reason', 'usage-proof-json');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('electron_simple_web_engine2d_validation_status', 'fail');
  emit('electron_simple_web_engine2d_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  process.exit(1);
}

const capturedArgbStat = artifactStat(proof.captured_argb_path, proofPath);

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
} else if (!integerAtLeast(proof.width, 1) || !integerAtLeast(proof.height, 1)) {
  reason = 'missing-viewport-proof';
} else if (proof.captured_argb_written !== true) {
  reason = 'missing-captured-argb';
} else if (capturedArgbStat === null) {
  reason = 'missing-captured-argb-file';
} else if (capturedArgbStat.stat.size <= 0) {
  reason = 'empty-captured-argb-file';
} else if (!integerAtLeast(proof.capture_native_width, 1) || !integerAtLeast(proof.capture_native_height, 1) || typeof proof.capture_downsampled !== 'boolean') {
  reason = 'missing-capture-provenance';
} else if (!sameInteger(proof.capture_native_width, proof.width) || !sameInteger(proof.capture_native_height, proof.height)) {
  reason = 'capture-viewport-mismatch';
} else if (!integerAtLeast(proof.frame_us, 1)) {
  reason = 'missing-electron-timing';
}

emit('electron_simple_web_engine2d_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('electron_simple_web_engine2d_validation_reason', reason);
emit('electron_simple_web_engine2d_simple_checksum', integerTextOrClean(proof.expected_checksum));
emit('electron_simple_web_engine2d_electron_checksum', integerTextOrClean(proof.checksum));
emit('electron_simple_web_engine2d_simple_weighted_checksum', integerTextOrClean(proof.expected_weighted_checksum));
emit('electron_simple_web_engine2d_electron_weighted_checksum', integerTextOrClean(proof.weighted_checksum));
emit('electron_simple_web_engine2d_mismatch_count', integerTextOrClean(proof.mismatch_count));
emit('electron_simple_web_engine2d_blur_or_tolerance_used', proof.blur_or_tolerance_used === false ? 'false' : clean(proof.blur_or_tolerance_used));
emit('electron_simple_web_engine2d_electron_frame_us', integerTextOrClean(proof.frame_us));
emit('electron_simple_web_engine2d_requested_width', integerTextOrClean(proof.width));
emit('electron_simple_web_engine2d_requested_height', integerTextOrClean(proof.height));
emit('electron_simple_web_engine2d_capture_native_width', integerTextOrClean(proof.capture_native_width));
emit('electron_simple_web_engine2d_capture_native_height', integerTextOrClean(proof.capture_native_height));
emit('electron_simple_web_engine2d_capture_downsampled', booleanString(proof.capture_downsampled));
emit('electron_simple_web_engine2d_captured_argb_path', proof.captured_argb_path);
emit('electron_simple_web_engine2d_captured_argb_written', proof.captured_argb_written === true ? 'true' : 'false');
emit('electron_simple_web_engine2d_captured_argb_file_status', capturedArgbStat === null ? 'fail' : 'pass');
emit('electron_simple_web_engine2d_captured_argb_size_bytes', capturedArgbStat === null ? '' : String(capturedArgbStat.stat.size));

if (reason !== 'pass') {
  process.exit(1);
}
