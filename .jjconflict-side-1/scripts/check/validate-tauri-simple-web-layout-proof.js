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

function jsonIntegerBetween(value, min, max) {
  const text = jsonIntegerText(value);
  if (text === null) return false;
  const bigint = BigInt(text);
  return bigint >= BigInt(min) && bigint <= BigInt(max);
}

function integerTextOrClean(value) {
  const text = decimalIntegerText(value);
  return text === null ? clean(value) : text;
}

function jsonIntegerTextOrBlank(value) {
  const text = jsonIntegerText(value);
  return text === null ? '' : text;
}

function jsonBoolTextOrBlank(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return '';
}

function readJsonArtifact(info) {
  if (info === null || info.symlink || info.hardlink) return null;
  try {
    return JSON.parse(fs.readFileSync(info.path, 'utf8'));
  } catch (_err) {
    return null;
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

function checksum(pixels) {
  if (!Array.isArray(pixels)) return '';
  let sum = 0n;
  for (const pixel of pixels) {
    if (
      typeof pixel !== 'number' ||
      !Number.isInteger(pixel) ||
      pixel < 0 ||
      pixel > 0xffffffff
    ) {
      return '';
    }
    sum += BigInt(pixel);
  }
  return sum.toString();
}

function weightedChecksum(pixels) {
  if (!Array.isArray(pixels)) return '';
  let sum = 0n;
  for (let i = 0; i < pixels.length; i += 1) {
    const pixel = pixels[i];
    if (
      typeof pixel !== 'number' ||
      !Number.isInteger(pixel) ||
      pixel < 0 ||
      pixel > 0xffffffff
    ) {
      return '';
    }
    sum += BigInt(pixel) * BigInt(i + 1);
  }
  return sum.toString();
}

function artifactStat(value, proofPath) {
  if (typeof value !== 'string' || value.trim() === '') {
    return null;
  }
  const raw = value.trim();
  const proofDir = path.resolve(path.dirname(proofPath));
  let realProofDir;
  let realProofPath;
  try {
    realProofDir = fs.realpathSync(proofDir);
    realProofPath = fs.realpathSync(proofPath);
  } catch (_err) {
    return null;
  }
  const candidates = path.isAbsolute(raw)
    ? [raw]
    : [raw, path.join(path.dirname(proofPath), raw)];
  for (const candidate of candidates) {
    const resolvedCandidate = path.resolve(candidate);
    if (
      resolvedCandidate === path.resolve(proofPath) ||
      !(resolvedCandidate === proofDir || resolvedCandidate.startsWith(`${proofDir}${path.sep}`))
    ) {
      continue;
    }
    try {
      const linkStat = fs.lstatSync(resolvedCandidate);
      if (linkStat.isSymbolicLink()) {
        return { stat: linkStat, path: resolvedCandidate, symlink: true, hardlink: false };
      }
      const realCandidate = fs.realpathSync(candidate);
      if (
        realCandidate === realProofPath ||
        !(realCandidate === realProofDir || realCandidate.startsWith(`${realProofDir}${path.sep}`))
      ) {
        continue;
      }
      const stat = fs.statSync(realCandidate);
      if (stat.isFile()) {
        return { stat, path: realCandidate, symlink: false, hardlink: stat.nlink > 1 };
      }
    } catch (_err) {
      // Try the next candidate.
    }
  }
  return null;
}

function artifactFileStatus(artifact) {
  if (artifact === null) return 'missing';
  if (artifact.symlink) return 'symlink';
  if (artifact.hardlink) return 'hardlink';
  return artifact.stat.size <= 0 ? 'empty' : 'pass';
}

function artifactSymlinkStatus(artifact) {
  if (artifact === null) return '';
  return artifact.symlink ? 'fail' : 'pass';
}

function artifactHardlinkStatus(artifact) {
  if (artifact === null) return '';
  return artifact.hardlink ? 'fail' : 'pass';
}

function artifactStatusFromFileStatus(status) {
  return status === 'pass' ? 'pass' : 'fail';
}

const proofPath = process.argv[2];
const expectedProducer = process.env.TAURI_SIMPLE_WEB_LAYOUT_EXPECTED_PRODUCER || 'tauri-x11-window-screenshot';
if (!proofPath) {
  emit('tauri_simple_web_layout_validation_status', 'fail');
  emit('tauri_simple_web_layout_validation_reason', 'usage-proof-json');
  process.exit(1);
}

let proofStat;
try {
  proofStat = fs.lstatSync(proofPath);
} catch (_err) {
  proofStat = null;
}

if (proofStat && proofStat.isSymbolicLink()) {
  emit('tauri_simple_web_layout_validation_status', 'fail');
  emit('tauri_simple_web_layout_validation_reason', 'proof-json-symlink');
  emit('tauri_simple_web_layout_proof_symlink_status', 'fail');
  emit('tauri_simple_web_layout_proof_hardlink_status', 'unknown');
  emit('tauri_simple_web_layout_captured_argb_symlink_status', '');
  emit('tauri_simple_web_layout_captured_argb_hardlink_status', '');
  process.exit(1);
}

if (proofStat && proofStat.isFile() && proofStat.nlink > 1) {
  emit('tauri_simple_web_layout_validation_status', 'fail');
  emit('tauri_simple_web_layout_validation_reason', 'proof-json-hardlink');
  emit('tauri_simple_web_layout_proof_symlink_status', 'pass');
  emit('tauri_simple_web_layout_proof_hardlink_status', 'fail');
  emit('tauri_simple_web_layout_captured_argb_symlink_status', '');
  emit('tauri_simple_web_layout_captured_argb_hardlink_status', '');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('tauri_simple_web_layout_validation_status', 'fail');
  emit('tauri_simple_web_layout_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  emit('tauri_simple_web_layout_proof_symlink_status', proofStat ? 'pass' : '');
  emit('tauri_simple_web_layout_proof_hardlink_status', proofStat ? 'pass' : '');
  emit('tauri_simple_web_layout_captured_argb_symlink_status', '');
  emit('tauri_simple_web_layout_captured_argb_hardlink_status', '');
  process.exit(1);
}

const capturedArgbStat = artifactStat(proof.captured_argb_path, proofPath);
const capturedArgb = readJsonArtifact(capturedArgbStat);
const capturedArgbPixels = capturedArgb && Array.isArray(capturedArgb.pixels) ? capturedArgb.pixels : null;
const capturedArgbNonzeroPixelCount = nonzeroPixelCount(capturedArgbPixels);
const capturedArgbChecksum = checksum(capturedArgbPixels);
const capturedArgbWeightedChecksum = weightedChecksum(capturedArgbPixels);
const capturedArgbFileStatus = artifactFileStatus(capturedArgbStat);
const capturedArgbArtifactStatus = artifactStatusFromFileStatus(capturedArgbFileStatus);

let reason = 'pass';
if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
} else if (!jsonIntegerAtLeast(proof.width, 1) || !jsonIntegerAtLeast(proof.height, 1)) {
  reason = 'missing-viewport-proof';
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
} else if (proof.captured_argb_written !== true) {
  reason = 'missing-captured-argb';
} else if (capturedArgbStat === null) {
  reason = 'missing-captured-argb-file';
} else if (capturedArgbStat.symlink) {
  reason = 'captured-argb-symlink';
} else if (capturedArgbStat.hardlink) {
  reason = 'captured-argb-hardlink';
} else if (capturedArgbStat.stat.size <= 0) {
  reason = 'empty-captured-argb-file';
} else if (capturedArgb === null || !Array.isArray(capturedArgb.pixels)) {
  reason = 'malformed-captured-argb';
} else if (capturedArgb.format !== 'argb-u32') {
  reason = 'captured-argb-format-mismatch';
} else if (capturedArgb.producer !== expectedProducer) {
  reason = 'captured-argb-producer-mismatch';
} else if (!sameJsonInteger(capturedArgb.width, proof.width) || !sameJsonInteger(capturedArgb.height, proof.height)) {
  reason = 'captured-argb-viewport-mismatch';
} else if (!argbPixelsAreUint32Numbers(capturedArgb.pixels)) {
  reason = 'captured-argb-pixel-type-mismatch';
} else if (!pixelCountMatches(capturedArgb.pixels, proof.width, proof.height)) {
  reason = 'captured-argb-pixel-count-mismatch';
} else if (!integerAtLeast(capturedArgbNonzeroPixelCount, 1)) {
  reason = 'blank-captured-argb';
} else if (!sameInteger(proof.checksum, capturedArgbChecksum)) {
  reason = 'captured-argb-checksum-mismatch';
} else if (!sameInteger(proof.weighted_checksum, capturedArgbWeightedChecksum)) {
  reason = 'captured-argb-weighted-checksum-mismatch';
} else if (!jsonIntegerBetween(proof.frame_us, 1, 1000000)) {
  reason = 'missing-tauri-timing';
} else if (typeof proof.expected_profile !== 'string' || proof.expected_profile === '') {
  reason = 'missing-expected-profile';
} else if (!jsonIntegerAtLeast(proof.expected_overlay_pixel_count, 0)) {
  reason = 'malformed-expected-overlay-pixel-count';
}

emit('tauri_simple_web_layout_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('tauri_simple_web_layout_validation_reason', reason);
emit('tauri_simple_web_layout_proof_symlink_status', 'pass');
emit('tauri_simple_web_layout_proof_hardlink_status', 'pass');
emit('tauri_simple_web_layout_simple_checksum', integerTextOrClean(proof.expected_checksum));
emit('tauri_simple_web_layout_tauri_checksum', integerTextOrClean(proof.checksum));
emit('tauri_simple_web_layout_simple_weighted_checksum', integerTextOrClean(proof.expected_weighted_checksum));
emit('tauri_simple_web_layout_tauri_weighted_checksum', integerTextOrClean(proof.weighted_checksum));
emit('tauri_simple_web_layout_mismatch_count', jsonIntegerTextOrBlank(proof.mismatch_count));
emit('tauri_simple_web_layout_requested_width', jsonIntegerTextOrBlank(proof.width));
emit('tauri_simple_web_layout_requested_height', jsonIntegerTextOrBlank(proof.height));
emit('tauri_simple_web_layout_blur_or_tolerance_used', jsonBoolTextOrBlank(proof.blur_or_tolerance_used));
emit('tauri_simple_web_layout_expected_profile', clean(proof.expected_profile));
emit('tauri_simple_web_layout_expected_overlay_pixel_count', jsonIntegerTextOrBlank(proof.expected_overlay_pixel_count));
emit('tauri_simple_web_layout_tauri_frame_us', jsonIntegerTextOrBlank(proof.frame_us));
emit('tauri_simple_web_layout_captured_argb_path', proof.captured_argb_path);
emit('tauri_simple_web_layout_captured_argb_written', jsonBoolTextOrBlank(proof.captured_argb_written));
emit('tauri_simple_web_layout_captured_argb_file_status', capturedArgbFileStatus);
emit('tauri_simple_web_layout_captured_argb_file_reason', capturedArgbFileStatus);
emit('tauri_simple_web_layout_captured_argb_artifact_status', capturedArgbArtifactStatus);
emit('tauri_simple_web_layout_captured_argb_symlink_status', artifactSymlinkStatus(capturedArgbStat));
emit('tauri_simple_web_layout_captured_argb_hardlink_status', artifactHardlinkStatus(capturedArgbStat));
emit('tauri_simple_web_layout_captured_argb_size_bytes', capturedArgbStat === null || capturedArgbStat.symlink || capturedArgbStat.hardlink ? '' : String(capturedArgbStat.stat.size));
emit('tauri_simple_web_layout_captured_argb_format', capturedArgb === null ? '' : capturedArgb.format);
emit('tauri_simple_web_layout_captured_argb_producer', capturedArgb === null ? '' : capturedArgb.producer);
emit('tauri_simple_web_layout_captured_argb_width', capturedArgb === null ? '' : jsonIntegerTextOrBlank(capturedArgb.width));
emit('tauri_simple_web_layout_captured_argb_height', capturedArgb === null ? '' : jsonIntegerTextOrBlank(capturedArgb.height));
emit('tauri_simple_web_layout_captured_argb_pixel_count', capturedArgbPixels === null ? '' : String(capturedArgbPixels.length));
emit('tauri_simple_web_layout_captured_argb_nonzero_pixel_count', capturedArgbNonzeroPixelCount);
emit('tauri_simple_web_layout_captured_argb_checksum', capturedArgbChecksum);
emit('tauri_simple_web_layout_captured_argb_weighted_checksum', capturedArgbWeightedChecksum);

if (reason !== 'pass') {
  process.exit(1);
}
