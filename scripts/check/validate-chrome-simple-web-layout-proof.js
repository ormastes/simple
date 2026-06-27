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

function pathInfo(filePath) {
  let lstat = null;
  let stat = null;
  try {
    lstat = fs.lstatSync(filePath);
  } catch (_err) {
    lstat = null;
  }
  try {
    stat = fs.statSync(filePath);
  } catch (_err) {
    stat = null;
  }
  return {
    lstat,
    stat,
    isSymlink: lstat !== null && lstat.isSymbolicLink(),
  };
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
      const lstat = fs.lstatSync(candidate);
      if (lstat.isSymbolicLink()) {
        return { stat: null, path: resolvedCandidate, symlink: true };
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
        return { stat, path: realCandidate, symlink: false };
      }
    } catch (_err) {
      // Try the next candidate.
    }
  }
  return null;
}

function readJsonArtifact(artifact, fallback) {
  if (!artifact || artifact.symlink) return { ok: false, value: null };
  try {
    return { ok: true, value: JSON.parse(fs.readFileSync(artifact.path, 'utf8')) };
  } catch (_err) {
    return { ok: false, value: fallback };
  }
}

function artifactFileStatus(artifact) {
  if (artifact === null) return 'missing';
  if (artifact.symlink) return 'symlink';
  return artifact.stat.size <= 0 ? 'empty' : 'pass';
}

function artifactSymlinkStatus(artifact) {
  if (artifact === null) return 'missing';
  return artifact.symlink ? 'fail' : 'pass';
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

function measuredGeometryItemCount(items, viewport) {
  if (!Array.isArray(items)) return 0;
  const viewportWidth = jsonIntegerText(viewport.width);
  const viewportHeight = jsonIntegerText(viewport.height);
  if (viewportWidth === null || viewportHeight === null) return 0;
  const maxWidth = BigInt(viewportWidth);
  const maxHeight = BigInt(viewportHeight);
  let count = 0;
  for (const item of items) {
    if (!item || typeof item !== 'object') continue;
    const x = jsonIntegerText(item.x);
    const y = jsonIntegerText(item.y);
    const width = jsonIntegerText(item.width);
    const height = jsonIntegerText(item.height);
    if (x === null || y === null || width === null || height === null) continue;
    const left = BigInt(x);
    const top = BigInt(y);
    const right = left + BigInt(width);
    const bottom = top + BigInt(height);
    if (BigInt(width) < 1n || BigInt(height) < 1n) continue;
    if (right <= 0n || bottom <= 0n || left >= maxWidth || top >= maxHeight) continue;
    count += 1;
  }
  return count;
}

const proofPath = process.argv[2];
if (!proofPath) {
  emit('chrome_simple_web_layout_validation_status', 'fail');
  emit('chrome_simple_web_layout_validation_reason', 'usage-proof-json');
  process.exit(1);
}

const proofInfo = pathInfo(proofPath);
if (proofInfo.isSymlink) {
  emit('chrome_simple_web_layout_validation_status', 'fail');
  emit('chrome_simple_web_layout_validation_reason', 'proof-json-symlink');
  emit('chrome_simple_web_layout_proof_symlink_status', 'fail');
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
const capturedArgbChecksum = checksum(capturedArgbPixels);
const capturedArgbWeightedChecksum = weightedChecksum(capturedArgbPixels);
const geometryStat = artifactStat(proof.geometry_path, proofPath);
const geometryJson = readJsonArtifact(geometryStat, {});
const geometry = geometryJson.value || {};
const geometryViewport = geometry.viewport || {};
const geometryItems = Array.isArray(geometry.items) ? geometry.items : [];
const geometryMeasuredItemCount = measuredGeometryItemCount(geometryItems, geometryViewport);
const expectedProofSource = 'tools/chrome-live-bitmap/capture_html_argb.js';
const proofSourceStat = pathInfo(expectedProofSource);
const proofSourceFileStatus = proofSourceStat.isSymlink
  ? 'symlink'
  : proofSourceStat.lstat === null || !proofSourceStat.lstat.isFile()
    ? 'missing'
    : proofSourceStat.lstat.size <= 0
      ? 'empty'
      : 'pass';
const proofSourceSizeBytes = proofSourceFileStatus === 'empty'
  ? '0'
  : proofSourceFileStatus === 'pass'
    ? String(proofSourceStat.lstat.size)
    : '';
const chromeUserAgent = typeof proof.chrome_user_agent === 'string' ? proof.chrome_user_agent : '';
const chromeProduct = typeof proof.chrome_product === 'string' ? proof.chrome_product : '';
const chromeProtocolVersion = typeof proof.chrome_protocol_version === 'string' ? proof.chrome_protocol_version : '';
const chromeBin = typeof proof.chrome_bin === 'string' ? proof.chrome_bin.trim() : '';

let reason = 'pass';
if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
} else if (proof.proof_source !== expectedProofSource) {
  reason = 'unexpected-chrome-proof-source';
} else if (proofSourceFileStatus !== 'pass') {
  reason = `unexpected-chrome-proof-source-file-${proofSourceFileStatus}`;
} else if (proof.capture_mode !== 'chrome-devtools-screenshot') {
  reason = 'unexpected-chrome-capture-mode';
} else if (!/(Chrome|Chromium)\/[0-9]/.test(chromeUserAgent)) {
  reason = 'missing-chrome-runtime-user-agent';
} else if (!/(Chrome|Chromium|HeadlessChrome)\/[0-9]/.test(chromeProduct)) {
  reason = 'missing-chrome-product-version';
} else if (!/^[0-9]+(?:\.[0-9]+)*$/.test(chromeProtocolVersion)) {
  reason = 'missing-chrome-protocol-version';
} else if (chromeBin === '') {
  reason = 'missing-chrome-bin';
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
} else if (capturedArgbStat !== null && capturedArgbStat.symlink) {
  reason = 'captured-argb-symlink';
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
} else if (!sameInteger(proof.checksum, capturedArgbChecksum)) {
  reason = 'captured-argb-checksum-mismatch';
} else if (!sameInteger(proof.weighted_checksum, capturedArgbWeightedChecksum)) {
  reason = 'captured-argb-weighted-checksum-mismatch';
} else if (proof.geometry_written !== true) {
  reason = 'missing-chrome-geometry';
} else if (geometryStat !== null && geometryStat.symlink) {
  reason = 'chrome-geometry-symlink';
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
} else if (geometryMeasuredItemCount < 1) {
  reason = 'missing-chrome-geometry-measured-items';
} else if (!jsonIntegerBetween(proof.frame_us, 1, 1000000)) {
  reason = 'missing-chrome-timing';
}

emit('chrome_simple_web_layout_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('chrome_simple_web_layout_validation_reason', reason);
emit('chrome_simple_web_layout_proof_symlink_status', proofInfo.isSymlink ? 'fail' : 'pass');
emit('chrome_simple_web_layout_proof_source', proof.proof_source);
emit('chrome_simple_web_layout_proof_source_file_status', proofSourceFileStatus);
emit('chrome_simple_web_layout_proof_source_size_bytes', proofSourceSizeBytes);
emit('chrome_simple_web_layout_capture_mode', proof.capture_mode);
emit('chrome_simple_web_layout_chrome_user_agent', proof.chrome_user_agent);
emit('chrome_simple_web_layout_chrome_product', proof.chrome_product);
emit('chrome_simple_web_layout_chrome_protocol_version', proof.chrome_protocol_version);
emit('chrome_simple_web_layout_simple_checksum', integerTextOrClean(proof.expected_checksum));
emit('chrome_simple_web_layout_chrome_checksum', integerTextOrClean(proof.checksum));
emit('chrome_simple_web_layout_simple_weighted_checksum', integerTextOrClean(proof.expected_weighted_checksum));
emit('chrome_simple_web_layout_chrome_weighted_checksum', integerTextOrClean(proof.weighted_checksum));
emit('chrome_simple_web_layout_mismatch_count', jsonIntegerTextOrBlank(proof.mismatch_count));
emit('chrome_simple_web_layout_blur_or_tolerance_used', jsonBoolTextOrBlank(proof.blur_or_tolerance_used));
emit('chrome_simple_web_layout_chrome_frame_us', jsonIntegerTextOrBlank(proof.frame_us));
emit('chrome_simple_web_layout_capture_width', jsonIntegerTextOrBlank(proof.width));
emit('chrome_simple_web_layout_capture_height', jsonIntegerTextOrBlank(proof.height));
emit('chrome_simple_web_layout_captured_argb_path', proof.captured_argb_path);
emit('chrome_simple_web_layout_captured_argb_written', jsonBoolTextOrBlank(proof.captured_argb_written));
emit('chrome_simple_web_layout_captured_argb_file_status', artifactFileStatus(capturedArgbStat));
emit('chrome_simple_web_layout_captured_argb_symlink_status', artifactSymlinkStatus(capturedArgbStat));
emit('chrome_simple_web_layout_captured_argb_size_bytes', capturedArgbStat === null || capturedArgbStat.symlink ? '' : String(capturedArgbStat.stat.size));
emit('chrome_simple_web_layout_captured_argb_format', capturedArgb.format);
emit('chrome_simple_web_layout_captured_argb_producer', capturedArgb.producer);
emit('chrome_simple_web_layout_captured_argb_width', jsonIntegerTextOrBlank(capturedArgb.width));
emit('chrome_simple_web_layout_captured_argb_height', jsonIntegerTextOrBlank(capturedArgb.height));
emit('chrome_simple_web_layout_captured_argb_pixel_count', capturedArgbPixels === null ? '' : String(capturedArgbPixels.length));
emit('chrome_simple_web_layout_captured_argb_nonzero_pixel_count', capturedArgbNonzeroPixelCount);
emit('chrome_simple_web_layout_captured_argb_checksum', capturedArgbChecksum);
emit('chrome_simple_web_layout_captured_argb_weighted_checksum', capturedArgbWeightedChecksum);
emit('chrome_simple_web_layout_geometry_path', proof.geometry_path);
emit('chrome_simple_web_layout_geometry_written', jsonBoolTextOrBlank(proof.geometry_written));
emit('chrome_simple_web_layout_geometry_file_status', artifactFileStatus(geometryStat));
emit('chrome_simple_web_layout_geometry_symlink_status', artifactSymlinkStatus(geometryStat));
emit('chrome_simple_web_layout_geometry_size_bytes', geometryStat === null || geometryStat.symlink ? '' : String(geometryStat.stat.size));
emit('chrome_simple_web_layout_geometry_producer', geometry.producer);
emit('chrome_simple_web_layout_geometry_viewport_width', jsonIntegerTextOrBlank(geometryViewport.width));
emit('chrome_simple_web_layout_geometry_viewport_height', jsonIntegerTextOrBlank(geometryViewport.height));
emit('chrome_simple_web_layout_geometry_item_count', String(geometryItems.length));
emit('chrome_simple_web_layout_geometry_measured_item_count', String(geometryMeasuredItemCount));
emit('chrome_simple_web_layout_chrome_bin', proof.chrome_bin);

if (reason !== 'pass') {
  process.exit(1);
}
