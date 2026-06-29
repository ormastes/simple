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

function textField(value) {
  return typeof value === 'string' ? value : '';
}

function plainObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function pathInfo(filePath) {
  let lstat = null;
  try {
    lstat = fs.lstatSync(filePath);
  } catch (_err) {
    lstat = null;
  }
  return {
    lstat,
    isSymlink: lstat !== null && lstat.isSymbolicLink(),
    hasMultipleLinks: lstat !== null && lstat.isFile() && lstat.nlink > 1,
  };
}

function proofSourceArtifact(filePath) {
  const info = pathInfo(filePath);
  if (info.isSymlink) return { status: 'symlink', size: '', actualSize: '' };
  if (info.lstat === null) return { status: 'missing', size: '', actualSize: '' };
  if (!info.lstat.isFile()) return { status: 'not-regular', size: '', actualSize: '' };
  if (info.hasMultipleLinks) return { status: 'hardlink', size: String(info.lstat.size), actualSize: '' };
  if (info.lstat.size <= 0) return { status: 'empty', size: '0', actualSize: '' };
  let bytes;
  try {
    bytes = fs.readFileSync(filePath);
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  const actualSize = String(bytes.length);
  if (actualSize !== String(info.lstat.size)) {
    return { status: 'size-mismatch', size: String(info.lstat.size), actualSize };
  }
  const source = bytes.toString('utf8');
  if (
    !source.includes('renderer: "electron-live-capture-page"') ||
    !source.includes('proof_source: "tools/electron-live-bitmap/exact_fixture.js"') ||
    !source.includes('capture_backend: captureBackend') ||
    !source.includes('compositor_mode: compositorMode')
  ) {
    return { status: 'marker-missing', size: String(info.lstat.size), actualSize };
  }
  return { status: 'pass', size: String(info.lstat.size), actualSize };
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
        return { stat: null, path: resolvedCandidate, symlink: true, hardlink: false };
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
        return { stat, path: realCandidate, symlink: false, hardlink: lstat.nlink > 1 };
      }
    } catch (_err) {
      // Try the next candidate.
    }
  }
  return null;
}

function readJsonArtifact(artifact) {
  if (!artifact || artifact.symlink || artifact.hardlink) return { ok: false, value: null };
  try {
    return { ok: true, value: JSON.parse(fs.readFileSync(artifact.path, 'utf8')) };
  } catch (_err) {
    return { ok: false, value: null };
  }
}

function artifactFileStatus(artifact) {
  if (artifact === null) return 'missing';
  if (artifact.symlink) return 'symlink';
  if (artifact.hardlink) return 'hardlink';
  return artifact.stat.size <= 0 ? 'empty' : 'pass';
}

function artifactSymlinkStatus(artifact) {
  if (artifact === null) return 'missing';
  return artifact.symlink ? 'fail' : 'pass';
}

function artifactHardlinkStatus(artifact) {
  if (artifact === null) return 'missing';
  return artifact.hardlink ? 'fail' : 'pass';
}

function artifactStatusFromFileStatus(status) {
  return status === 'pass' ? 'pass' : 'fail';
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
  emit('electron_simple_web_layout_validation_status', 'fail');
  emit('electron_simple_web_layout_validation_reason', 'usage-proof-json');
  process.exit(1);
}

const proofInfo = pathInfo(proofPath);
if (proofInfo.isSymlink) {
  emit('electron_simple_web_layout_validation_status', 'fail');
  emit('electron_simple_web_layout_validation_reason', 'proof-json-symlink');
  emit('electron_simple_web_layout_proof_symlink_status', 'fail');
  emit('electron_simple_web_layout_proof_hardlink_status', 'unknown');
  emit('electron_simple_web_layout_geometry_symlink_status', '');
  emit('electron_simple_web_layout_geometry_hardlink_status', '');
  emit('electron_simple_web_layout_captured_argb_symlink_status', '');
  emit('electron_simple_web_layout_captured_argb_hardlink_status', '');
  process.exit(1);
}
if (proofInfo.hasMultipleLinks) {
  emit('electron_simple_web_layout_validation_status', 'fail');
  emit('electron_simple_web_layout_validation_reason', 'proof-json-hardlink');
  emit('electron_simple_web_layout_proof_symlink_status', 'pass');
  emit('electron_simple_web_layout_proof_hardlink_status', 'fail');
  emit('electron_simple_web_layout_geometry_symlink_status', '');
  emit('electron_simple_web_layout_geometry_hardlink_status', '');
  emit('electron_simple_web_layout_captured_argb_symlink_status', '');
  emit('electron_simple_web_layout_captured_argb_hardlink_status', '');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('electron_simple_web_layout_validation_status', 'fail');
  emit('electron_simple_web_layout_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  emit('electron_simple_web_layout_proof_symlink_status', 'pass');
  emit('electron_simple_web_layout_proof_hardlink_status', 'pass');
  emit('electron_simple_web_layout_geometry_symlink_status', '');
  emit('electron_simple_web_layout_geometry_hardlink_status', '');
  emit('electron_simple_web_layout_captured_argb_symlink_status', '');
  emit('electron_simple_web_layout_captured_argb_hardlink_status', '');
  process.exit(1);
}

const capturedArgbStat = artifactStat(proof.captured_argb_path, proofPath);
const capturedArgbJson = readJsonArtifact(capturedArgbStat);
const capturedArgb = capturedArgbJson.value || {};
const capturedArgbPixels = Array.isArray(capturedArgb.pixels) ? capturedArgb.pixels : [];
const capturedArgbNonzeroPixels = nonzeroPixelCount(capturedArgbPixels);
const capturedArgbChecksum = checksum(capturedArgbPixels);
const capturedArgbWeightedChecksum = weightedChecksum(capturedArgbPixels);
const geometryStat = artifactStat(proof.geometry_path, proofPath);
const geometryJson = readJsonArtifact(geometryStat);
const geometry = geometryJson.value || {};
const geometryViewport = geometry.viewport || {};
const geometryItems = Array.isArray(geometry.items) ? geometry.items : [];
const geometryMeasuredItemCount = measuredGeometryItemCount(geometryItems, geometryViewport);
const expectedProofSource = 'tools/electron-live-bitmap/exact_fixture.js';
const proofSource = proofSourceArtifact(expectedProofSource);
const proofSourceFileStatus = proofSource.status;
const proofSourceSizeBytes = proofSource.size;
const proofSourceActualSizeBytes = proofSource.actualSize;
const proofSourceArtifactStatus =
  proofSourceFileStatus === 'pass' &&
  proofSourceSizeBytes !== '' &&
  proofSourceActualSizeBytes !== '' &&
  proofSourceSizeBytes === proofSourceActualSizeBytes
    ? 'pass'
    : 'fail';
const geometryFileStatus = artifactFileStatus(geometryStat);
const geometryArtifactStatus = artifactStatusFromFileStatus(geometryFileStatus);
const capturedArgbFileStatus = artifactFileStatus(capturedArgbStat);
const capturedArgbArtifactStatus = artifactStatusFromFileStatus(capturedArgbFileStatus);
const expectedCaptureBackend = 'electron-offscreen-capture-page';
const expectedCompositorMode = 'offscreen-osr-exact-srgb';
const browserEngine = textField(proof.browser_engine);
const electronUserAgent = textField(proof.electron_user_agent);
const electronProcessVersion = textField(proof.electron_process_version);
const chromeProcessVersion = textField(proof.chrome_process_version);
const proofGpuFeatureStatus = plainObject(proof.gpu_feature_status) ? proof.gpu_feature_status : null;
const proofGpuCompositing = textField(proof.gpu_compositing);
const proofGpuRasterization = textField(proof.gpu_rasterization);
const frameUsText = jsonIntegerText(proof.frame_us);
const estimatedFpsFloor = frameUsText === null || BigInt(frameUsText) <= 0n
  ? ''
  : String(1000000n / BigInt(frameUsText));

let reason = 'pass';
if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
} else if (proof.renderer !== 'electron-live-capture-page') {
  reason = 'unexpected-electron-renderer';
} else if (proof.proof_source !== expectedProofSource) {
  reason = 'unexpected-electron-proof-source';
} else if (proofSourceFileStatus !== 'pass') {
  reason = `unexpected-electron-proof-source-file-${proofSourceFileStatus}`;
} else if (typeof proof.scene !== 'string' || !proof.scene.startsWith('simple-web-layout-')) {
  reason = 'unexpected-electron-scene';
} else if (proof.capture_backend !== expectedCaptureBackend) {
  reason = 'unexpected-capture-backend';
} else if (proof.compositor_mode !== expectedCompositorMode) {
  reason = 'unexpected-compositor-mode';
} else if (
  browserEngine !== 'chromium' ||
  !/Electron\/[0-9]/.test(electronUserAgent) ||
  !/(Chrome|Chromium)\/[0-9]/.test(electronUserAgent) ||
  !/^[0-9]+(?:\.[0-9]+)*$/.test(electronProcessVersion) ||
  !/^[0-9]+(?:\.[0-9]+)*$/.test(chromeProcessVersion)
) {
  reason = 'missing-electron-runtime-identity';
} else if (
  proofGpuFeatureStatus === null ||
  proofGpuCompositing.trim() === '' ||
  proofGpuRasterization.trim() === '' ||
  proofGpuFeatureStatus.gpu_compositing !== proofGpuCompositing ||
  proofGpuFeatureStatus.rasterization !== proofGpuRasterization
) {
  reason = 'missing-gpu-feature-status';
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
  reason = 'missing-viewport-proof';
} else if (proof.captured_argb_written !== true) {
  reason = 'missing-captured-argb';
} else if (capturedArgbStat !== null && capturedArgbStat.symlink) {
  reason = 'captured-argb-symlink';
} else if (capturedArgbStat !== null && capturedArgbStat.hardlink) {
  reason = 'captured-argb-hardlink';
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
} else if (!sameInteger(proof.checksum, capturedArgbChecksum)) {
  reason = 'captured-argb-checksum-mismatch';
} else if (!sameInteger(proof.weighted_checksum, capturedArgbWeightedChecksum)) {
  reason = 'captured-argb-weighted-checksum-mismatch';
} else if (!jsonIntegerAtLeast(proof.capture_native_width, 1) || !jsonIntegerAtLeast(proof.capture_native_height, 1) || typeof proof.capture_downsampled !== 'boolean') {
  reason = 'missing-capture-provenance';
} else if (!sameJsonInteger(proof.capture_native_width, proof.width) || !sameJsonInteger(proof.capture_native_height, proof.height)) {
  reason = 'capture-viewport-mismatch';
} else if (proof.geometry_written !== true) {
  reason = 'missing-electron-geometry';
} else if (geometryStat !== null && geometryStat.symlink) {
  reason = 'electron-geometry-symlink';
} else if (geometryStat !== null && geometryStat.hardlink) {
  reason = 'electron-geometry-hardlink';
} else if (geometryStat === null) {
  reason = 'missing-electron-geometry-file';
} else if (geometryStat.stat.size <= 0) {
  reason = 'empty-electron-geometry-file';
} else if (!geometryJson.ok || geometry.producer !== 'electron-offscreen-geometry') {
  reason = 'malformed-electron-geometry';
} else if (!sameJsonInteger(geometryViewport.width, proof.width) || !sameJsonInteger(geometryViewport.height, proof.height)) {
  reason = 'electron-geometry-viewport-mismatch';
} else if (geometryItems.length < 1) {
  reason = 'missing-electron-geometry-items';
} else if (geometryMeasuredItemCount < 1) {
  reason = 'missing-electron-geometry-measured-items';
} else if (!jsonIntegerAtLeast(proof.iterations, 2)) {
  reason = 'missing-performance-iterations';
} else if (!jsonIntegerBetween(proof.frame_us, 1, 1000000)) {
  reason = 'missing-electron-timing';
}

emit('electron_simple_web_layout_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('electron_simple_web_layout_validation_reason', reason);
emit('electron_simple_web_layout_proof_symlink_status', proofInfo.isSymlink ? 'fail' : 'pass');
emit('electron_simple_web_layout_proof_hardlink_status', proofInfo.hasMultipleLinks ? 'fail' : 'pass');
emit('electron_simple_web_layout_renderer', proof.renderer);
emit('electron_simple_web_layout_proof_source', proof.proof_source);
emit('electron_simple_web_layout_proof_source_file_status', proofSourceFileStatus);
emit('electron_simple_web_layout_proof_source_size_bytes', proofSourceSizeBytes);
emit('electron_simple_web_layout_proof_source_actual_size_bytes', proofSourceActualSizeBytes);
emit('electron_simple_web_layout_proof_source_file_reason', proofSourceFileStatus);
emit('electron_simple_web_layout_proof_source_artifact_status', proofSourceArtifactStatus);
emit('electron_simple_web_layout_capture_backend', proof.capture_backend);
emit('electron_simple_web_layout_compositor_mode', proof.compositor_mode);
emit('electron_simple_web_layout_browser_engine', browserEngine);
emit('electron_simple_web_layout_electron_user_agent', electronUserAgent);
emit('electron_simple_web_layout_electron_process_version', electronProcessVersion);
emit('electron_simple_web_layout_chrome_process_version', chromeProcessVersion);
emit('electron_simple_web_layout_gpu_compositing', proofGpuCompositing);
emit('electron_simple_web_layout_gpu_rasterization', proofGpuRasterization);
emit('electron_simple_web_layout_scene', proof.scene);
emit('electron_simple_web_layout_simple_checksum', integerTextOrClean(proof.expected_checksum));
emit('electron_simple_web_layout_electron_checksum', integerTextOrClean(proof.checksum));
emit('electron_simple_web_layout_simple_weighted_checksum', integerTextOrClean(proof.expected_weighted_checksum));
emit('electron_simple_web_layout_electron_weighted_checksum', integerTextOrClean(proof.weighted_checksum));
emit('electron_simple_web_layout_mismatch_count', jsonIntegerTextOrBlank(proof.mismatch_count));
emit('electron_simple_web_layout_blur_or_tolerance_used', jsonBoolTextOrBlank(proof.blur_or_tolerance_used));
emit('electron_simple_web_layout_proof_iterations', jsonIntegerTextOrBlank(proof.iterations));
emit('electron_simple_web_layout_electron_frame_us', jsonIntegerTextOrBlank(proof.frame_us));
emit('electron_simple_web_layout_estimated_fps_floor', estimatedFpsFloor);
emit('electron_simple_web_layout_requested_width', jsonIntegerTextOrBlank(proof.width));
emit('electron_simple_web_layout_requested_height', jsonIntegerTextOrBlank(proof.height));
emit('electron_simple_web_layout_capture_native_width', jsonIntegerTextOrBlank(proof.capture_native_width));
emit('electron_simple_web_layout_capture_native_height', jsonIntegerTextOrBlank(proof.capture_native_height));
emit('electron_simple_web_layout_capture_downsampled', jsonBoolTextOrBlank(proof.capture_downsampled));
emit('electron_simple_web_layout_geometry_path', proof.geometry_path);
emit('electron_simple_web_layout_geometry_written', jsonBoolTextOrBlank(proof.geometry_written));
emit('electron_simple_web_layout_geometry_file_status', geometryFileStatus);
emit('electron_simple_web_layout_geometry_file_reason', geometryFileStatus);
emit('electron_simple_web_layout_geometry_artifact_status', geometryArtifactStatus);
emit('electron_simple_web_layout_geometry_symlink_status', artifactSymlinkStatus(geometryStat));
emit('electron_simple_web_layout_geometry_hardlink_status', artifactHardlinkStatus(geometryStat));
emit('electron_simple_web_layout_geometry_size_bytes', geometryStat === null || geometryStat.symlink || geometryStat.hardlink ? '' : String(geometryStat.stat.size));
emit('electron_simple_web_layout_geometry_producer', geometry.producer);
emit('electron_simple_web_layout_geometry_viewport_width', jsonIntegerTextOrBlank(geometryViewport.width));
emit('electron_simple_web_layout_geometry_viewport_height', jsonIntegerTextOrBlank(geometryViewport.height));
emit('electron_simple_web_layout_geometry_item_count', String(geometryItems.length));
emit('electron_simple_web_layout_geometry_measured_item_count', String(geometryMeasuredItemCount));
emit('electron_simple_web_layout_captured_argb_path', proof.captured_argb_path);
emit('electron_simple_web_layout_captured_argb_written', jsonBoolTextOrBlank(proof.captured_argb_written));
emit('electron_simple_web_layout_captured_argb_file_status', capturedArgbFileStatus);
emit('electron_simple_web_layout_captured_argb_file_reason', capturedArgbFileStatus);
emit('electron_simple_web_layout_captured_argb_artifact_status', capturedArgbArtifactStatus);
emit('electron_simple_web_layout_captured_argb_symlink_status', artifactSymlinkStatus(capturedArgbStat));
emit('electron_simple_web_layout_captured_argb_hardlink_status', artifactHardlinkStatus(capturedArgbStat));
emit('electron_simple_web_layout_captured_argb_size_bytes', capturedArgbStat === null || capturedArgbStat.symlink || capturedArgbStat.hardlink ? '' : String(capturedArgbStat.stat.size));
emit('electron_simple_web_layout_captured_argb_format', capturedArgb.format);
emit('electron_simple_web_layout_captured_argb_producer', capturedArgb.producer);
emit('electron_simple_web_layout_captured_argb_width', jsonIntegerTextOrBlank(capturedArgb.width));
emit('electron_simple_web_layout_captured_argb_height', jsonIntegerTextOrBlank(capturedArgb.height));
emit('electron_simple_web_layout_captured_argb_pixel_count', String(capturedArgbPixels.length));
emit('electron_simple_web_layout_captured_argb_nonzero_pixel_count', String(capturedArgbNonzeroPixels));
emit('electron_simple_web_layout_captured_argb_checksum', capturedArgbChecksum);
emit('electron_simple_web_layout_captured_argb_weighted_checksum', capturedArgbWeightedChecksum);

if (reason !== 'pass') {
  process.exit(1);
}
