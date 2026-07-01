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
  if (typeof value === 'bigint') return value.toString();
  if (typeof value === 'string' && /^[0-9]+$/.test(value.trim())) return value.trim();
  return null;
}

function integerNumberAtLeast(value, min) {
  return typeof value === 'number' && Number.isInteger(value) && value >= min;
}

function finiteNumberGreaterThan(value, min) {
  return typeof value === 'number' && Number.isFinite(value) && value > min;
}

function finiteNumberAtMost(value, max) {
  return typeof value === 'number' && Number.isFinite(value) && value <= max;
}

function jsonIntegerTextOrBlank(value) {
  return typeof value === 'number' && Number.isInteger(value) ? String(value) : '';
}

function jsonNumberTextOrBlank(value) {
  return typeof value === 'number' && Number.isFinite(value) ? String(value) : '';
}

function jsonBoolTextOrBlank(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return '';
}

function textSample(value) {
  return typeof value === 'string' ? value : '';
}

function versionText(value) {
  return typeof value === 'string' && /^[0-9]+(?:\.[0-9]+)*$/.test(value);
}

function proofSourceArtifact(marker) {
  const [filePath, symbol] = marker.split(':');
  let stat;
  try {
    stat = fs.lstatSync(filePath);
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  if (stat.isSymbolicLink()) return { status: 'symlink', size: '', actualSize: '' };
  if (!stat.isFile()) return { status: 'not-regular', size: '', actualSize: '' };
  const actualSize = String(stat.size);
  if (stat.nlink > 1) return { status: 'hardlink', size: actualSize, actualSize };
  if (stat.size <= 0) return { status: 'empty', size: '0', actualSize: '0' };
  let source = '';
  try {
    source = fs.readFileSync(filePath, 'utf8');
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  if (!source.includes(`function ${symbol}`) || !source.includes(`proof_source: '${marker}'`)) {
    return { status: 'symbol-missing', size: actualSize, actualSize };
  }
  return { status: 'pass', size: actualSize, actualSize };
}

function pngArtifact(filePath, expectedSize) {
  if (typeof filePath !== 'string' || filePath.length === 0) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  let stat;
  try {
    stat = fs.lstatSync(filePath);
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  if (stat.isSymbolicLink()) return { status: 'symlink', size: '', actualSize: '' };
  if (!stat.isFile()) return { status: 'not-regular', size: '', actualSize: '' };
  const actualSize = String(stat.size);
  if (stat.nlink > 1) return { status: 'hardlink', size: actualSize, actualSize };
  if (stat.size <= 8) return { status: 'empty', size: actualSize, actualSize };
  const expectedSizeText = jsonIntegerTextOrBlank(expectedSize);
  if (expectedSizeText && expectedSizeText !== actualSize) {
    return { status: 'size-mismatch', size: expectedSizeText, actualSize };
  }
  let header;
  try {
    header = fs.readFileSync(filePath).subarray(0, 8);
  } catch (_err) {
    return { status: 'missing', size: '', actualSize: '' };
  }
  const pngSignature = Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);
  if (header.length !== pngSignature.length || !header.equals(pngSignature)) {
    return { status: 'not-png', size: actualSize, actualSize };
  }
  return { status: 'pass', size: actualSize, actualSize };
}

function artifactStatus(artifact) {
  return artifact.status === 'pass' &&
    artifact.size !== '' &&
    artifact.actualSize !== '' &&
    artifact.size === artifact.actualSize
    ? 'pass'
    : 'fail';
}

const [proofPath, widthText, heightText] = process.argv.slice(2);
if (!proofPath || !widthText || !heightText) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'usage-proof-width-height');
  process.exit(1);
}

let proofPathStat;
try {
  proofPathStat = fs.lstatSync(proofPath);
} catch (err) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', `missing-proof-json:${err && err.message ? err.message : err}`);
  emit('electron_live_smoke_proof_symlink_status', 'unknown');
  emit('electron_live_smoke_proof_hardlink_status', 'unknown');
  process.exit(1);
}

if (proofPathStat.isSymbolicLink()) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'proof-json-symlink');
  emit('electron_live_smoke_proof_symlink_status', 'fail');
  emit('electron_live_smoke_proof_hardlink_status', 'unknown');
  process.exit(1);
}

if (!proofPathStat.isFile()) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'proof-json-not-regular');
  emit('electron_live_smoke_proof_symlink_status', 'pass');
  emit('electron_live_smoke_proof_hardlink_status', 'pass');
  process.exit(1);
}

if (proofPathStat.nlink > 1) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'proof-json-hardlink');
  emit('electron_live_smoke_proof_symlink_status', 'pass');
  emit('electron_live_smoke_proof_hardlink_status', 'fail');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  process.exit(1);
}

const expectedWidthText = decimalIntegerText(widthText);
const expectedHeightText = decimalIntegerText(heightText);
const expectedWidth = expectedWidthText === null ? NaN : Number(expectedWidthText);
const expectedHeight = expectedHeightText === null ? NaN : Number(expectedHeightText);
const expectedProofSource = 'src/app/ui.electron/bridge.js:electronLiveSmokeProofScript';
const proofSource = proofSourceArtifact(expectedProofSource);
const screenshotArtifact = pngArtifact(proof.screenshot_path, proof.screenshot_png_size_bytes);
const proofSourceArtifactStatus = artifactStatus(proofSource);
const screenshotArtifactStatus = artifactStatus(screenshotArtifact);
const userAgent = textSample(proof.electron_user_agent);
const maxEventTimingMs = 1000;
const maxEventDispatchToPaintMs = 1000;

let reason = 'pass';
if (proof.target !== 'electron') {
  reason = 'unexpected-target';
} else if (proof.surface_id !== 'main') {
  reason = 'unexpected-surface';
} else if (proof.proof_source !== expectedProofSource) {
  reason = 'unexpected-proof-source';
} else if (proofSource.status !== 'pass') {
  reason = `unexpected-proof-source-file-${proofSource.status}`;
} else if (proof.browser_engine !== 'chromium') {
  reason = 'unexpected-browser-engine';
} else if (!/Electron\/[0-9]/.test(userAgent) || !/(Chrome|Chromium)\/[0-9]/.test(userAgent)) {
  reason = 'missing-electron-chromium-user-agent';
} else if (!versionText(proof.electron_process_version) || !versionText(proof.chrome_process_version)) {
  reason = 'missing-electron-chromium-process-versions';
} else if (!Number.isInteger(expectedWidth) || expectedWidth < 1 || proof.width !== expectedWidth) {
  reason = 'unexpected-width';
} else if (!Number.isInteger(expectedHeight) || expectedHeight < 1 || proof.height !== expectedHeight) {
  reason = 'unexpected-height';
} else if (!integerNumberAtLeast(proof.body_html_length, 1)) {
  reason = 'missing-render-html';
} else if (!integerNumberAtLeast(proof.css_length, 1)) {
  reason = 'missing-render-css';
} else if (proof.app_element_present !== true) {
  reason = 'missing-app-element';
} else if (!integerNumberAtLeast(proof.body_text_length, 1)) {
  reason = 'missing-rendered-text';
} else if (
  textSample(proof.body_text_sample).length < 1 ||
  !textSample(proof.body_text_sample).includes('Hello World from Web!') ||
  textSample(proof.body_text_sample).length > proof.body_text_length
) {
  reason = 'missing-rendered-text-sample';
} else if (
  proof.performance_now_available !== true ||
  !finiteNumberGreaterThan(proof.performance_now_delta_ms, 0) ||
  !finiteNumberAtMost(proof.performance_now_delta_ms, maxEventTimingMs)
) {
  reason = 'missing-performance-now';
} else if (proof.animation_frame_available !== true || !integerNumberAtLeast(proof.animation_frame_count, 2)) {
  reason = 'missing-animation-frames';
} else if (proof.css_animation_probe !== true) {
  reason = 'missing-css-animation';
} else if (
  proof.event_dispatch_available !== true ||
  !integerNumberAtLeast(proof.event_dispatch_count, 1) ||
  proof.event_dispatch_type !== 'simple-electron-live-smoke-event' ||
  proof.event_dispatch_detail !== 'live-smoke-input' ||
  textSample(proof.event_dispatch_error).length > 0
) {
  reason = 'missing-event-dispatch';
} else if (
  !finiteNumberGreaterThan(proof.event_dispatch_to_paint_ms, 0) ||
  !finiteNumberAtMost(proof.event_dispatch_to_paint_ms, maxEventDispatchToPaintMs)
) {
  reason = 'missing-event-dispatch-to-paint';
} else if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
} else if (textSample(proof.screenshot_error).length > 0) {
  reason = 'screenshot-capture-error';
} else if (screenshotArtifact.status !== 'pass') {
  reason = `screenshot-artifact-${screenshotArtifact.status}`;
} else if (proof.screenshot_width !== expectedWidth || proof.screenshot_height !== expectedHeight) {
  reason = 'screenshot-dimensions-mismatch';
} else if (!integerNumberAtLeast(proof.screenshot_png_size_bytes, 9)) {
  reason = 'screenshot-png-size-missing';
} else if (proof.screenshot_bitmap_byte_count !== expectedWidth * expectedHeight * 4) {
  reason = 'screenshot-bitmap-size-mismatch';
} else if (!integerNumberAtLeast(proof.screenshot_pixel_checksum, 1)) {
  reason = 'screenshot-pixel-checksum-missing';
} else if (!integerNumberAtLeast(proof.screenshot_nontransparent_pixel_count, 1)) {
  reason = 'screenshot-nontransparent-pixels-missing';
} else if (!integerNumberAtLeast(proof.screenshot_distinct_color_count, 2)) {
  reason = 'screenshot-distinct-colors-missing';
}

emit('electron_live_smoke_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('electron_live_smoke_validation_reason', reason);
emit('electron_live_smoke_proof_symlink_status', proofPathStat.isSymbolicLink() ? 'fail' : 'pass');
emit('electron_live_smoke_proof_hardlink_status', proofPathStat.nlink > 1 ? 'fail' : 'pass');
emit('electron_live_smoke_target', proof.target);
emit('electron_live_smoke_surface_id', proof.surface_id);
emit('electron_live_smoke_proof_source', proof.proof_source);
emit('electron_live_smoke_proof_source_file_status', proofSource.status);
emit('electron_live_smoke_proof_source_size_bytes', proofSource.size);
emit('electron_live_smoke_proof_source_actual_size_bytes', proofSource.actualSize);
emit('electron_live_smoke_proof_source_file_reason', proofSource.status);
emit('electron_live_smoke_proof_source_artifact_status', proofSourceArtifactStatus);
emit('electron_live_smoke_browser_engine', proof.browser_engine);
emit('electron_live_smoke_electron_user_agent', proof.electron_user_agent);
emit('electron_live_smoke_electron_process_version', proof.electron_process_version);
emit('electron_live_smoke_chrome_process_version', proof.chrome_process_version);
emit('electron_live_smoke_width', jsonIntegerTextOrBlank(proof.width));
emit('electron_live_smoke_height', jsonIntegerTextOrBlank(proof.height));
emit('electron_live_smoke_body_html_length', jsonIntegerTextOrBlank(proof.body_html_length));
emit('electron_live_smoke_css_length', jsonIntegerTextOrBlank(proof.css_length));
emit('electron_live_smoke_app_element_present', jsonBoolTextOrBlank(proof.app_element_present));
emit('electron_live_smoke_body_text_length', jsonIntegerTextOrBlank(proof.body_text_length));
emit('electron_live_smoke_body_text_sample', proof.body_text_sample);
emit('electron_live_smoke_performance_now_available', jsonBoolTextOrBlank(proof.performance_now_available));
emit('electron_live_smoke_performance_now_delta_ms', jsonNumberTextOrBlank(proof.performance_now_delta_ms));
emit('electron_live_smoke_animation_frame_available', jsonBoolTextOrBlank(proof.animation_frame_available));
emit('electron_live_smoke_animation_frame_count', jsonIntegerTextOrBlank(proof.animation_frame_count));
emit('electron_live_smoke_css_animation_probe', jsonBoolTextOrBlank(proof.css_animation_probe));
emit('electron_live_smoke_event_dispatch_available', jsonBoolTextOrBlank(proof.event_dispatch_available));
emit('electron_live_smoke_event_dispatch_count', jsonIntegerTextOrBlank(proof.event_dispatch_count));
emit('electron_live_smoke_event_dispatch_type', proof.event_dispatch_type);
emit('electron_live_smoke_event_dispatch_detail', proof.event_dispatch_detail);
emit('electron_live_smoke_event_dispatch_error', proof.event_dispatch_error);
emit('electron_live_smoke_event_dispatch_to_paint_ms', jsonNumberTextOrBlank(proof.event_dispatch_to_paint_ms));
emit('electron_live_smoke_screenshot_path', proof.screenshot_path);
emit('electron_live_smoke_screenshot_file_status', screenshotArtifact.status);
emit('electron_live_smoke_screenshot_size_bytes', jsonIntegerTextOrBlank(proof.screenshot_png_size_bytes));
emit('electron_live_smoke_screenshot_actual_size_bytes', screenshotArtifact.actualSize);
emit('electron_live_smoke_screenshot_file_reason', screenshotArtifact.status);
emit('electron_live_smoke_screenshot_artifact_status', screenshotArtifactStatus);
emit('electron_live_smoke_screenshot_width', jsonIntegerTextOrBlank(proof.screenshot_width));
emit('electron_live_smoke_screenshot_height', jsonIntegerTextOrBlank(proof.screenshot_height));
emit('electron_live_smoke_screenshot_bitmap_byte_count', jsonIntegerTextOrBlank(proof.screenshot_bitmap_byte_count));
emit('electron_live_smoke_screenshot_pixel_checksum', jsonIntegerTextOrBlank(proof.screenshot_pixel_checksum));
emit('electron_live_smoke_screenshot_nontransparent_pixel_count', jsonIntegerTextOrBlank(proof.screenshot_nontransparent_pixel_count));
emit('electron_live_smoke_screenshot_distinct_color_count', jsonIntegerTextOrBlank(proof.screenshot_distinct_color_count));
emit('electron_live_smoke_screenshot_error', proof.screenshot_error);
emit('electron_live_smoke_blur_or_tolerance_used', jsonBoolTextOrBlank(proof.blur_or_tolerance_used));

if (reason !== 'pass') {
  process.exit(1);
}
