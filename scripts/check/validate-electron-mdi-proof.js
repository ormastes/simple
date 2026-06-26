#!/usr/bin/env node
const fs = require('fs');

function clean(value) {
  if (value === undefined || value === null) return '';
  return String(value).replace(/[\r\n]/g, ' ');
}

function emit(key, value) {
  console.log(`${key}=${clean(value)}`);
}

function jsonIntegerText(value) {
  if (typeof value === 'number' && Number.isInteger(value)) return String(value);
  return null;
}

function jsonNumberText(value) {
  if (typeof value === 'number' && Number.isFinite(value)) return String(value);
  return null;
}

function jsonIntegerAtLeast(value, required) {
  const text = jsonIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(required);
}

function jsonDecimalGreaterThan(value, required) {
  const text = jsonNumberText(value);
  if (text === null) return false;
  return Number(text) > required;
}

function jsonIntegerTextOrBlank(value) {
  const text = jsonIntegerText(value);
  return text === null ? '' : text;
}

function jsonDecimalTextOrBlank(value) {
  const text = jsonNumberText(value);
  return text === null ? '' : text;
}

const [proofPath, screenshotPath] = process.argv.slice(2);
if (!proofPath || !screenshotPath) {
  emit('electron_mdi_json_proof', 'fail');
  emit('reason', 'usage-proof-screenshot');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('electron_mdi_json_proof', 'fail');
  emit('reason', `invalid-json:${err && err.message ? err.message : err}`);
  process.exit(1);
}

const eventChecks = {
  count: jsonIntegerAtLeast(proof.count, 4),
  hasDesktop: proof.hasDesktop === true,
  imageCount: jsonIntegerAtLeast(proof.imageCount, 1),
  hasDragRuntime: proof.hasDragRuntime === true,
  hasDragEvents: proof.hasDragEvents === true,
  dragMoved: proof.dragMoved === true,
  hasWindowEventRuntime: proof.hasWindowEventRuntime === true,
  appActionControlFound: proof.appActionControlFound === true,
  appInputControlFound: proof.appInputControlFound === true,
  bodyClickRouted: proof.bodyClickRouted === true,
  bodyInputRouted: proof.bodyInputRouted === true,
  bodyKeyRouted: proof.bodyKeyRouted === true,
  trafficMinimizeRouted: proof.trafficMinimizeRouted === true,
  trafficMaximizeRouted: proof.trafficMaximizeRouted === true,
  trafficCloseRouted: proof.trafficCloseRouted === true,
  bridgeIpcFrameCount: jsonIntegerAtLeast(proof.bridgeIpcFrameCount, 8),
  bridgeBodyActionFrameRouted: proof.bridgeBodyActionFrameRouted === true,
  bridgeBodyInputFrameRouted: proof.bridgeBodyInputFrameRouted === true,
  bridgeBodyKeyFrameRouted: proof.bridgeBodyKeyFrameRouted === true,
  bridgeMouseDownFrameRouted: proof.bridgeMouseDownFrameRouted === true,
  bridgeMouseUpFrameRouted: proof.bridgeMouseUpFrameRouted === true,
  bridgeMinimizeFrameRouted: proof.bridgeMinimizeFrameRouted === true,
  bridgeMaximizeFrameRouted: proof.bridgeMaximizeFrameRouted === true,
  bridgeCloseFrameRouted: proof.bridgeCloseFrameRouted === true,
  taskbarItemCount: jsonIntegerAtLeast(proof.taskbarItemCount, 4),
  taskbarIconCount: jsonIntegerAtLeast(proof.taskbarIconCount, 4),
  taskbarIconsVisible: proof.taskbarIconsVisible === true,
  taskbarLabelsVisible: proof.taskbarLabelsVisible === true,
  htmlRenderable: proof.htmlRenderable === true,
};
let screenshotStat = null;
try {
  screenshotStat = fs.statSync(screenshotPath);
} catch (_err) {
  screenshotStat = null;
}
let screenshotMagicOk = false;
if (screenshotStat !== null && screenshotStat.isFile() && screenshotStat.size >= 8) {
  try {
    const fd = fs.openSync(screenshotPath, 'r');
    const header = Buffer.alloc(8);
    fs.readSync(fd, header, 0, 8, 0);
    fs.closeSync(fd);
    screenshotMagicOk = header.equals(Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]));
  } catch (_err) {
    screenshotMagicOk = false;
  }
}
const captureChecks = {
  screenshotPath: proof.screenshotPath === screenshotPath,
  screenshotFileExists: screenshotStat !== null && screenshotStat.isFile(),
  screenshotFileNonempty: screenshotStat !== null && screenshotStat.isFile() && screenshotStat.size > 0,
  screenshotPngMagic: screenshotMagicOk,
};
const performanceChecks = {
  performanceNowAvailable: proof.performanceNowAvailable === true,
  performanceNowDeltaMs: jsonDecimalGreaterThan(proof.performanceNowDeltaMs, 0),
};
const animationChecks = {
  animationFrameAvailable: proof.animationFrameAvailable === true,
  animationFrameCount: jsonIntegerAtLeast(proof.animationFrameCount, 2),
  cssAnimationProbe: proof.cssAnimationProbe === true,
};

function failedNames(checks) {
  return Object.entries(checks).filter(([, ok]) => !ok).map(([name]) => name);
}

const eventFailed = failedNames(eventChecks);
const captureFailed = failedNames(captureChecks);
const performanceFailed = failedNames(performanceChecks);
const animationFailed = failedNames(animationChecks);

let reason = 'pass';
if (eventFailed.length) {
  reason = `event-contract-missing:${eventFailed.join(',')}`;
} else if (captureFailed.length) {
  reason = `capture-contract-missing:${captureFailed.join(',')}`;
} else if (performanceFailed.length) {
  reason = `performance-contract-missing:${performanceFailed.join(',')}`;
} else if (animationFailed.length) {
  reason = `animation-contract-missing:${animationFailed.join(',')}`;
}

emit('electron_mdi_json_proof', reason === 'pass' ? 'pass' : 'fail');
emit('electron_mdi_json_proof_reason', reason);
emit('electron_mdi_event_status', eventFailed.length ? 'fail' : 'pass');
emit('electron_mdi_capture_status', captureFailed.length ? 'fail' : 'pass');
emit('electron_mdi_performance_status', performanceFailed.length ? 'fail' : 'pass');
emit('electron_mdi_animation_status', animationFailed.length ? 'fail' : 'pass');
emit('electron_mdi_window_count', jsonIntegerTextOrBlank(proof.count));
emit('electron_mdi_bridge_ipc_frame_count', jsonIntegerTextOrBlank(proof.bridgeIpcFrameCount));
emit('electron_mdi_performance_now_available', proof.performanceNowAvailable === true ? 'true' : 'false');
emit('electron_mdi_performance_now_delta_ms', jsonDecimalTextOrBlank(proof.performanceNowDeltaMs));
emit('electron_mdi_animation_frame_available', proof.animationFrameAvailable === true ? 'true' : 'false');
emit('electron_mdi_animation_frame_count', jsonIntegerTextOrBlank(proof.animationFrameCount));
emit('electron_mdi_css_animation_probe', proof.cssAnimationProbe === true ? 'true' : 'false');
emit('electron_mdi_screenshot_path_matches', proof.screenshotPath === screenshotPath ? 'true' : 'false');
emit('electron_mdi_screenshot_file_status', screenshotStat !== null && screenshotStat.isFile() ? 'pass' : 'fail');
emit('electron_mdi_screenshot_size_bytes', screenshotStat !== null && screenshotStat.isFile() ? String(screenshotStat.size) : '');
emit('electron_mdi_screenshot_png_magic_status', screenshotMagicOk ? 'pass' : 'fail');
if (reason !== 'pass') {
  emit('reason', reason);
  process.exit(1);
}
