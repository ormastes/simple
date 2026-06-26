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

function decimalNumberText(value) {
  if (typeof value === 'number' && Number.isFinite(value)) return String(value);
  if (typeof value === 'string' && /^-?(?:[0-9]+)(?:\.[0-9]+)?$/.test(value.trim())) return value.trim();
  return null;
}

function integerAtLeast(value, required) {
  const text = decimalIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(required);
}

function decimalAtLeast(value, required) {
  const text = decimalNumberText(value);
  if (text === null) return false;
  return Number(text) >= required;
}

function integerTextOrBlank(value) {
  const text = decimalIntegerText(value);
  return text === null ? '' : text;
}

function decimalTextOrBlank(value) {
  const text = decimalNumberText(value);
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
  count: integerAtLeast(proof.count, 4),
  hasDesktop: proof.hasDesktop === true,
  imageCount: integerAtLeast(proof.imageCount, 1),
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
  bridgeIpcFrameCount: integerAtLeast(proof.bridgeIpcFrameCount, 8),
  bridgeBodyActionFrameRouted: proof.bridgeBodyActionFrameRouted === true,
  bridgeBodyInputFrameRouted: proof.bridgeBodyInputFrameRouted === true,
  bridgeBodyKeyFrameRouted: proof.bridgeBodyKeyFrameRouted === true,
  bridgeMouseDownFrameRouted: proof.bridgeMouseDownFrameRouted === true,
  bridgeMouseUpFrameRouted: proof.bridgeMouseUpFrameRouted === true,
  bridgeMinimizeFrameRouted: proof.bridgeMinimizeFrameRouted === true,
  bridgeMaximizeFrameRouted: proof.bridgeMaximizeFrameRouted === true,
  bridgeCloseFrameRouted: proof.bridgeCloseFrameRouted === true,
  taskbarItemCount: integerAtLeast(proof.taskbarItemCount, 4),
  taskbarIconCount: integerAtLeast(proof.taskbarIconCount, 4),
  taskbarIconsVisible: proof.taskbarIconsVisible === true,
  taskbarLabelsVisible: proof.taskbarLabelsVisible === true,
  htmlRenderable: proof.htmlRenderable === true,
};
const captureChecks = {
  screenshotPath: proof.screenshotPath === screenshotPath,
};
const performanceChecks = {
  performanceNowAvailable: proof.performanceNowAvailable === true,
  performanceNowDeltaMs: decimalAtLeast(proof.performanceNowDeltaMs, 0),
};
const animationChecks = {
  animationFrameAvailable: proof.animationFrameAvailable === true,
  animationFrameCount: integerAtLeast(proof.animationFrameCount, 2),
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
emit('electron_mdi_window_count', integerTextOrBlank(proof.count));
emit('electron_mdi_bridge_ipc_frame_count', integerTextOrBlank(proof.bridgeIpcFrameCount));
emit('electron_mdi_performance_now_available', proof.performanceNowAvailable === true ? 'true' : 'false');
emit('electron_mdi_performance_now_delta_ms', decimalTextOrBlank(proof.performanceNowDeltaMs));
emit('electron_mdi_animation_frame_available', proof.animationFrameAvailable === true ? 'true' : 'false');
emit('electron_mdi_animation_frame_count', integerTextOrBlank(proof.animationFrameCount));
emit('electron_mdi_css_animation_probe', proof.cssAnimationProbe === true ? 'true' : 'false');
emit('electron_mdi_screenshot_path_matches', proof.screenshotPath === screenshotPath ? 'true' : 'false');
if (reason !== 'pass') {
  emit('reason', reason);
  process.exit(1);
}
