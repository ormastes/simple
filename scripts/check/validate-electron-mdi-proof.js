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

function min(value, required) {
  const n = numberValue(value);
  return Number.isFinite(n) && n >= required;
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
  count: min(proof.count, 4),
  hasDesktop: proof.hasDesktop === true,
  imageCount: min(proof.imageCount, 1),
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
  bridgeIpcFrameCount: min(proof.bridgeIpcFrameCount, 8),
  bridgeBodyActionFrameRouted: proof.bridgeBodyActionFrameRouted === true,
  bridgeBodyInputFrameRouted: proof.bridgeBodyInputFrameRouted === true,
  bridgeBodyKeyFrameRouted: proof.bridgeBodyKeyFrameRouted === true,
  bridgeMouseDownFrameRouted: proof.bridgeMouseDownFrameRouted === true,
  bridgeMouseUpFrameRouted: proof.bridgeMouseUpFrameRouted === true,
  bridgeMinimizeFrameRouted: proof.bridgeMinimizeFrameRouted === true,
  bridgeMaximizeFrameRouted: proof.bridgeMaximizeFrameRouted === true,
  bridgeCloseFrameRouted: proof.bridgeCloseFrameRouted === true,
  taskbarItemCount: min(proof.taskbarItemCount, 4),
  taskbarIconCount: min(proof.taskbarIconCount, 4),
  taskbarIconsVisible: proof.taskbarIconsVisible === true,
  taskbarLabelsVisible: proof.taskbarLabelsVisible === true,
  htmlRenderable: proof.htmlRenderable === true,
};
const captureChecks = {
  screenshotPath: proof.screenshotPath === screenshotPath,
};
const performanceChecks = {
  performanceNowAvailable: proof.performanceNowAvailable === true,
  performanceNowDeltaMs: min(proof.performanceNowDeltaMs, 0),
};
const animationChecks = {
  animationFrameAvailable: proof.animationFrameAvailable === true,
  animationFrameCount: min(proof.animationFrameCount, 2),
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
emit('electron_mdi_window_count', Number.isFinite(numberValue(proof.count)) ? numberValue(proof.count) : '');
emit('electron_mdi_bridge_ipc_frame_count', Number.isFinite(numberValue(proof.bridgeIpcFrameCount)) ? numberValue(proof.bridgeIpcFrameCount) : '');
emit('electron_mdi_performance_now_available', proof.performanceNowAvailable === true ? 'true' : 'false');
emit('electron_mdi_performance_now_delta_ms', Number.isFinite(numberValue(proof.performanceNowDeltaMs)) ? numberValue(proof.performanceNowDeltaMs) : '');
emit('electron_mdi_animation_frame_available', proof.animationFrameAvailable === true ? 'true' : 'false');
emit('electron_mdi_animation_frame_count', Number.isFinite(numberValue(proof.animationFrameCount)) ? numberValue(proof.animationFrameCount) : '');
emit('electron_mdi_css_animation_probe', proof.cssAnimationProbe === true ? 'true' : 'false');
emit('electron_mdi_screenshot_path_matches', proof.screenshotPath === screenshotPath ? 'true' : 'false');
if (reason !== 'pass') {
  emit('reason', reason);
  process.exit(1);
}
