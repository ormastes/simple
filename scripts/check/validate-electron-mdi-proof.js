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

function jsonDecimalAtMost(value, required) {
  const text = jsonNumberText(value);
  if (text === null) return false;
  return Number(text) <= required;
}

function jsonIntegerTextOrBlank(value) {
  const text = jsonIntegerText(value);
  return text === null ? '' : text;
}

function jsonDecimalTextOrBlank(value) {
  const text = jsonNumberText(value);
  return text === null ? '' : text;
}

function jsonBoolTextOrBlank(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return '';
}

function pngHasStructuredImageChunks(bytes) {
  let offset = 8;
  let sawIdat = false;
  let sawIend = false;
  while (offset + 12 <= bytes.length) {
    const length = bytes.readUInt32BE(offset);
    const type = bytes.subarray(offset + 4, offset + 8).toString('ascii');
    const dataStart = offset + 8;
    const crcStart = dataStart + length;
    const next = crcStart + 4;
    if (next > bytes.length) return false;
    if (type === 'IDAT' && length > 0) {
      sawIdat = true;
    }
    if (type === 'IEND') {
      sawIend = true;
      break;
    }
    offset = next;
  }
  return sawIdat && sawIend;
}

const [proofPath, screenshotPath] = process.argv.slice(2);
const maxEventTimingMs = 1000;
if (!proofPath || !screenshotPath) {
  emit('electron_mdi_json_proof', 'fail');
  emit('reason', 'usage-proof-screenshot');
  process.exit(1);
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
    isRegularFile: lstat !== null && lstat.isFile(),
    hasMultipleLinks: lstat !== null && lstat.isFile() && lstat.nlink > 1,
  };
}

function artifactStatusFromReason(reason) {
  return reason === 'pass' ? 'pass' : 'fail';
}

function screenshotFileReason(info) {
  if (info.isSymlink) return 'symlink';
  if (info.lstat === null || info.stat === null) return 'missing';
  if (!info.isRegularFile) return 'not-regular';
  if (info.hasMultipleLinks) return 'hardlink';
  if (!info.stat.isFile()) return 'not-regular';
  if (info.stat.size <= 0) return 'empty';
  return 'pass';
}

const proofInfo = pathInfo(proofPath);
if (proofInfo.isSymlink) {
  emit('electron_mdi_json_proof', 'fail');
  emit('electron_mdi_json_proof_reason', 'proof-json-symlink');
  emit('electron_mdi_proof_symlink_status', 'fail');
  emit('electron_mdi_proof_hardlink_status', 'pass');
  emit('reason', 'proof-json-symlink');
  process.exit(1);
}
if (proofInfo.hasMultipleLinks) {
  emit('electron_mdi_json_proof', 'fail');
  emit('electron_mdi_json_proof_reason', 'proof-json-hardlink');
  emit('electron_mdi_proof_symlink_status', 'pass');
  emit('electron_mdi_proof_hardlink_status', 'fail');
  emit('reason', 'proof-json-hardlink');
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
const screenshotInfo = pathInfo(screenshotPath);
const screenshotStat = screenshotInfo.stat;
const screenshotFileReasonValue = screenshotFileReason(screenshotInfo);
const screenshotArtifactStatus = artifactStatusFromReason(screenshotFileReasonValue);
let screenshotMagicOk = false;
let screenshotStructureOk = false;
if (!screenshotInfo.isSymlink && screenshotStat !== null && screenshotStat.isFile() && screenshotStat.size >= 8) {
  try {
    const bytes = fs.readFileSync(screenshotPath);
    screenshotMagicOk = bytes.subarray(0, 8).equals(Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]));
    const ihdrOk =
      bytes.length >= 33 &&
      bytes.readUInt32BE(8) === 13 &&
      bytes.subarray(12, 16).toString('ascii') === 'IHDR' &&
      bytes.readUInt32BE(16) > 0 &&
      bytes.readUInt32BE(20) > 0;
    screenshotStructureOk =
      screenshotMagicOk &&
      ihdrOk &&
      pngHasStructuredImageChunks(bytes);
  } catch (_err) {
    screenshotMagicOk = false;
    screenshotStructureOk = false;
  }
}
const captureChecks = {
  screenshotPath: proof.screenshotPath === screenshotPath,
  screenshotFileExists: screenshotStat !== null && screenshotStat.isFile(),
  screenshotFileNonempty: screenshotStat !== null && screenshotStat.isFile() && screenshotStat.size > 0,
  screenshotNotSymlink: !screenshotInfo.isSymlink,
  screenshotNotHardlink: !screenshotInfo.hasMultipleLinks,
  screenshotPngMagic: screenshotMagicOk,
  screenshotPngStructure: screenshotStructureOk,
};
const performanceChecks = {
  performanceNowAvailable: proof.performanceNowAvailable === true,
  performanceNowDeltaMs: jsonDecimalGreaterThan(proof.performanceNowDeltaMs, 0),
  performanceNowDeltaMsWithinBudget:
    !jsonDecimalGreaterThan(proof.performanceNowDeltaMs, 0) ||
    jsonDecimalAtMost(proof.performanceNowDeltaMs, maxEventTimingMs),
};
const interactionLatencyChecks = {
  inputToPaintMs: jsonDecimalGreaterThan(proof.inputToPaintMs, 0),
  inputToPaintMsWithinBudget:
    !jsonDecimalGreaterThan(proof.inputToPaintMs, 0) ||
    jsonDecimalAtMost(proof.inputToPaintMs, maxEventTimingMs),
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
const interactionLatencyFailed = failedNames(interactionLatencyChecks);
const animationFailed = failedNames(animationChecks);

let reason = 'pass';
if (eventFailed.length) {
  reason = `event-contract-missing:${eventFailed.join(',')}`;
} else if (captureFailed.length) {
  reason = `capture-contract-missing:${captureFailed.join(',')}`;
} else if (performanceFailed.length) {
  reason = `performance-contract-missing:${performanceFailed.join(',')}`;
} else if (interactionLatencyFailed.length) {
  reason = `interaction-latency-contract-missing:${interactionLatencyFailed.join(',')}`;
} else if (animationFailed.length) {
  reason = `animation-contract-missing:${animationFailed.join(',')}`;
}

emit('electron_mdi_json_proof', reason === 'pass' ? 'pass' : 'fail');
emit('electron_mdi_json_proof_reason', reason);
emit('electron_mdi_proof_symlink_status', proofInfo.isSymlink ? 'fail' : 'pass');
emit('electron_mdi_proof_hardlink_status', proofInfo.hasMultipleLinks ? 'fail' : 'pass');
emit('electron_mdi_event_status', eventFailed.length ? 'fail' : 'pass');
emit('electron_mdi_capture_status', captureFailed.length ? 'fail' : 'pass');
emit('electron_mdi_performance_status', performanceFailed.length ? 'fail' : 'pass');
emit('electron_mdi_interaction_latency_status', interactionLatencyFailed.length ? 'fail' : 'pass');
emit('electron_mdi_animation_status', animationFailed.length ? 'fail' : 'pass');
emit('electron_mdi_window_count', jsonIntegerTextOrBlank(proof.count));
emit('electron_mdi_render_image_count', jsonIntegerTextOrBlank(proof.imageCount));
emit('electron_mdi_render_html_renderable', jsonBoolTextOrBlank(proof.htmlRenderable));
emit('electron_mdi_event_has_desktop', jsonBoolTextOrBlank(proof.hasDesktop));
emit('electron_mdi_event_drag_runtime_available', jsonBoolTextOrBlank(proof.hasDragRuntime));
emit('electron_mdi_event_drag_events_available', jsonBoolTextOrBlank(proof.hasDragEvents));
emit('electron_mdi_event_drag_moved', jsonBoolTextOrBlank(proof.dragMoved));
emit('electron_mdi_event_window_event_runtime_available', jsonBoolTextOrBlank(proof.hasWindowEventRuntime));
emit('electron_mdi_event_app_action_control_found', jsonBoolTextOrBlank(proof.appActionControlFound));
emit('electron_mdi_event_app_input_control_found', jsonBoolTextOrBlank(proof.appInputControlFound));
emit('electron_mdi_event_body_click_routed', jsonBoolTextOrBlank(proof.bodyClickRouted));
emit('electron_mdi_event_body_input_routed', jsonBoolTextOrBlank(proof.bodyInputRouted));
emit('electron_mdi_event_body_key_routed', jsonBoolTextOrBlank(proof.bodyKeyRouted));
emit('electron_mdi_event_traffic_minimize_routed', jsonBoolTextOrBlank(proof.trafficMinimizeRouted));
emit('electron_mdi_event_traffic_maximize_routed', jsonBoolTextOrBlank(proof.trafficMaximizeRouted));
emit('electron_mdi_event_traffic_close_routed', jsonBoolTextOrBlank(proof.trafficCloseRouted));
emit('electron_mdi_bridge_ipc_frame_count', jsonIntegerTextOrBlank(proof.bridgeIpcFrameCount));
emit('electron_mdi_bridge_body_action_frame_routed', jsonBoolTextOrBlank(proof.bridgeBodyActionFrameRouted));
emit('electron_mdi_bridge_body_input_frame_routed', jsonBoolTextOrBlank(proof.bridgeBodyInputFrameRouted));
emit('electron_mdi_bridge_body_key_frame_routed', jsonBoolTextOrBlank(proof.bridgeBodyKeyFrameRouted));
emit('electron_mdi_bridge_mouse_down_frame_routed', jsonBoolTextOrBlank(proof.bridgeMouseDownFrameRouted));
emit('electron_mdi_bridge_mouse_up_frame_routed', jsonBoolTextOrBlank(proof.bridgeMouseUpFrameRouted));
emit('electron_mdi_bridge_minimize_frame_routed', jsonBoolTextOrBlank(proof.bridgeMinimizeFrameRouted));
emit('electron_mdi_bridge_maximize_frame_routed', jsonBoolTextOrBlank(proof.bridgeMaximizeFrameRouted));
emit('electron_mdi_bridge_close_frame_routed', jsonBoolTextOrBlank(proof.bridgeCloseFrameRouted));
emit('electron_mdi_event_taskbar_item_count', jsonIntegerTextOrBlank(proof.taskbarItemCount));
emit('electron_mdi_event_taskbar_icon_count', jsonIntegerTextOrBlank(proof.taskbarIconCount));
emit('electron_mdi_event_taskbar_icons_visible', jsonBoolTextOrBlank(proof.taskbarIconsVisible));
emit('electron_mdi_event_taskbar_labels_visible', jsonBoolTextOrBlank(proof.taskbarLabelsVisible));
emit('electron_mdi_performance_now_available', jsonBoolTextOrBlank(proof.performanceNowAvailable));
emit('electron_mdi_performance_now_delta_ms', jsonDecimalTextOrBlank(proof.performanceNowDeltaMs));
emit('electron_mdi_input_to_paint_ms', jsonDecimalTextOrBlank(proof.inputToPaintMs));
emit('electron_mdi_animation_frame_available', jsonBoolTextOrBlank(proof.animationFrameAvailable));
emit('electron_mdi_animation_frame_count', jsonIntegerTextOrBlank(proof.animationFrameCount));
emit('electron_mdi_css_animation_probe', jsonBoolTextOrBlank(proof.cssAnimationProbe));
emit('electron_mdi_screenshot_path_matches', proof.screenshotPath === screenshotPath ? 'true' : 'false');
emit('electron_mdi_screenshot_symlink_status', screenshotInfo.isSymlink ? 'fail' : 'pass');
emit('electron_mdi_screenshot_hardlink_status', screenshotInfo.hasMultipleLinks ? 'fail' : 'pass');
emit('electron_mdi_screenshot_file_status', screenshotStat !== null && screenshotStat.isFile() ? 'pass' : 'fail');
emit('electron_mdi_screenshot_file_reason', screenshotFileReasonValue);
emit('electron_mdi_screenshot_artifact_status', screenshotArtifactStatus);
emit('electron_mdi_screenshot_size_bytes', screenshotStat !== null && screenshotStat.isFile() ? String(screenshotStat.size) : '');
emit('electron_mdi_screenshot_png_magic_status', screenshotMagicOk ? 'pass' : 'fail');
emit('electron_mdi_screenshot_png_structure_status', screenshotStructureOk ? 'pass' : 'fail');
if (reason !== 'pass') {
  emit('reason', reason);
  process.exit(1);
}
