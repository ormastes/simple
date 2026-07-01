#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');

const [platform, proofPath, ...sourcePaths] = process.argv.slice(2);

function die(reason) {
  console.log(`${platform || 'unknown'}_mdi_proof_status=fail`);
  console.log(`${platform || 'unknown'}_mdi_failure_marker_status=fail`);
  console.log(`${platform || 'unknown'}_mdi_normalize_reason=${reason}`);
  process.exit(1);
}

if (!platform || !/^(ios|android)$/.test(platform)) die('invalid-platform');
if (!proofPath) die('missing-proof-path');

function readIfFile(file) {
  try {
    const stat = fs.lstatSync(file);
    if (!stat.isFile()) return null;
    return fs.readFileSync(file, 'utf8');
  } catch (_err) {
    return null;
  }
}

function parseJsonText(text) {
  try {
    return JSON.parse(text);
  } catch (_err) {
    return null;
  }
}

function proofFromSources() {
  const direct = readIfFile(proofPath);
  if (direct) {
    const parsed = parseJsonText(direct);
    if (parsed) return parsed;
  }
  for (const source of sourcePaths) {
    const text = readIfFile(source);
    if (!text) continue;
    const lines = text.split(/\r?\n/).reverse();
    for (const line of lines) {
      const marker = line.match(/mdi proof:\s*(\{.*\})/);
      if (marker) {
        const parsed = parseJsonText(marker[1]);
        if (parsed) {
          fs.mkdirSync(path.dirname(proofPath), { recursive: true });
          fs.writeFileSync(proofPath, `${JSON.stringify(parsed)}\n`);
          return parsed;
        }
      }
    }
  }
  return null;
}

function integerAtLeast(value, min) {
  return typeof value === 'number' && Number.isSafeInteger(value) && value >= min;
}

function positiveAtMost(value, max) {
  return typeof value === 'number' && Number.isFinite(value) && value > 0 && value <= max;
}

function boolText(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return '';
}

function numberText(value) {
  if (typeof value !== 'number' || !Number.isFinite(value)) return '';
  return String(value);
}

function integerText(value) {
  if (typeof value !== 'number' || !Number.isSafeInteger(value)) return '';
  return String(value);
}

function eventSequenceText(value) {
  if (!Array.isArray(value)) return '';
  return value.map((entry) => String(entry).replace(/[\r\n]/g, ' ')).join(',');
}

const proof = proofFromSources();
if (!proof) die('proof-json-missing');

const expectedEventSequence = 'window_drag:move,app_action:body_click,app_input:body_input,app_key:body_key';
const renderPass = integerAtLeast(proof.imageCount, 1) && proof.htmlRenderable === true;
const eventPass =
  integerAtLeast(proof.count, 4) &&
  proof.hasDesktop === true &&
  proof.hasDragRuntime === true &&
  proof.hasDragEvents === true &&
  proof.dragMoved === true &&
  proof.hasWindowEventRuntime === true &&
  proof.appActionControlFound === true &&
  proof.appInputControlFound === true &&
  proof.bodyClickRouted === true &&
  proof.bodyInputRouted === true &&
  proof.bodyKeyRouted === true &&
  eventSequenceText(proof.eventSequence) === expectedEventSequence &&
  integerAtLeast(proof.taskbarItemCount, 4) &&
  integerAtLeast(proof.taskbarIconCount, 4) &&
  proof.taskbarIconsVisible === true &&
  proof.taskbarLabelsVisible === true;
const capturePass =
  integerAtLeast(proof.viewportWidth, 300) &&
  integerAtLeast(proof.viewportHeight, 300) &&
  typeof proof.devicePixelRatio === 'number' &&
  Number.isFinite(proof.devicePixelRatio) &&
  proof.devicePixelRatio > 0 &&
  (proof.screenOrientation === 'portrait' || proof.screenOrientation === 'landscape');
const performancePass = proof.performanceNowAvailable === true && positiveAtMost(proof.performanceNowDeltaMs, 1000);
const interactionPass = positiveAtMost(proof.inputToPaintMs, 1000);
const animationPass =
  proof.animationFrameAvailable === true &&
  integerAtLeast(proof.animationFrameCount, 2) &&
  proof.cssAnimationProbe === true;

const allSources = [proofPath, ...sourcePaths].filter((entry) => entry && entry.length > 0);
let sourceCount = 0;
let missingSourceCount = 0;
let symlinkSourceCount = 0;
let emptySourceCount = 0;
let nonregularSourceCount = 0;
let markerSourcePath = '';
let markerSourceSize = 0;
let failureMarkerStatus = 'pass';
const forbidden = [/F\/DEBUG/, /Fatal signal/, /F\/libc/, /F\/VulkanManager/, /panicked/, /InvalidUri/, /Cannot redefine/, /parse error/, /Permission denied/];

for (const source of allSources) {
  let stat;
  try {
    stat = fs.lstatSync(source);
  } catch (_err) {
    missingSourceCount += 1;
    continue;
  }
  if (stat.isSymbolicLink()) symlinkSourceCount += 1;
  if (!stat.isFile()) {
    nonregularSourceCount += 1;
    continue;
  }
  if (stat.size <= 0) emptySourceCount += 1;
  sourceCount += 1;
  const text = fs.readFileSync(source, 'utf8');
  if (!markerSourcePath && source !== proofPath && /(mdi proof|ios_mdi_probe|openWindow id=terminal)/.test(text)) {
    markerSourcePath = source;
    markerSourceSize = stat.size;
  }
  if (forbidden.some((pattern) => pattern.test(text))) failureMarkerStatus = 'fail';
}
if (!markerSourcePath && sourcePaths.length > 0) {
  for (const source of sourcePaths) {
    try {
      const stat = fs.lstatSync(source);
      if (stat.isFile() && stat.size > 0) {
        markerSourcePath = source;
        markerSourceSize = stat.size;
        break;
      }
    } catch (_err) {
      // Counted above.
    }
  }
}

function emit(key, value) {
  console.log(`${platform}_${key}=${value}`);
}

emit('mdi_proof_json', proofPath);
emit('mdi_proof_status', renderPass && eventPass && capturePass && performancePass && interactionPass && animationPass ? 'pass' : 'fail');
emit('mdi_failure_marker_status', failureMarkerStatus);
emit('mdi_proof_requested_source_count', allSources.length);
emit('mdi_proof_source_count', sourceCount);
emit('mdi_proof_marker_source_count', markerSourcePath ? 1 : 0);
emit('mdi_proof_missing_source_count', missingSourceCount);
emit('mdi_proof_symlink_source_count', symlinkSourceCount);
emit('mdi_proof_hardlink_source_count', 0);
emit('mdi_proof_duplicate_source_count', 0);
emit('mdi_proof_empty_source_count', emptySourceCount);
emit('mdi_proof_nonregular_source_count', nonregularSourceCount);
emit('mdi_proof_marker_source_path', markerSourcePath);
emit('mdi_proof_marker_source_size_bytes', markerSourceSize);
emit('mdi_render_status', renderPass ? 'pass' : 'fail');
emit('mdi_render_image_count', integerText(proof.imageCount));
emit('mdi_render_html_renderable', boolText(proof.htmlRenderable));
emit('mdi_event_status', eventPass ? 'pass' : 'fail');
emit('mdi_proof_window_count', integerText(proof.count));
emit('mdi_event_taskbar_item_count', integerText(proof.taskbarItemCount));
emit('mdi_event_taskbar_icon_count', integerText(proof.taskbarIconCount));
emit('mdi_event_has_desktop', boolText(proof.hasDesktop));
emit('mdi_event_drag_runtime_available', boolText(proof.hasDragRuntime));
emit('mdi_event_drag_events_available', boolText(proof.hasDragEvents));
emit('mdi_event_drag_moved', boolText(proof.dragMoved));
emit('mdi_event_window_event_runtime_available', boolText(proof.hasWindowEventRuntime));
emit('mdi_event_app_action_control_found', boolText(proof.appActionControlFound));
emit('mdi_event_app_input_control_found', boolText(proof.appInputControlFound));
emit('mdi_event_body_click_routed', boolText(proof.bodyClickRouted));
emit('mdi_event_body_input_routed', boolText(proof.bodyInputRouted));
emit('mdi_event_body_key_routed', boolText(proof.bodyKeyRouted));
emit('mdi_event_sequence', eventSequenceText(proof.eventSequence));
emit('mdi_event_taskbar_icons_visible', boolText(proof.taskbarIconsVisible));
emit('mdi_event_taskbar_labels_visible', boolText(proof.taskbarLabelsVisible));
emit('mdi_capture_status', capturePass ? 'pass' : 'fail');
emit('mdi_capture_viewport_width', integerText(proof.viewportWidth));
emit('mdi_capture_viewport_height', integerText(proof.viewportHeight));
emit('mdi_capture_device_pixel_ratio', numberText(proof.devicePixelRatio));
emit('mdi_capture_screen_orientation', proof.screenOrientation || '');
emit('mdi_performance_status', performancePass ? 'pass' : 'fail');
emit('mdi_performance_now_available', boolText(proof.performanceNowAvailable));
emit('mdi_performance_now_delta_ms', numberText(proof.performanceNowDeltaMs));
emit('mdi_interaction_latency_status', interactionPass ? 'pass' : 'fail');
emit('mdi_input_to_paint_ms', numberText(proof.inputToPaintMs));
emit('mdi_animation_status', animationPass ? 'pass' : 'fail');
emit('mdi_animation_frame_available', boolText(proof.animationFrameAvailable));
emit('mdi_animation_frame_count', integerText(proof.animationFrameCount));
emit('mdi_css_animation_probe', boolText(proof.cssAnimationProbe));

if (!(renderPass && eventPass && capturePass && performancePass && interactionPass && animationPass) || failureMarkerStatus !== 'pass') {
  process.exit(1);
}
