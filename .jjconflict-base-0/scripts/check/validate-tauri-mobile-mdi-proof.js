#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const [prefix, jsonPath, ...files] = process.argv.slice(2);
const maxEventTimingMs = 1000;
const expectedEventSequence = [
  "window_drag:move",
  "app_action:body_click",
  "app_input:body_input",
  "app_key:body_key",
];

function clean(value) {
  if (value === undefined || value === null) return "";
  return String(value).replace(/[\r\n]/g, " ");
}

function emit(key, value) {
  console.log(`${prefix}_${key}=${clean(value)}`);
}

function jsonIntegerText(value) {
  if (typeof value === "number" && Number.isSafeInteger(value)) return String(value);
  return null;
}

function jsonNumberText(value) {
  if (typeof value === "number" && Number.isFinite(value)) return String(value);
  return null;
}

function jsonIntegerAtLeast(value, min) {
  const text = jsonIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(min);
}

function jsonDecimalGreaterThan(value, min) {
  const text = jsonNumberText(value);
  if (text === null) return false;
  return Number(text) > min;
}

function jsonDecimalAtMost(value, max) {
  const text = jsonNumberText(value);
  if (text === null) return false;
  return Number(text) <= max;
}

function jsonIntegerTextOrBlank(value) {
  const text = jsonIntegerText(value);
  return text === null ? "" : text;
}

function jsonDecimalTextOrBlank(value) {
  const text = jsonNumberText(value);
  return text === null ? "" : text;
}

function orientationText(value) {
  if (value === "portrait" || value === "landscape") return value;
  return "";
}

function jsonBoolTextOrBlank(value) {
  if (value === true) return "true";
  if (value === false) return "false";
  return "";
}

function eventSequenceText(value) {
  if (!Array.isArray(value)) return "";
  return value.map(clean).join(",");
}

function eventSequenceMatches(value) {
  return Array.isArray(value) &&
    value.length === expectedEventSequence.length &&
    expectedEventSequence.every((entry, index) => value[index] === entry);
}

function fail(reason) {
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", reason);
  process.exit(1);
}

if (!prefix || !jsonPath || files.length === 0) {
  fail("usage-prefix-jsonpath-files");
}

if (prefix !== "ios" && prefix !== "android") {
  console.log("mobile_mdi_proof_status=fail");
  console.log("mobile_mdi_proof_reason=unsupported-platform-prefix");
  console.log(`mobile_mdi_proof_prefix=${clean(prefix)}`);
  process.exit(1);
}

const requestedSourceCount = files.length;
let missingSourceCount = 0;
let emptySourceCount = 0;
let symlinkSourceCount = 0;
let hardlinkSourceCount = 0;
let duplicateSourceCount = 0;
let nonregularSourceCount = 0;
let sourceCount = 0;
let lastJson = "";
let proofMarkerSourceCount = 0;
let canonicalProofJson = "";
let conflictingProofLog = false;
let proofMarkerParseError = "";
let failureMarker = false;
let proofMarkerSourcePath = "";
let proofMarkerSourceSizeBytes = "";
let proofMarkerSourceActualSizeBytes = "";
let proofMarkerSourceFileStatus = "unavailable";
let proofMarkerSourceFileReason = "not-run";
const sourceFileIdentities = new Set();
const failureMarkerPattern =
  /(eval FAIL|inline shell eval FAIL|delayed inline shell eval FAIL|Fatal signal|F\/DEBUG|F\/libc|NSURLErrorDomain|failed provisional load|Headless UI completed|subprocess exited with code|Simple subprocess stdout closed before a valid render arrived|parse error|Requested GL implementation .* not found|Exiting GPU process due to errors during initialization)/i;
function fileIdentity(stat) {
  if (!stat || stat.dev === undefined || stat.ino === undefined) return "";
  return `${stat.dev}:${stat.ino}`;
}

let jsonPathStat = null;
try {
  jsonPathStat = fs.lstatSync(jsonPath);
} catch (_err) {
  jsonPathStat = null;
}
const jsonPathIdentity = jsonPathStat && jsonPathStat.isFile() ? fileIdentity(jsonPathStat) : "";

for (const file of files) {
  let stat = null;
  if (file) {
    try {
      stat = fs.lstatSync(file);
    } catch (_err) {
      stat = null;
    }
  }
  if (!file || !stat) {
    missingSourceCount += 1;
    continue;
  }
  if (stat.isSymbolicLink()) {
    symlinkSourceCount += 1;
    continue;
  }
  if (!stat.isFile()) {
    nonregularSourceCount += 1;
    continue;
  }
  const identity = fileIdentity(stat);
  if (stat.nlink > 1 && (!identity || identity !== jsonPathIdentity)) {
    hardlinkSourceCount += 1;
    continue;
  }
  if (identity) {
    if (sourceFileIdentities.has(identity)) {
      duplicateSourceCount += 1;
      continue;
    }
    sourceFileIdentities.add(identity);
  }
  const text = fs.readFileSync(file, "utf8");
  if (text.length === 0) {
    emptySourceCount += 1;
    continue;
  }
  sourceCount += 1;
  if (failureMarkerPattern.test(text)) {
    failureMarker = true;
  }
  const matches = [...text.matchAll(/\[tauri-shell\] mdi proof:\s*(\{[^\r\n]*\})/g)];
  if (matches.length > 0) {
    const sourceLastJson = matches[matches.length - 1][1];
    proofMarkerSourceCount += 1;
    proofMarkerSourcePath = file;
    proofMarkerSourceSizeBytes = String(stat.size);
    proofMarkerSourceActualSizeBytes = String(stat.size);
    proofMarkerSourceFileStatus = "pass";
    proofMarkerSourceFileReason = "pass";
    try {
      const normalized = JSON.stringify(JSON.parse(sourceLastJson));
      if (canonicalProofJson && canonicalProofJson !== normalized) {
        conflictingProofLog = true;
      } else if (!canonicalProofJson) {
        canonicalProofJson = normalized;
      }
      lastJson = sourceLastJson;
    } catch (err) {
      if (!proofMarkerParseError) {
        proofMarkerParseError = String(err && err.message ? err.message : err);
      }
    }
  }
}

function sameResolvedPath(left, right) {
  return path.resolve(left) === path.resolve(right);
}

function emitSourceRows() {
  emit("mdi_proof_requested_source_count", requestedSourceCount);
  emit("mdi_proof_source_count", sourceCount);
  emit("mdi_proof_marker_source_count", proofMarkerSourceCount);
  emit("mdi_proof_missing_source_count", missingSourceCount);
  emit("mdi_proof_symlink_source_count", symlinkSourceCount);
  emit("mdi_proof_hardlink_source_count", hardlinkSourceCount);
  emit("mdi_proof_duplicate_source_count", duplicateSourceCount);
  emit("mdi_proof_empty_source_count", emptySourceCount);
  emit("mdi_proof_nonregular_source_count", nonregularSourceCount);
  emit("mdi_proof_marker_source_path", proofMarkerSourcePath);
  emit("mdi_proof_marker_source_size_bytes", proofMarkerSourceSizeBytes);
  emit("mdi_proof_marker_source_actual_size_bytes", proofMarkerSourceActualSizeBytes);
  emit("mdi_proof_marker_source_file_status", proofMarkerSourceFileStatus);
  emit("mdi_proof_marker_source_file_reason", proofMarkerSourceFileReason);
}

if (missingSourceCount > 0) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "missing-mdi-proof-source");
  emitSourceRows();
  process.exit(1);
}

if (symlinkSourceCount > 0) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "symlink-mdi-proof-source");
  emitSourceRows();
  process.exit(1);
}

if (hardlinkSourceCount > 0) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "hardlink-mdi-proof-source");
  emitSourceRows();
  process.exit(1);
}

if (nonregularSourceCount > 0) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "nonregular-mdi-proof-source");
  emitSourceRows();
  process.exit(1);
}

if (duplicateSourceCount > 0) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "duplicate-mdi-proof-source");
  emitSourceRows();
  process.exit(1);
}

if (emptySourceCount > 0) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "empty-mdi-proof-source");
  emitSourceRows();
  process.exit(1);
}

if (files.some((file) => sameResolvedPath(jsonPath, file))) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "mdi-proof-json-path-overlaps-source");
  emitSourceRows();
  process.exit(1);
}

if (jsonPathStat && jsonPathStat.isSymbolicLink()) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "mdi-proof-json-path-symlink");
  emitSourceRows();
  process.exit(1);
}

if (jsonPathStat && !jsonPathStat.isFile()) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "mdi-proof-json-path-not-regular");
  emitSourceRows();
  process.exit(1);
}

if (jsonPathStat && sourceFileIdentities.has(fileIdentity(jsonPathStat))) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "mdi-proof-json-path-overlaps-source");
  emitSourceRows();
  process.exit(1);
}

if (jsonPathStat && jsonPathStat.nlink > 1) {
  emit("mdi_proof_json", jsonPath);
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", "mdi-proof-json-path-hardlink");
  emitSourceRows();
  process.exit(1);
}

if (!lastJson) {
  emitSourceRows();
  fail(proofMarkerParseError ? `invalid-mdi-proof-json:${proofMarkerParseError}` : "missing-mdi-proof-log");
}

if (proofMarkerParseError) {
  emitSourceRows();
  fail(`invalid-mdi-proof-json:${proofMarkerParseError}`);
}

if (conflictingProofLog) {
  emitSourceRows();
  fail("conflicting-mdi-proof-log");
}

let proof;
try {
  proof = JSON.parse(lastJson);
} catch (err) {
  fail(`invalid-mdi-proof-json:${String(err && err.message ? err.message : err)}`);
}

fs.writeFileSync(jsonPath, `${JSON.stringify(proof)}\n`);

const eventPass =
  jsonIntegerAtLeast(proof.count, 4) &&
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
  eventSequenceMatches(proof.eventSequence) &&
  jsonIntegerAtLeast(proof.taskbarItemCount, 4) &&
  jsonIntegerAtLeast(proof.taskbarIconCount, 4) &&
  proof.taskbarIconsVisible === true &&
  proof.taskbarLabelsVisible === true;
const renderPass =
  jsonIntegerAtLeast(proof.imageCount, 1) &&
  proof.htmlRenderable === true;

const capturePass =
  jsonIntegerAtLeast(proof.viewportWidth, 300) &&
  jsonIntegerAtLeast(proof.viewportHeight, 300) &&
  jsonDecimalGreaterThan(proof.devicePixelRatio, 0) &&
  orientationText(proof.screenOrientation) !== "";
const performancePass =
  proof.performanceNowAvailable === true &&
  jsonDecimalGreaterThan(proof.performanceNowDeltaMs, 0) &&
  jsonDecimalAtMost(proof.performanceNowDeltaMs, maxEventTimingMs);
const interactionLatencyPass =
  jsonDecimalGreaterThan(proof.inputToPaintMs, 0) &&
  jsonDecimalAtMost(proof.inputToPaintMs, maxEventTimingMs);
const animationPass =
  proof.animationFrameAvailable === true &&
  jsonIntegerAtLeast(proof.animationFrameCount, 2) &&
  proof.cssAnimationProbe === true;
// P1.2: the invoke() native->webview return path must be proven with a real
// returned value (not `eval OK`), so require the deterministic seq*2+1 reply
// the webview actually received back over invoke() to match what the native
// command computed. See invoke_roundtrip_ping/report_invoke_roundtrip in
// tools/tauri-shell/src-tauri/src/lib.rs.
const invokeRoundtripPass = proof.invokeRoundtripStatus === "pass";
const detailPass = eventPass && renderPass && capturePass && performancePass && interactionLatencyPass && animationPass && invokeRoundtripPass;
const status = !failureMarker && detailPass ? "pass" : "fail";
const reason = failureMarker
  ? "mobile-mdi-failure-marker"
  : detailPass
    ? "pass"
    : "contract-missing";

emit("mdi_proof_json", jsonPath);
emit("mdi_proof_status", status);
emit("mdi_proof_reason", reason);
emitSourceRows();
emit("mdi_failure_marker_status", failureMarker ? "fail" : "pass");
emit("mdi_proof_window_count", jsonIntegerTextOrBlank(proof.count));
emit("mdi_render_status", renderPass ? "pass" : "fail");
emit("mdi_render_image_count", jsonIntegerTextOrBlank(proof.imageCount));
emit("mdi_render_html_renderable", jsonBoolTextOrBlank(proof.htmlRenderable));
emit("mdi_event_taskbar_item_count", jsonIntegerTextOrBlank(proof.taskbarItemCount));
emit("mdi_event_taskbar_icon_count", jsonIntegerTextOrBlank(proof.taskbarIconCount));
emit("mdi_event_has_desktop", jsonBoolTextOrBlank(proof.hasDesktop));
emit("mdi_event_drag_runtime_available", jsonBoolTextOrBlank(proof.hasDragRuntime));
emit("mdi_event_drag_events_available", jsonBoolTextOrBlank(proof.hasDragEvents));
emit("mdi_event_drag_moved", jsonBoolTextOrBlank(proof.dragMoved));
emit("mdi_event_window_event_runtime_available", jsonBoolTextOrBlank(proof.hasWindowEventRuntime));
emit("mdi_event_app_action_control_found", jsonBoolTextOrBlank(proof.appActionControlFound));
emit("mdi_event_app_input_control_found", jsonBoolTextOrBlank(proof.appInputControlFound));
emit("mdi_event_body_click_routed", jsonBoolTextOrBlank(proof.bodyClickRouted));
emit("mdi_event_body_input_routed", jsonBoolTextOrBlank(proof.bodyInputRouted));
emit("mdi_event_body_key_routed", jsonBoolTextOrBlank(proof.bodyKeyRouted));
emit("mdi_event_sequence", eventSequenceText(proof.eventSequence));
emit("mdi_event_taskbar_icons_visible", jsonBoolTextOrBlank(proof.taskbarIconsVisible));
emit("mdi_event_taskbar_labels_visible", jsonBoolTextOrBlank(proof.taskbarLabelsVisible));
emit("mdi_event_status", eventPass ? "pass" : "fail");
emit("mdi_capture_status", capturePass ? "pass" : "fail");
emit("mdi_capture_viewport_width", jsonIntegerTextOrBlank(proof.viewportWidth));
emit("mdi_capture_viewport_height", jsonIntegerTextOrBlank(proof.viewportHeight));
emit("mdi_capture_device_pixel_ratio", jsonDecimalTextOrBlank(proof.devicePixelRatio));
emit("mdi_capture_screen_orientation", orientationText(proof.screenOrientation));
emit("mdi_performance_status", performancePass ? "pass" : "fail");
emit("mdi_performance_now_available", jsonBoolTextOrBlank(proof.performanceNowAvailable));
emit("mdi_performance_now_delta_ms", jsonDecimalTextOrBlank(proof.performanceNowDeltaMs));
emit("mdi_interaction_latency_status", interactionLatencyPass ? "pass" : "fail");
emit("mdi_input_to_paint_ms", jsonDecimalTextOrBlank(proof.inputToPaintMs));
emit("mdi_animation_status", animationPass ? "pass" : "fail");
emit("mdi_animation_frame_available", jsonBoolTextOrBlank(proof.animationFrameAvailable));
emit("mdi_animation_frame_count", jsonIntegerTextOrBlank(proof.animationFrameCount));
emit("mdi_css_animation_probe", jsonBoolTextOrBlank(proof.cssAnimationProbe));
emit("mdi_invoke_roundtrip_status", invokeRoundtripPass ? "pass" : "fail");
emit("mdi_invoke_roundtrip_reply", clean(proof.invokeRoundtripReply));

if (status !== "pass") {
  process.exit(1);
}
