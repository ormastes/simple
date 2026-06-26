#!/usr/bin/env node

const fs = require("fs");

const [prefix, jsonPath, ...files] = process.argv.slice(2);

function clean(value) {
  if (value === undefined || value === null) return "";
  return String(value).replace(/[\r\n]/g, " ");
}

function emit(key, value) {
  console.log(`${prefix}_${key}=${clean(value)}`);
}

function jsonIntegerText(value) {
  if (typeof value === "number" && Number.isInteger(value)) return String(value);
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

function jsonIntegerTextOrBlank(value) {
  const text = jsonIntegerText(value);
  return text === null ? "" : text;
}

function jsonDecimalTextOrBlank(value) {
  const text = jsonNumberText(value);
  return text === null ? "" : text;
}

function fail(reason) {
  emit("mdi_proof_status", "fail");
  emit("mdi_proof_reason", reason);
  process.exit(1);
}

if (!prefix || !jsonPath || files.length === 0) {
  fail("usage-prefix-jsonpath-files");
}

let lastJson = "";
for (const file of files) {
  if (!file || !fs.existsSync(file)) continue;
  const text = fs.readFileSync(file, "utf8");
  const matches = [...text.matchAll(/\[tauri-shell\] mdi proof:\s*(\{[^\r\n]*\})/g)];
  if (matches.length > 0) {
    lastJson = matches[matches.length - 1][1];
  }
}

if (!lastJson) {
  fail("missing-mdi-proof-log");
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
  jsonIntegerAtLeast(proof.taskbarItemCount, 4) &&
  jsonIntegerAtLeast(proof.taskbarIconCount, 4) &&
  proof.taskbarIconsVisible === true &&
  proof.taskbarLabelsVisible === true;
const renderPass =
  jsonIntegerAtLeast(proof.imageCount, 1) &&
  proof.htmlRenderable === true;

const capturePass =
  jsonIntegerAtLeast(proof.viewportWidth, 300) &&
  jsonIntegerAtLeast(proof.viewportHeight, 300);
const performancePass =
  proof.performanceNowAvailable === true &&
  jsonDecimalGreaterThan(proof.performanceNowDeltaMs, 0);
const animationPass =
  proof.animationFrameAvailable === true &&
  jsonIntegerAtLeast(proof.animationFrameCount, 2) &&
  proof.cssAnimationProbe === true;

emit("mdi_proof_json", jsonPath);
emit("mdi_proof_status", eventPass && renderPass && capturePass && performancePass && animationPass ? "pass" : "fail");
emit("mdi_proof_reason", eventPass && renderPass && capturePass && performancePass && animationPass ? "pass" : "contract-missing");
emit("mdi_proof_window_count", jsonIntegerTextOrBlank(proof.count));
emit("mdi_render_status", renderPass ? "pass" : "fail");
emit("mdi_render_image_count", jsonIntegerTextOrBlank(proof.imageCount));
emit("mdi_render_html_renderable", proof.htmlRenderable === true ? "true" : "false");
emit("mdi_event_taskbar_item_count", jsonIntegerTextOrBlank(proof.taskbarItemCount));
emit("mdi_event_taskbar_icon_count", jsonIntegerTextOrBlank(proof.taskbarIconCount));
emit("mdi_event_status", eventPass ? "pass" : "fail");
emit("mdi_capture_status", capturePass ? "pass" : "fail");
emit("mdi_capture_viewport_width", jsonIntegerTextOrBlank(proof.viewportWidth));
emit("mdi_capture_viewport_height", jsonIntegerTextOrBlank(proof.viewportHeight));
emit("mdi_performance_status", performancePass ? "pass" : "fail");
emit("mdi_performance_now_available", proof.performanceNowAvailable === true ? "true" : "false");
emit("mdi_performance_now_delta_ms", jsonDecimalTextOrBlank(proof.performanceNowDeltaMs));
emit("mdi_animation_status", animationPass ? "pass" : "fail");
emit("mdi_animation_frame_available", proof.animationFrameAvailable === true ? "true" : "false");
emit("mdi_animation_frame_count", jsonIntegerTextOrBlank(proof.animationFrameCount));
emit("mdi_css_animation_probe", proof.cssAnimationProbe === true ? "true" : "false");

if (!(eventPass && renderPass && capturePass && performancePass && animationPass)) {
  process.exit(1);
}
