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

const count = Number(proof.count || 0);
const taskbarItemCount = Number(proof.taskbarItemCount || 0);
const taskbarIconCount = Number(proof.taskbarIconCount || 0);
const viewportWidth = Number(proof.viewportWidth);
const viewportHeight = Number(proof.viewportHeight);
const performanceNowDeltaMs = Number(proof.performanceNowDeltaMs);
const animationFrameCount = Number(proof.animationFrameCount);

const eventPass =
  count >= 4 &&
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
  taskbarItemCount >= 4 &&
  taskbarIconCount >= 4 &&
  proof.taskbarIconsVisible === true &&
  proof.taskbarLabelsVisible === true &&
  proof.htmlRenderable === true;

const capturePass =
  Number.isFinite(viewportWidth) &&
  Number.isFinite(viewportHeight) &&
  viewportWidth >= 300 &&
  viewportHeight >= 300;
const performancePass =
  proof.performanceNowAvailable === true &&
  Number.isFinite(performanceNowDeltaMs) &&
  performanceNowDeltaMs >= 0;
const animationPass =
  proof.animationFrameAvailable === true &&
  Number.isFinite(animationFrameCount) &&
  animationFrameCount >= 2 &&
  proof.cssAnimationProbe === true;

emit("mdi_proof_json", jsonPath);
emit("mdi_proof_status", eventPass && capturePass && performancePass && animationPass ? "pass" : "fail");
emit("mdi_proof_reason", eventPass && capturePass && performancePass && animationPass ? "pass" : "contract-missing");
emit("mdi_proof_window_count", count);
emit("mdi_event_status", eventPass ? "pass" : "fail");
emit("mdi_capture_status", capturePass ? "pass" : "fail");
emit("mdi_capture_viewport_width", Number.isFinite(viewportWidth) ? viewportWidth : "");
emit("mdi_capture_viewport_height", Number.isFinite(viewportHeight) ? viewportHeight : "");
emit("mdi_performance_status", performancePass ? "pass" : "fail");
emit("mdi_performance_now_delta_ms", Number.isFinite(performanceNowDeltaMs) ? performanceNowDeltaMs : "");
emit("mdi_animation_status", animationPass ? "pass" : "fail");
emit("mdi_animation_frame_count", Number.isFinite(animationFrameCount) ? animationFrameCount : "");
emit("mdi_css_animation_probe", proof.cssAnimationProbe === true ? "true" : "false");

if (!(eventPass && capturePass && performancePass && animationPass)) {
  process.exit(1);
}
