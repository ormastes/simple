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

function decimalIntegerText(value) {
  if (typeof value === "number" && Number.isInteger(value)) return String(value);
  if (typeof value === "bigint") return value.toString();
  if (typeof value === "string" && /^-?[0-9]+$/.test(value.trim())) return value.trim();
  return null;
}

function decimalNumberText(value) {
  if (typeof value === "number" && Number.isFinite(value)) return String(value);
  if (typeof value === "string" && /^-?(?:[0-9]+)(?:\.[0-9]+)?$/.test(value.trim())) return value.trim();
  return null;
}

function integerAtLeast(value, min) {
  const text = decimalIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(min);
}

function decimalAtLeast(value, min) {
  const text = decimalNumberText(value);
  if (text === null) return false;
  return Number(text) >= min;
}

function integerTextOrBlank(value) {
  const text = decimalIntegerText(value);
  return text === null ? "" : text;
}

function decimalTextOrBlank(value) {
  const text = decimalNumberText(value);
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
  integerAtLeast(proof.taskbarItemCount, 4) &&
  integerAtLeast(proof.taskbarIconCount, 4) &&
  proof.taskbarIconsVisible === true &&
  proof.taskbarLabelsVisible === true &&
  proof.htmlRenderable === true;

const capturePass =
  integerAtLeast(proof.viewportWidth, 300) &&
  integerAtLeast(proof.viewportHeight, 300);
const performancePass =
  proof.performanceNowAvailable === true &&
  decimalAtLeast(proof.performanceNowDeltaMs, 0);
const animationPass =
  proof.animationFrameAvailable === true &&
  integerAtLeast(proof.animationFrameCount, 2) &&
  proof.cssAnimationProbe === true;

emit("mdi_proof_json", jsonPath);
emit("mdi_proof_status", eventPass && capturePass && performancePass && animationPass ? "pass" : "fail");
emit("mdi_proof_reason", eventPass && capturePass && performancePass && animationPass ? "pass" : "contract-missing");
emit("mdi_proof_window_count", integerTextOrBlank(proof.count));
emit("mdi_event_status", eventPass ? "pass" : "fail");
emit("mdi_capture_status", capturePass ? "pass" : "fail");
emit("mdi_capture_viewport_width", integerTextOrBlank(proof.viewportWidth));
emit("mdi_capture_viewport_height", integerTextOrBlank(proof.viewportHeight));
emit("mdi_performance_status", performancePass ? "pass" : "fail");
emit("mdi_performance_now_delta_ms", decimalTextOrBlank(proof.performanceNowDeltaMs));
emit("mdi_animation_status", animationPass ? "pass" : "fail");
emit("mdi_animation_frame_count", integerTextOrBlank(proof.animationFrameCount));
emit("mdi_css_animation_probe", proof.cssAnimationProbe === true ? "true" : "false");

if (!(eventPass && capturePass && performancePass && animationPass)) {
  process.exit(1);
}
