#!/usr/bin/env node
"use strict";

// Join independently captured production facts into the fail-closed evidence
// envelope consumed by check-aetheric-host-web-gui-evidence.shs.  This module
// does not render HTML, manufacture pixels, or simulate events.

const crypto = require("crypto");
const fs = require("fs");
const path = require("path");

function option(name) {
  const index = process.argv.indexOf(name);
  return index >= 0 ? String(process.argv[index + 1] || "") : "";
}

function required(name) {
  const value = option(name);
  if (!value) throw new Error(`missing-${name}`);
  return value;
}

function sha256(file) {
  return crypto.createHash("sha256").update(fs.readFileSync(file)).digest("hex");
}

function readJson(file) {
  return JSON.parse(fs.readFileSync(file, "utf8"));
}

function line(log, key) {
  const match = log.match(new RegExp(`^${key}=([^\\r\\n]*)$`, "m"));
  return match ? match[1] : "";
}

function nonblankArgb(pixels) {
  return Array.isArray(pixels) ? pixels.reduce((count, pixel) => count + ((Number(pixel) >>> 24) !== 0 ? 1 : 0), 0) : 0;
}

function value(object, key) {
  const result = object && object[key];
  return result === undefined || result === null ? "" : String(result);
}

function main() {
  const sourceLogPath = required("--source-log");
  const simplePixelsPath = required("--simple-pixels");
  const electronPixelsPath = required("--electron-pixels");
  const observationPath = required("--observation");
  const screenshotPath = required("--screenshot");
  const binaryPath = required("--binary");
  const revision = required("--revision");
  const outputPath = required("--output");
  const sourceLog = fs.readFileSync(sourceLogPath, "utf8");
  const simplePixels = readJson(simplePixelsPath);
  const electronPixels = readJson(electronPixelsPath);
  const observation = readJson(observationPath);
  const events = electronPixels.event_proof || {};
  const renderedPixelCount = Array.isArray(simplePixels.pixels) ? simplePixels.pixels.length : 0;
  const electronNonblank = nonblankArgb(electronPixels.pixels);
  const generated = line(sourceLog, "aetheric_host_web_gui_generation_status") === "pass";
  const productionFactsPass = generated &&
    String(simplePixels.format || "") === "argb-u32" &&
    renderedPixelCount > 0 &&
    String(events.status || "") === "pass" &&
    String(observation.status || "") === "pass" &&
    electronNonblank > 0 &&
    fs.statSync(screenshotPath).size > 0;

  // The canonical Simple UI-access service currently observes UISession-backed
  // Electron applications, but the standalone Chromium capture surface has no
  // registered adapter.  Do not map the DOM to an invented, second UI state.
  const uiAccessGap = "electron-capture-surface-not-registered-with-canonical-ui-access";
  const fields = {
    schema: "aetheric-host-web-gui-v1",
    status: productionFactsPass ? "fail" : "fail",
    reason: productionFactsPass ? "ui-access-abi-gap" : "production-capture-failed",
    producer: "production-html-webir-drawir-electron",
    theme_id: line(sourceLog, "aetheric_host_web_gui_generation_theme_id"),
    theme_source_manifest_sha256: line(sourceLog, "aetheric_host_web_gui_generation_theme_manifest_sha256"),
    theme_material_sha256: line(sourceLog, "aetheric_host_web_gui_generation_theme_material_sha256"),
    source_revision: revision,
    binary_sha256: sha256(binaryPath),
    backend: "engine2d",
    capture_path: electronPixelsPath,
    capture_sha256: sha256(electronPixelsPath),
    pixel_artifact_path: simplePixelsPath,
    pixel_artifact_sha256: sha256(simplePixelsPath),
    pixel_count: String(renderedPixelCount),
    pixel_checksum: sha256(simplePixelsPath),
    screenshot_path: screenshotPath,
    screenshot_sha256: sha256(screenshotPath),
    screenshot_nonblank_pixels: String(electronNonblank),
    ui_access_snapshot_status: "blocked",
    ui_access_surface_status: "blocked",
    ui_access_find_status: "blocked",
    ui_access_act_focus_status: "blocked",
    ui_access_act_pointer_down_status: "blocked",
    ui_access_act_pointer_up_status: "blocked",
    ui_access_act_keyboard_status: "blocked",
    ui_access_act_text_status: "blocked",
    ui_access_history_status: "blocked",
    ui_access_abi_gap: uiAccessGap,
    post_action_semantic_state: "electron-dom-text-mutated-and-focused-ui-access-unavailable",
    computed_window_background: value(observation, "computed_window_background"),
    computed_window_border_color: value(observation, "computed_window_border_color"),
    computed_window_border_radius: value(observation, "computed_window_border_radius"),
    computed_window_box_shadow: value(observation, "computed_window_box_shadow"),
    computed_titlebar_backdrop_filter: value(observation, "computed_titlebar_backdrop_filter"),
    computed_titlebar_webkit_backdrop_filter: value(observation, "computed_titlebar_webkit_backdrop_filter"),
    computed_typography_family: value(observation, "computed_typography_family"),
    computed_typography_weight: value(observation, "computed_typography_weight"),
    computed_inactive_border: value(observation, "computed_inactive_border"),
    computed_active_border: value(observation, "computed_active_border"),
    computed_active_shadow: value(observation, "computed_active_shadow"),
    performance_now_available: value(observation, "performance_now_available"),
    performance_now_delta_ms: value(observation, "performance_now_delta_ms"),
    animation_frame_available: value(observation, "animation_frame_available"),
    animation_frame_count: value(observation, "animation_frame_count"),
    css_animation_probe: value(observation, "css_animation_probe"),
    blur_or_tolerance_used: "false",
    synthetic_fixture: "false",
    raw_source_execution: "false",
    compatibility_renderer: "false",
    electron_event_status: value(events, "status"),
    electron_focus_event_count: value(events, "focus_count"),
    electron_keyboard_event_count: value(events, "keyboard_count"),
    electron_input_event_count: value(events, "input_count"),
    electron_pointer_down_event_count: value(events, "pointer_down_count"),
    electron_pointer_up_event_count: value(events, "pointer_up_count"),
    electron_click_event_count: value(events, "click_count"),
    production_facts_status: productionFactsPass ? "pass" : "fail"
  };
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, Object.entries(fields).map(([key, val]) => `${key}=${String(val).replace(/[\\r\\n]/g, " ")}`).join("\n") + "\n");
  console.log(`aetheric_host_web_gui_proof=${outputPath}`);
  console.log(`aetheric_host_web_gui_production_facts=${fields.production_facts_status}`);
  console.log(`aetheric_host_web_gui_status=${fields.status}`);
  console.log(`aetheric_host_web_gui_reason=${fields.reason}`);
}

try {
  main();
} catch (error) {
  console.error(`write-aetheric-host-web-gui-proof: ${error && error.message ? error.message : error}`);
  process.exit(2);
}
