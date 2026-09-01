#!/usr/bin/env node
"use strict";

// Join independently captured production facts into the fail-closed evidence
// envelope consumed by check-aetheric-host-web-gui-evidence.shs.  This module
// does not render HTML, manufacture pixels, or simulate events.

const crypto = require("crypto");
const fs = require("fs");
const path = require("path");
const {
  resolveElectronIdentity,
} = require("./aetheric_electron_identity");

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

function accessResult(file, operation, requiredText) {
  const raw = fs.readFileSync(file, "utf8");
  return {
    raw,
    pass:
      raw.includes('"schema":"simple.access/v1"') &&
      raw.includes(`"operation":"${operation}"`) &&
      (operation !== "act" || raw.includes('"ok":true')) &&
      (!requiredText || raw.includes(requiredText)),
  };
}

function snapshotRevision(raw) {
  const match = raw.match(/"snapshot_revision":([0-9]+)/);
  return match ? Number(match[1]) : -1;
}

function accessAction(file, revisionFile, canonicalId, action) {
  const result = accessResult(file, "act", canonicalId);
  const revisionResult = accessResult(revisionFile, "snapshot", "");
  const expectedRevision = snapshotRevision(revisionResult.raw);
  const requestId = result.raw.match(/"request_id":"([^"]+)"/);
  return {
    ...result,
    expectedRevision,
    requestId: requestId ? requestId[1] : "",
    revisionPass:
      revisionResult.pass &&
      expectedRevision >= 0 &&
      result.raw.includes(`"action":"${action}"`) &&
      result.raw.includes(`"expected_revision":${expectedRevision}`) &&
      result.raw.includes(`"applied_revision":${expectedRevision + 2}`) &&
      Boolean(requestId && requestId[1]),
  };
}

function main() {
  const sourceLogPath = required("--source-log");
  const htmlPath = required("--html");
  const simplePixelsPath = required("--simple-pixels");
  const electronPixelsPath = required("--electron-pixels");
  const observationPath = required("--observation");
  const screenshotPath = required("--screenshot");
  const binaryPath = required("--binary");
  const generatorBinaryPath = required("--generator-binary");
  const rendererBinaryPath = required("--renderer-binary");
  const uiDriverBinaryPath = required("--ui-driver-binary");
  const providerProvenancePath = required("--provider-provenance");
  const rendererWmProviderPath = required("--renderer-wm-provider");
  const rendererCWmProviderPath = required("--renderer-c-wm-provider");
  const uiSqliteProviderPath = required("--ui-sqlite-provider");
  const uiSqliteSystemProviderPath = required("--ui-sqlite-system-provider");
  const electronIdentity = resolveElectronIdentity({
    root: process.cwd(),
    launcher: required("--electron-launcher"),
    appExecutable: required("--electron-app-executable"),
    package: required("--electron-package"),
    lock: required("--electron-lock"),
  });
  const revision = required("--revision");
  const uiAccessDir = required("--ui-access-dir");
  const outputPath = required("--output");
  const sourceLog = fs.readFileSync(sourceLogPath, "utf8");
  const simplePixels = readJson(simplePixelsPath);
  const electronPixels = readJson(electronPixelsPath);
  const observation = readJson(observationPath);
  const events = electronPixels.event_proof || {};
  const renderedPixelCount = Array.isArray(simplePixels.pixels) ? simplePixels.pixels.length : 0;
  const electronNonblank = nonblankArgb(electronPixels.pixels);
  const providerFactsPass = [
    providerProvenancePath,
    rendererWmProviderPath,
    rendererCWmProviderPath,
    uiSqliteProviderPath,
    uiSqliteSystemProviderPath,
  ].every(providerPath => fs.statSync(providerPath).isFile() && fs.statSync(providerPath).size > 0);
  const generated = line(sourceLog, "aetheric_host_web_gui_generation_status") === "pass";
  const sourceProducer = line(sourceLog, "aetheric_host_web_gui_generation_producer");
  const sourceSynthetic = line(sourceLog, "aetheric_host_web_gui_generation_synthetic_fixture");
  const sourceRawExecution = line(sourceLog, "aetheric_host_web_gui_generation_raw_source_execution");
  const simpleProducer = value(simplePixels, "producer");
  const requestedBackend = value(simplePixels, "requested_backend");
  const resolvedBackend = value(simplePixels, "resolved_backend");
  const readbackSource = value(simplePixels, "engine2d_readback_source");
  const compatibilityRenderer = simpleProducer.includes("compatibility") || simpleProducer.includes("native-safe");
  const dimensionsMatch =
    Number(simplePixels.width) > 0 &&
    Number(simplePixels.height) > 0 &&
    Number(simplePixels.width) === Number(electronPixels.width) &&
    Number(simplePixels.height) === Number(electronPixels.height);
  const uiPaths = {
    snapshot: path.join(uiAccessDir, "snapshot.json"),
    surface: path.join(uiAccessDir, "surface.json"),
    find: path.join(uiAccessDir, "find.json"),
    focus: path.join(uiAccessDir, "act-focus.json"),
    focusRevision: path.join(uiAccessDir, "act-focus-revision.json"),
    pointerDown: path.join(uiAccessDir, "act-pointer-down.json"),
    pointerDownRevision: path.join(uiAccessDir, "act-pointer-down-revision.json"),
    pointerUp: path.join(uiAccessDir, "act-pointer-up.json"),
    pointerUpRevision: path.join(uiAccessDir, "act-pointer-up-revision.json"),
    keyboard: path.join(uiAccessDir, "act-keyboard.json"),
    keyboardRevision: path.join(uiAccessDir, "act-keyboard-revision.json"),
    text: path.join(uiAccessDir, "act-text.json"),
    textRevision: path.join(uiAccessDir, "act-text-revision.json"),
    postAction: path.join(uiAccessDir, "post-action.json"),
    history: path.join(uiAccessDir, "history.json"),
  };
  const ui = {
    snapshot: accessResult(uiPaths.snapshot, "snapshot", "main#theme-name"),
    surface: accessResult(uiPaths.surface, "surface", "Aetheric Production Web GUI"),
    find: accessResult(uiPaths.find, "find", "main#apply-theme"),
    focus: accessAction(uiPaths.focus, uiPaths.focusRevision, "main#theme-name", "focus"),
    pointerDown: accessAction(uiPaths.pointerDown, uiPaths.pointerDownRevision, "main#apply-theme", "pointer_down"),
    pointerUp: accessAction(uiPaths.pointerUp, uiPaths.pointerUpRevision, "main#apply-theme", "pointer_up"),
    keyboard: accessAction(uiPaths.keyboard, uiPaths.keyboardRevision, "main#theme-name", "keyboard_x"),
    text: accessAction(uiPaths.text, uiPaths.textRevision, "main#theme-name", "text_x"),
    postAction: accessResult(uiPaths.postAction, "find", "Aetheric DarkX"),
    history: accessResult(uiPaths.history, "history", "access_result"),
  };
  const postActionPass = ui.postAction.pass && ui.postAction.raw.includes('"focused":true');
  const revisions = [ui.focus, ui.pointerDown, ui.pointerUp, ui.keyboard, ui.text].map(item => item.expectedRevision);
  const revisionPass =
    [ui.focus, ui.pointerDown, ui.pointerUp, ui.keyboard, ui.text].every(item => item.revisionPass) &&
    revisions.every((revision, index) => index === 0 || revision > revisions[index - 1]);
  const historyPass =
    ui.history.pass &&
    ["focus", "pointer_down", "pointer_up", "keyboard_x", "text_x"].every(action => ui.history.raw.includes(action)) &&
    ui.history.raw.includes("main#theme-name") &&
    ui.history.raw.includes("main#apply-theme") &&
    ui.history.raw.includes("access_request") &&
    ui.history.raw.includes("access_result") &&
    [ui.focus, ui.pointerDown, ui.pointerUp, ui.keyboard, ui.text].every(item =>
      item.requestId !== "" && ui.history.raw.includes(`request_id=${item.requestId};code=`));
  const uiAccessPass =
    ui.snapshot.pass && ui.surface.pass && ui.find.pass && ui.focus.pass &&
    ui.pointerDown.pass && ui.pointerUp.pass && ui.keyboard.pass && ui.text.pass &&
    revisionPass && postActionPass && historyPass;
  const productionFactsPass = generated &&
    sourceProducer === "simple_web_content_render_request_with_theme" &&
    sourceSynthetic === "false" &&
    sourceRawExecution === "false" &&
    (fs.statSync(generatorBinaryPath).mode & 0o111) !== 0 &&
    (fs.statSync(rendererBinaryPath).mode & 0o111) !== 0 &&
    (fs.statSync(uiDriverBinaryPath).mode & 0o111) !== 0 &&
    fs.statSync(htmlPath).size > 0 &&
    String(simplePixels.format || "") === "argb-u32" &&
    simpleProducer.startsWith("simple-web-core-renderer-") &&
    requestedBackend === "cpu_simd" &&
    resolvedBackend === "cpu_simd" &&
    readbackSource === "cpu_mirror" &&
    !compatibilityRenderer &&
    renderedPixelCount > 0 &&
    dimensionsMatch &&
    String(electronPixels.producer || "") === "electron-chromium-capture" &&
    electronPixels.blur_or_tolerance_used === false &&
    String(events.status || "") === "pass" &&
    String(observation.status || "") === "pass" &&
    value(observation, "electron_process_version") === "42.5.0" &&
    /^[0-9]+(?:\.[0-9]+)*$/.test(value(observation, "chrome_process_version")) &&
    electronIdentity.version === "42.5.0" &&
    electronNonblank > 0 &&
    fs.statSync(screenshotPath).size > 0;

  const admitted = productionFactsPass && providerFactsPass && uiAccessPass;
  const fields = {
    schema: "aetheric-host-web-gui-v1",
    status: admitted ? "pass" : "fail",
    reason: admitted ? "pass" :
      (!productionFactsPass ? "production-capture-failed" :
        (!providerFactsPass ? "native-provider-provenance-failed" : "canonical-ui-access-failed")),
    producer: productionFactsPass ? "production-html-webir-drawir-electron" : "production-provenance-rejected",
    theme_id: line(sourceLog, "aetheric_host_web_gui_generation_theme_id"),
    theme_source_manifest_sha256: line(sourceLog, "aetheric_host_web_gui_generation_theme_manifest_sha256"),
    theme_material_sha256: line(sourceLog, "aetheric_host_web_gui_generation_theme_material_sha256"),
    source_revision: revision,
    binary_sha256: sha256(binaryPath),
    generator_binary_path: generatorBinaryPath,
    generator_binary_sha256: sha256(generatorBinaryPath),
    renderer_binary_path: rendererBinaryPath,
    renderer_binary_sha256: sha256(rendererBinaryPath),
    ui_driver_binary_path: uiDriverBinaryPath,
    ui_driver_binary_sha256: sha256(uiDriverBinaryPath),
    provider_provenance_path: providerProvenancePath,
    provider_provenance_sha256: sha256(providerProvenancePath),
    renderer_wm_provider_path: rendererWmProviderPath,
    renderer_wm_provider_sha256: sha256(rendererWmProviderPath),
    renderer_c_wm_provider_path: rendererCWmProviderPath,
    renderer_c_wm_provider_sha256: sha256(rendererCWmProviderPath),
    ui_sqlite_provider_path: uiSqliteProviderPath,
    ui_sqlite_provider_sha256: sha256(uiSqliteProviderPath),
    ui_sqlite_system_provider_path: uiSqliteSystemProviderPath,
    ui_sqlite_system_provider_sha256: sha256(uiSqliteSystemProviderPath),
    source_log_path: sourceLogPath,
    source_log_sha256: sha256(sourceLogPath),
    html_path: htmlPath,
    html_sha256: sha256(htmlPath),
    observation_path: observationPath,
    observation_sha256: sha256(observationPath),
    electron_process_version: value(observation, "electron_process_version"),
    chrome_process_version: value(observation, "chrome_process_version"),
    electron_launcher_path: electronIdentity.launcherPath,
    electron_launcher_sha256: electronIdentity.launcherSha256,
    electron_app_executable_path: electronIdentity.appExecutablePath,
    electron_app_executable_sha256: electronIdentity.appExecutableSha256,
    electron_package_path: electronIdentity.packagePath,
    electron_package_sha256: electronIdentity.packageSha256,
    electron_lock_path: electronIdentity.lockPath,
    electron_lock_sha256: electronIdentity.lockSha256,
    backend: resolvedBackend,
    simple_renderer_producer: simpleProducer,
    simple_requested_backend: requestedBackend,
    simple_resolved_backend: resolvedBackend,
    simple_readback_source: readbackSource,
    simple_width: value(simplePixels, "width"),
    simple_height: value(simplePixels, "height"),
    electron_producer: value(electronPixels, "producer"),
    electron_width: value(electronPixels, "width"),
    electron_height: value(electronPixels, "height"),
    capture_path: electronPixelsPath,
    capture_sha256: sha256(electronPixelsPath),
    pixel_artifact_path: simplePixelsPath,
    pixel_artifact_sha256: sha256(simplePixelsPath),
    pixel_count: String(renderedPixelCount),
    pixel_checksum: sha256(simplePixelsPath),
    screenshot_path: screenshotPath,
    screenshot_sha256: sha256(screenshotPath),
    screenshot_nonblank_pixels: String(electronNonblank),
    ui_access_snapshot_status: ui.snapshot.pass ? "pass" : "fail",
    ui_access_surface_status: ui.surface.pass ? "pass" : "fail",
    ui_access_find_status: ui.find.pass ? "pass" : "fail",
    ui_access_act_focus_status: ui.focus.pass && ui.focus.revisionPass ? "pass" : "fail",
    ui_access_act_pointer_down_status: ui.pointerDown.pass && ui.pointerDown.revisionPass ? "pass" : "fail",
    ui_access_act_pointer_up_status: ui.pointerUp.pass && ui.pointerUp.revisionPass ? "pass" : "fail",
    ui_access_act_keyboard_status: ui.keyboard.pass && ui.keyboard.revisionPass ? "pass" : "fail",
    ui_access_act_text_status: ui.text.pass && ui.text.revisionPass ? "pass" : "fail",
    ui_access_history_status: historyPass ? "pass" : "fail",
    ui_access_revision_status: revisionPass ? "pass" : "fail",
    ui_access_snapshot_path: uiPaths.snapshot,
    ui_access_snapshot_sha256: sha256(uiPaths.snapshot),
    ui_access_surface_path: uiPaths.surface,
    ui_access_surface_sha256: sha256(uiPaths.surface),
    ui_access_find_path: uiPaths.find,
    ui_access_find_sha256: sha256(uiPaths.find),
    ui_access_act_focus_path: uiPaths.focus,
    ui_access_act_focus_sha256: sha256(uiPaths.focus),
    ui_access_act_focus_revision_path: uiPaths.focusRevision,
    ui_access_act_focus_revision_sha256: sha256(uiPaths.focusRevision),
    ui_access_act_pointer_down_path: uiPaths.pointerDown,
    ui_access_act_pointer_down_sha256: sha256(uiPaths.pointerDown),
    ui_access_act_pointer_down_revision_path: uiPaths.pointerDownRevision,
    ui_access_act_pointer_down_revision_sha256: sha256(uiPaths.pointerDownRevision),
    ui_access_act_pointer_up_path: uiPaths.pointerUp,
    ui_access_act_pointer_up_sha256: sha256(uiPaths.pointerUp),
    ui_access_act_pointer_up_revision_path: uiPaths.pointerUpRevision,
    ui_access_act_pointer_up_revision_sha256: sha256(uiPaths.pointerUpRevision),
    ui_access_act_keyboard_path: uiPaths.keyboard,
    ui_access_act_keyboard_sha256: sha256(uiPaths.keyboard),
    ui_access_act_keyboard_revision_path: uiPaths.keyboardRevision,
    ui_access_act_keyboard_revision_sha256: sha256(uiPaths.keyboardRevision),
    ui_access_act_text_path: uiPaths.text,
    ui_access_act_text_sha256: sha256(uiPaths.text),
    ui_access_act_text_revision_path: uiPaths.textRevision,
    ui_access_act_text_revision_sha256: sha256(uiPaths.textRevision),
    ui_access_post_action_path: uiPaths.postAction,
    ui_access_post_action_sha256: sha256(uiPaths.postAction),
    ui_access_history_path: uiPaths.history,
    ui_access_history_sha256: sha256(uiPaths.history),
    post_action_semantic_state: postActionPass ? "text-mutated-and-focused" : "post-action-state-missing",
    computed_window_background: value(observation, "computed_window_background"),
    computed_window_border_color: value(observation, "computed_window_border_color"),
    computed_window_border_radius: value(observation, "computed_window_border_radius"),
    computed_window_box_shadow: value(observation, "computed_window_box_shadow"),
    computed_titlebar_backdrop_filter: value(observation, "computed_titlebar_backdrop_filter"),
    computed_titlebar_webkit_backdrop_filter: value(observation, "computed_titlebar_webkit_backdrop_filter"),
    computed_typography_family: value(observation, "computed_typography_family"),
    computed_typography_weight: value(observation, "computed_typography_weight"),
    computed_inactive_border: value(observation, "computed_inactive_border"),
    computed_inactive_shadow: value(observation, "computed_inactive_shadow"),
    computed_active_border: value(observation, "computed_active_border"),
    computed_active_shadow: value(observation, "computed_active_shadow"),
    computed_button_transition_duration: value(observation, "computed_button_transition_duration"),
    performance_now_available: value(observation, "performance_now_available"),
    performance_now_delta_ms: value(observation, "performance_now_delta_ms"),
    animation_frame_available: value(observation, "animation_frame_available"),
    animation_frame_count: value(observation, "animation_frame_count"),
    css_animation_probe: value(observation, "css_animation_probe"),
    blur_or_tolerance_used: value(electronPixels, "blur_or_tolerance_used"),
    synthetic_fixture: sourceSynthetic,
    raw_source_execution: sourceRawExecution,
    compatibility_renderer: compatibilityRenderer ? "true" : "false",
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
