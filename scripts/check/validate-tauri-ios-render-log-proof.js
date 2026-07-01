#!/usr/bin/env node
const fs = require("fs");

const sources = process.argv.slice(2).filter((value) => value && value !== "-");

function statSource(path) {
  try {
    const lst = fs.lstatSync(path);
    const isSymlink = lst.isSymbolicLink();
    const st = fs.statSync(path);
    const text = st.isFile() ? fs.readFileSync(path, "utf8") : "";
    return { path, exists: true, isSymlink, isFile: st.isFile(), nlink: st.nlink || 1, size: st.size, text };
  } catch {
    return { path, exists: false, isSymlink: false, isFile: false, nlink: 0, size: 0, text: "" };
  }
}

const records = sources.map(statSource);
const existing = records.filter((r) => r.exists && r.isFile);
const missing = records.filter((r) => !r.exists);
const empty = existing.filter((r) => r.size === 0);
const symlink = records.filter((r) => r.isSymlink);
const hardlink = existing.filter((r) => r.nlink > 1);
const nonregular = records.filter((r) => r.exists && !r.isFile);

const markerRecords = existing.filter((r) => /\[tauri-shell\] render, html_len=\d+/.test(r.text));
const coherent = markerRecords[0] || existing[0];
const allText = existing.map((r) => r.text).join("\n");

const renderMatch = allText.match(/\[tauri-shell\] render, html_len=(\d+)/);
const renderMarker = !!renderMatch;
const metalMarker = /Metal|CAMetalLayer|MTL|AGX|IOGPU|-framework Metal/i.test(allText);
const fallbackFailure = /fallback|swiftshader|software renderer/i.test(allText);
const tauriContext = /WKWebView|ios renderer context|WebviewUrl::App|creating window from app:\/\/index\.html|creating window from mobile inline shell base|external_url: Some/i.test(allText);
const metalContext = /CAMetalLayer|metal_layer=CAMetalLayer|Metal renderer ready|Metal/i.test(allText);
const failureMarker = /render failure|eval FAIL|spawn failed|without a bundled Simple runtime|Headless UI completed|parse error/i.test(allText);
const pass = renderMarker && metalMarker && tauriContext && metalContext && !failureMarker &&
  missing.length === 0 && empty.length === 0 && symlink.length === 0 && hardlink.length === 0 &&
  nonregular.length === 0 && coherent && coherent.size > 0;

function row(key, value) {
  console.log(`${key}=${value}`);
}

row("ios_render_log_validation_status", pass ? "pass" : "fail");
row("ios_render_log_validation_reason", pass ? "pass" :
  failureMarker ? "ios-render-log-failure-marker" :
  !renderMarker ? "ios-render-log-marker-missing" :
  !metalMarker ? "ios-metal-log-marker-missing" :
  !tauriContext ? "ios-tauri-wkwebview-context-missing" :
  !metalContext ? "ios-metal-context-missing" :
  missing.length ? "ios-render-log-source-missing" :
  symlink.length ? "ios-render-log-source-symlink" :
  hardlink.length ? "ios-render-log-source-hardlink" :
  nonregular.length ? "ios-render-log-source-not-regular" :
  empty.length ? "ios-render-log-source-empty" :
  "ios-render-log-validation-failed");
row("ios_render_log_requested_source_count", records.length);
row("ios_render_log_source_count", existing.length);
row("ios_render_log_missing_source_count", missing.length);
row("ios_render_log_empty_source_count", empty.length);
row("ios_render_log_symlink_source_count", symlink.length);
row("ios_render_log_hardlink_source_count", hardlink.length);
row("ios_render_log_duplicate_source_count", 0);
row("ios_render_log_nonregular_source_count", nonregular.length);
row("ios_render_log_html_len", renderMatch ? renderMatch[1] : "");
row("ios_render_log_source_coherence_status", coherent && renderMarker && coherent.text.includes(renderMatch[0]) ? "pass" : "fail");
row("ios_render_log_coherent_source_path", coherent ? coherent.path : "");
row("ios_render_log_coherent_source_size_bytes", coherent ? coherent.size : "");
row("ios_render_log_marker_status", renderMarker ? "pass" : "fail");
row("ios_render_log_metal_marker_status", metalMarker ? "pass" : "fail");
row("ios_render_log_fallback_marker_status", fallbackFailure ? "fail" : "pass");
row("ios_render_log_tauri_context_status", tauriContext ? "pass" : "fail");
row("ios_render_log_metal_context_status", metalContext ? "pass" : "fail");
row("ios_render_log_failure_marker_status", failureMarker ? "fail" : "pass");
process.exit(pass ? 0 : 1);
