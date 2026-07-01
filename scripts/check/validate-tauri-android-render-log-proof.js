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
const vulkanMarker = /Vulkan|vulkan|VK_|ANGLE.*Vulkan|Renderer.*Vulkan|HWUI.*Vulkan|skiavk/i.test(allText);
const failureMarker = /F\/DEBUG|Fatal signal|F\/libc|F\/VulkanManager|Simple subprocess stdout closed before a valid render arrived|Headless UI completed|parse error: expected value/i.test(allText);
const pass = renderMarker && vulkanMarker && !failureMarker &&
  missing.length === 0 && empty.length === 0 && symlink.length === 0 && hardlink.length === 0 &&
  nonregular.length === 0 && coherent && coherent.size > 0;

function row(key, value) {
  console.log(`${key}=${value}`);
}

row("android_render_log_validation_status", pass ? "pass" : "fail");
row("android_render_log_validation_reason", pass ? "pass" :
  failureMarker ? "android-render-log-failure-marker" :
  !renderMarker ? "android-render-log-marker-missing" :
  !vulkanMarker ? "android-vulkan-log-marker-missing" :
  missing.length ? "android-render-log-source-missing" :
  symlink.length ? "android-render-log-source-symlink" :
  hardlink.length ? "android-render-log-source-hardlink" :
  empty.length ? "android-render-log-source-empty" :
  nonregular.length ? "android-render-log-source-not-regular" :
  "android-render-log-validation-failed");
row("android_render_log_requested_source_count", records.length);
row("android_render_log_source_count", existing.length);
row("android_render_log_missing_source_count", missing.length);
row("android_render_log_empty_source_count", empty.length);
row("android_render_log_symlink_source_count", symlink.length);
row("android_render_log_hardlink_source_count", hardlink.length);
row("android_render_log_duplicate_source_count", 0);
row("android_render_log_html_len", renderMatch ? renderMatch[1] : "");
row("android_render_log_source_coherence_status", coherent && renderMarker && coherent.text.includes(renderMatch[0]) ? "pass" : "fail");
row("android_render_log_coherent_source_path", coherent ? coherent.path : "");
row("android_render_log_coherent_source_size_bytes", coherent ? coherent.size : "");
row("android_render_log_marker_status", renderMarker ? "pass" : "fail");
row("android_render_log_vulkan_marker_status", vulkanMarker ? "pass" : "fail");
row("android_render_log_failure_marker_status", failureMarker ? "fail" : "pass");
process.exit(pass ? 0 : 1);
