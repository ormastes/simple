#!/usr/bin/env node
const fs = require('fs');

function clean(value) {
  if (value === undefined || value === null) return '';
  return String(value).replace(/[\r\n]/g, ' ');
}

function emit(key, value) {
  console.log(`${key}=${clean(value)}`);
}

const files = process.argv.slice(2).filter(Boolean);
let sourceCount = 0;
let text = '';
for (const file of files) {
  if (!file || !fs.existsSync(file) || !fs.statSync(file).isFile()) continue;
  const content = fs.readFileSync(file, 'utf8');
  if (content.length === 0) continue;
  sourceCount += 1;
  text += `\n${content}`;
}

const renderMarker = /\[tauri-shell\]\s+render,\s+html_len=[1-9][0-9]*/.test(text);
const metalMarker = /(CAMetalLayer|Metal renderer ready|MetalKit\.framework|Metal\.framework|-framework Metal|\bMTL[A-Za-z0-9_]*\b|\bAGX\b|\bIOGPU\b)/i.test(text);
const tauriIosContext = /(\[tauri-shell\]\s+ios renderer context:.*WKWebView|Tauri iOS external_url|ios_mdi_probe\.html|\[tauri-shell\]\s+creating window (from|with)|mobile inline shell base)/i.test(text);
const metalContext = /\[tauri-shell\]\s+ios renderer context:(?=.*WKWebView)(?=.*metal_expected=true)(?=.*metal_layer=CAMetalLayer)/i.test(text);
const failureMarker = /(eval FAIL|inline shell eval FAIL|delayed inline shell eval FAIL|window 'main' not found|parse error|Fatal signal|F\/DEBUG|NSURLErrorDomain|failed provisional load|Headless UI completed|subprocess exited with code)/i.test(text);

let reason = 'pass';
if (sourceCount === 0) {
  reason = 'missing-ios-render-log-source';
} else if (failureMarker) {
  reason = 'ios-render-log-failure-marker';
} else if (!renderMarker) {
  reason = 'ios-render-log-marker-missing';
} else if (!metalMarker) {
  reason = 'ios-metal-log-marker-missing';
} else if (!tauriIosContext) {
  reason = 'ios-tauri-wkwebview-context-missing';
} else if (!metalContext) {
  reason = 'ios-metal-context-missing';
}

emit('ios_render_log_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('ios_render_log_validation_reason', reason);
emit('ios_render_log_source_count', sourceCount);
emit('ios_render_log_marker_status', renderMarker ? 'pass' : 'fail');
emit('ios_render_log_metal_marker_status', metalMarker ? 'pass' : 'fail');
emit('ios_render_log_tauri_context_status', tauriIosContext ? 'pass' : 'fail');
emit('ios_render_log_metal_context_status', metalContext ? 'pass' : 'fail');
emit('ios_render_log_failure_marker_status', failureMarker ? 'fail' : 'pass');

if (reason !== 'pass') {
  process.exit(1);
}
