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
const requestedSourceCount = files.length;
let missingSourceCount = 0;
let sourceCount = 0;
let text = '';
let coherentSource = false;
let htmlLen = '';

const validRenderMarkerPattern = /\[tauri-shell\]\s+render,\s+html_len=([1-9][0-9]*)(?:\s|$)/;
const anyRenderMarkerPattern = /\[tauri-shell\]\s+render,\s+html_len=/;

function renderHtmlLen(content) {
  const match = content.match(validRenderMarkerPattern);
  return match ? match[1] : '';
}

for (const file of files) {
  if (!file || !fs.existsSync(file) || !fs.statSync(file).isFile()) {
    missingSourceCount += 1;
    continue;
  }
  const content = fs.readFileSync(file, 'utf8');
  if (content.length === 0) continue;
  sourceCount += 1;
  text += `\n${content}`;
  const sourceHtmlLen = renderHtmlLen(content);
  const sourceRenderMarker = sourceHtmlLen !== '';
  if (htmlLen === '' && sourceHtmlLen !== '') htmlLen = sourceHtmlLen;
  const sourceMetalMarker = /(CAMetalLayer|Metal renderer ready|MetalKit\.framework|Metal\.framework|-framework Metal|\bMTL[A-Za-z0-9_]*\b|\bAGX\b|\bIOGPU\b)/i.test(content);
  const sourceTauriIosContext = /(\[tauri-shell\]\s+ios renderer context:.*WKWebView|Tauri iOS external_url|ios_mdi_probe\.html|\[tauri-shell\]\s+creating window (from|with)|mobile inline shell base)/i.test(content);
  const sourceMetalContext = /\[tauri-shell\]\s+ios renderer context:(?=.*WKWebView)(?=.*metal_expected=true)(?=.*metal_layer=CAMetalLayer)/i.test(content);
  if (sourceRenderMarker && sourceMetalMarker && sourceTauriIosContext && sourceMetalContext) {
    coherentSource = true;
  }
}

const hasAnyRenderMarker = anyRenderMarkerPattern.test(text);
const renderMarker = renderHtmlLen(text) !== '';
const metalMarker = /(CAMetalLayer|Metal renderer ready|MetalKit\.framework|Metal\.framework|-framework Metal|\bMTL[A-Za-z0-9_]*\b|\bAGX\b|\bIOGPU\b)/i.test(text);
const tauriIosContext = /(\[tauri-shell\]\s+ios renderer context:.*WKWebView|Tauri iOS external_url|ios_mdi_probe\.html|\[tauri-shell\]\s+creating window (from|with)|mobile inline shell base)/i.test(text);
const metalContext = /\[tauri-shell\]\s+ios renderer context:(?=.*WKWebView)(?=.*metal_expected=true)(?=.*metal_layer=CAMetalLayer)/i.test(text);
const failureMarker = /(eval FAIL|inline shell eval FAIL|delayed inline shell eval FAIL|window 'main' not found|parse error|Fatal signal|F\/DEBUG|NSURLErrorDomain|failed provisional load|Headless UI completed|subprocess exited with code)/i.test(text);

let reason = 'pass';
if (requestedSourceCount === 0 || sourceCount === 0) {
  reason = 'missing-ios-render-log-source';
} else if (missingSourceCount > 0) {
  reason = 'ios-render-log-source-missing';
} else if (failureMarker) {
  reason = 'ios-render-log-failure-marker';
} else if (hasAnyRenderMarker && !renderMarker) {
  reason = 'ios-render-log-html-len-malformed';
} else if (!renderMarker) {
  reason = 'ios-render-log-marker-missing';
} else if (!metalMarker) {
  reason = 'ios-metal-log-marker-missing';
} else if (!tauriIosContext) {
  reason = 'ios-tauri-wkwebview-context-missing';
} else if (!metalContext) {
  reason = 'ios-metal-context-missing';
} else if (!coherentSource) {
  reason = 'ios-render-log-source-mismatch';
}

emit('ios_render_log_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('ios_render_log_validation_reason', reason);
emit('ios_render_log_requested_source_count', requestedSourceCount);
emit('ios_render_log_source_count', sourceCount);
emit('ios_render_log_missing_source_count', missingSourceCount);
emit('ios_render_log_source_coherence_status', coherentSource ? 'pass' : 'fail');
emit('ios_render_log_marker_status', renderMarker ? 'pass' : 'fail');
emit('ios_render_log_html_len', htmlLen);
emit('ios_render_log_metal_marker_status', metalMarker ? 'pass' : 'fail');
emit('ios_render_log_tauri_context_status', tauriIosContext ? 'pass' : 'fail');
emit('ios_render_log_metal_context_status', metalContext ? 'pass' : 'fail');
emit('ios_render_log_failure_marker_status', failureMarker ? 'fail' : 'pass');

if (reason !== 'pass') {
  process.exit(1);
}
