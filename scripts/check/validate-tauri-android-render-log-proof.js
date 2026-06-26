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
let coherentSource = false;
let htmlLen = '';

const validRenderMarkerPattern = /\[tauri-shell\]\s+render,\s+html_len=([1-9][0-9]*)(?:\s|$)/;
const anyRenderMarkerPattern = /\[tauri-shell\]\s+render,\s+html_len=/;
const vulkanMarkerPattern = /(Vulkan|vulkan|VK_|ANGLE.*Vulkan|Renderer.*Vulkan|HWUI.*Vulkan|skiavk)/i;
const failureMarkerPattern = /(F\/DEBUG|Fatal signal|F\/libc|F\/VulkanManager|Simple subprocess stdout closed before a valid render arrived|Headless UI completed|parse error: expected value|Requested GL implementation .*angle=vulkan.* not found|Exiting GPU process due to errors during initialization)/i;

function renderHtmlLen(content) {
  const match = content.match(validRenderMarkerPattern);
  return match ? match[1] : '';
}

for (const file of files) {
  if (!file || !fs.existsSync(file) || !fs.statSync(file).isFile()) continue;
  const content = fs.readFileSync(file, 'utf8');
  if (content.length === 0) continue;
  sourceCount += 1;
  text += `\n${content}`;
  const sourceHtmlLen = renderHtmlLen(content);
  if (htmlLen === '' && sourceHtmlLen !== '') htmlLen = sourceHtmlLen;
  if (sourceHtmlLen !== '' && vulkanMarkerPattern.test(content)) {
    coherentSource = true;
  }
}

const hasAnyRenderMarker = anyRenderMarkerPattern.test(text);
const renderMarker = renderHtmlLen(text) !== '';
const vulkanMarker = vulkanMarkerPattern.test(text);
const failureMarker = failureMarkerPattern.test(text);

let reason = 'pass';
if (sourceCount === 0) {
  reason = 'missing-android-render-log-source';
} else if (failureMarker) {
  reason = 'android-render-log-failure-marker';
} else if (hasAnyRenderMarker && !renderMarker) {
  reason = 'android-render-log-html-len-malformed';
} else if (!renderMarker) {
  reason = 'android-render-log-marker-missing';
} else if (!vulkanMarker) {
  reason = 'android-vulkan-log-marker-missing';
} else if (!coherentSource) {
  reason = 'android-render-log-source-mismatch';
}

emit('android_render_log_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('android_render_log_validation_reason', reason);
emit('android_render_log_source_count', sourceCount);
emit('android_render_log_html_len', htmlLen);
emit('android_render_log_source_coherence_status', coherentSource ? 'pass' : 'fail');
emit('android_render_log_marker_status', renderMarker ? 'pass' : 'fail');
emit('android_render_log_vulkan_marker_status', vulkanMarker ? 'pass' : 'fail');
emit('android_render_log_failure_marker_status', failureMarker ? 'fail' : 'pass');

if (reason !== 'pass') {
  process.exit(1);
}
