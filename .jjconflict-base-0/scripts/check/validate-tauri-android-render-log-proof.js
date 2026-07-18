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
let emptySourceCount = 0;
let symlinkSourceCount = 0;
let hardlinkSourceCount = 0;
let duplicateSourceCount = 0;
let nonregularSourceCount = 0;
let sourceCount = 0;
let text = '';
let coherentSource = false;
let coherentSourcePath = '';
let coherentSourceSizeBytes = '';
let htmlLen = '';
let coherentSourceHtmlLen = '';
const maxRenderHtmlLen = 10000000;

const validRenderMarkerPattern = /\[tauri-shell\]\s+render,\s+html_len=([1-9][0-9]*)(?:\s|$)/;
const anyRenderMarkerPattern = /\[tauri-shell\]\s+render,\s+html_len=/;
const vulkanMarkerPattern = /(Vulkan|vulkan|VK_|ANGLE.*Vulkan|Renderer.*Vulkan|HWUI.*Vulkan|skiavk)/i;
const foregroundMarkerPattern = /(foreground=.*com\.simple\.ui|mCurrentFocus=.*com\.simple\.ui|topResumedActivity=.*com\.simple\.ui|ResumedActivity:.*com\.simple\.ui|ACTIVITY[^\n]*com\.simple\.ui)/i;
const failureMarkerPattern = /(F\/DEBUG|Fatal signal|F\/libc|F\/VulkanManager|Simple subprocess stdout closed before a valid render arrived|Headless UI completed|parse error: expected value|Requested GL implementation .*angle=vulkan.* not found|Exiting GPU process due to errors during initialization)/i;
const seenSourceRealpaths = new Set();

function renderHtmlLen(content) {
  const match = content.match(validRenderMarkerPattern);
  if (!match) return '';
  return BigInt(match[1]) <= BigInt(maxRenderHtmlLen) ? match[1] : '';
}

for (const file of files) {
  let stat;
  try {
    stat = file ? fs.lstatSync(file) : null;
  } catch (_err) {
    stat = null;
  }
  if (!stat) {
    missingSourceCount += 1;
    continue;
  }
  if (stat.isSymbolicLink()) {
    symlinkSourceCount += 1;
    continue;
  }
  if (!stat.isFile()) {
    nonregularSourceCount += 1;
    continue;
  }
  if (stat.nlink > 1) {
    hardlinkSourceCount += 1;
    continue;
  }
  let realpath = '';
  try {
    realpath = fs.realpathSync(file);
  } catch (_err) {
    missingSourceCount += 1;
    continue;
  }
  if (seenSourceRealpaths.has(realpath)) {
    duplicateSourceCount += 1;
    continue;
  }
  seenSourceRealpaths.add(realpath);
  const content = fs.readFileSync(file, 'utf8');
  if (content.length === 0) {
    emptySourceCount += 1;
    continue;
  }
  sourceCount += 1;
  text += `\n${content}`;
  const sourceHtmlLen = renderHtmlLen(content);
  if (htmlLen === '' && sourceHtmlLen !== '') htmlLen = sourceHtmlLen;
  if (sourceHtmlLen !== '' && vulkanMarkerPattern.test(content)) {
    coherentSource = true;
    if (coherentSourcePath === '') {
      coherentSourcePath = file;
      coherentSourceSizeBytes = String(stat.size);
      coherentSourceHtmlLen = sourceHtmlLen;
    }
  }
}

if (coherentSourceHtmlLen !== '') {
  htmlLen = coherentSourceHtmlLen;
}

const hasAnyRenderMarker = anyRenderMarkerPattern.test(text);
const renderMarker = renderHtmlLen(text) !== '';
const vulkanMarker = vulkanMarkerPattern.test(text);
const foregroundMarker = foregroundMarkerPattern.test(text);
const failureMarker = failureMarkerPattern.test(text);

let reason = 'pass';
if (requestedSourceCount === 0 || sourceCount === 0) {
  reason = 'missing-android-render-log-source';
} else if (missingSourceCount > 0) {
  reason = 'android-render-log-source-missing';
} else if (symlinkSourceCount > 0) {
  reason = 'android-render-log-source-symlink';
} else if (hardlinkSourceCount > 0) {
  reason = 'android-render-log-source-hardlink';
} else if (duplicateSourceCount > 0) {
  reason = 'android-render-log-source-duplicate';
} else if (nonregularSourceCount > 0) {
  reason = 'android-render-log-source-not-regular';
} else if (emptySourceCount > 0) {
  reason = 'android-render-log-source-empty';
} else if (failureMarker) {
  reason = 'android-render-log-failure-marker';
} else if (hasAnyRenderMarker && !renderMarker) {
  reason = 'android-render-log-html-len-malformed';
} else if (!renderMarker) {
  reason = 'android-render-log-marker-missing';
} else if (!vulkanMarker) {
  reason = 'android-vulkan-log-marker-missing';
} else if (!foregroundMarker) {
  reason = 'android-foreground-marker-missing';
} else if (!coherentSource) {
  reason = 'android-render-log-source-mismatch';
}

emit('android_render_log_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('android_render_log_validation_reason', reason);
emit('android_render_log_requested_source_count', requestedSourceCount);
emit('android_render_log_source_count', sourceCount);
emit('android_render_log_missing_source_count', missingSourceCount);
emit('android_render_log_empty_source_count', emptySourceCount);
emit('android_render_log_symlink_source_count', symlinkSourceCount);
emit('android_render_log_hardlink_source_count', hardlinkSourceCount);
emit('android_render_log_duplicate_source_count', duplicateSourceCount);
emit('android_render_log_nonregular_source_count', nonregularSourceCount);
emit('android_render_log_html_len', htmlLen);
emit('android_render_log_source_coherence_status', coherentSource ? 'pass' : 'fail');
emit('android_render_log_coherent_source_path', coherentSourcePath);
emit('android_render_log_coherent_source_size_bytes', coherentSourceSizeBytes);
emit('android_render_log_marker_status', renderMarker ? 'pass' : 'fail');
emit('android_render_log_vulkan_marker_status', vulkanMarker ? 'pass' : 'fail');
emit('android_render_log_foreground_marker_status', foregroundMarker ? 'pass' : 'fail');
emit('android_render_log_failure_marker_status', failureMarker ? 'fail' : 'pass');

if (reason !== 'pass') {
  process.exit(1);
}
