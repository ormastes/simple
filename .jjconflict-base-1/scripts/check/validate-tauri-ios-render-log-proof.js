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
const rawRenderEnvelopePattern = /\[tauri-shell\]\s+raw stdout:\s*(\{.*"type"\s*:\s*"render".*\})/;
const rawRenderEnvelopePrefixPattern = /\[tauri-shell\]\s+raw stdout:\s*\{[^\r\n]*"type"\s*:\s*"render"/;
const renderAppliedPattern = /\[tauri-shell\]\s+(inline shell eval OK|eval OK|delayed inline shell eval OK)/;
const metalRuntimeMarkerPattern = /(CAMetalLayer\s+Metal renderer ready|MetalKit\.framework|Metal\.framework|-framework Metal|\bMTL[A-Za-z0-9_]*\b|\bAGX\b|\bIOGPU\b)/i;
const fallbackRendererPattern = /(SwiftShader|software rasterizer|software renderer|software rendering|llvmpipe|ANGLE[^\r\n]*(OpenGL|GL)|OpenGL[^\r\n]*(renderer|fallback|software)|fallback renderer)/i;
const seenSourceRealpaths = new Set();

function renderProof(content) {
  const match = content.match(validRenderMarkerPattern);
  if (match) {
    const htmlLen = BigInt(match[1]) <= BigInt(maxRenderHtmlLen) ? match[1] : '';
    return { present: htmlLen !== '', htmlLen, source: htmlLen !== '' ? 'html_len' : 'html_len-malformed' };
  }
  for (const line of content.split(/\r?\n/)) {
    const rawMatch = line.match(rawRenderEnvelopePattern);
    if (!rawMatch) continue;
    try {
      const message = JSON.parse(rawMatch[1]);
      if (message && message.type === 'render' && typeof message.html === 'string') {
        const len = message.html.length;
        if (len > 0 && len <= maxRenderHtmlLen) {
          return { present: true, htmlLen: String(len), source: 'raw-render-envelope' };
        }
      }
    } catch (_err) {
      // A malformed raw stdout envelope is handled by the marker checks below.
    }
  }
  if (rawRenderEnvelopePrefixPattern.test(content) && renderAppliedPattern.test(content)) {
    return { present: true, htmlLen: '', source: 'raw-render-envelope-truncated' };
  }
  if (rawRenderEnvelopePrefixPattern.test(content)) {
    return { present: false, htmlLen: '', source: 'raw-render-envelope-malformed' };
  }
  return { present: false, htmlLen: '', source: 'missing' };
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
  const sourceRenderProof = renderProof(content);
  const sourceHtmlLen = sourceRenderProof.htmlLen;
  const sourceRenderMarker = sourceRenderProof.present;
  if (htmlLen === '' && sourceHtmlLen !== '') htmlLen = sourceHtmlLen;
  const sourceMetalMarker = metalRuntimeMarkerPattern.test(content);
  const sourceTauriIosContext = /(\[tauri-shell\]\s+ios renderer context:.*WKWebView|Tauri iOS external_url|ios_mdi_probe\.html|\[tauri-shell\]\s+creating window (from|with)|mobile inline shell base)/i.test(content);
  const sourceMetalContext = /\[tauri-shell\]\s+ios renderer context:(?=.*WKWebView)(?=.*metal_expected=true)(?=.*metal_layer=CAMetalLayer)/i.test(content);
  if (sourceRenderMarker && sourceMetalMarker && sourceTauriIosContext && sourceMetalContext) {
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
const hasAnyRawRenderEnvelope = rawRenderEnvelopePattern.test(text);
const renderLogProof = renderProof(text);
const renderMarker = renderLogProof.present;
const renderMarkerSource = hasAnyRenderMarker ? 'html_len' : renderLogProof.source;
const metalMarker = metalRuntimeMarkerPattern.test(text);
const fallbackMarker = fallbackRendererPattern.test(text);
const tauriIosContext = /(\[tauri-shell\]\s+ios renderer context:.*WKWebView|Tauri iOS external_url|ios_mdi_probe\.html|\[tauri-shell\]\s+creating window (from|with)|mobile inline shell base)/i.test(text);
const metalContext = /\[tauri-shell\]\s+ios renderer context:(?=.*WKWebView)(?=.*metal_expected=true)(?=.*metal_layer=CAMetalLayer)/i.test(text);
const failureMarker = /(eval FAIL|inline shell eval FAIL|delayed inline shell eval FAIL|window 'main' not found|parse error|Fatal signal|F\/DEBUG|NSURLErrorDomain|failed provisional load|Headless UI completed|subprocess exited with code)/i.test(text);

let reason = 'pass';
if (requestedSourceCount === 0 || sourceCount === 0) {
  reason = 'missing-ios-render-log-source';
} else if (missingSourceCount > 0) {
  reason = 'ios-render-log-source-missing';
} else if (symlinkSourceCount > 0) {
  reason = 'ios-render-log-source-symlink';
} else if (hardlinkSourceCount > 0) {
  reason = 'ios-render-log-source-hardlink';
} else if (duplicateSourceCount > 0) {
  reason = 'ios-render-log-source-duplicate';
} else if (nonregularSourceCount > 0) {
  reason = 'ios-render-log-source-not-regular';
} else if (emptySourceCount > 0) {
  reason = 'ios-render-log-source-empty';
} else if (failureMarker) {
  reason = 'ios-render-log-failure-marker';
} else if (fallbackMarker) {
  reason = 'ios-render-log-fallback-gpu';
} else if (hasAnyRenderMarker && !renderMarker) {
  reason = 'ios-render-log-html-len-malformed';
} else if ((hasAnyRawRenderEnvelope || rawRenderEnvelopePrefixPattern.test(text)) && !renderMarker) {
  reason = 'ios-render-log-raw-envelope-malformed';
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
emit('ios_render_log_empty_source_count', emptySourceCount);
emit('ios_render_log_symlink_source_count', symlinkSourceCount);
emit('ios_render_log_hardlink_source_count', hardlinkSourceCount);
emit('ios_render_log_duplicate_source_count', duplicateSourceCount);
emit('ios_render_log_nonregular_source_count', nonregularSourceCount);
emit('ios_render_log_source_coherence_status', coherentSource ? 'pass' : 'fail');
emit('ios_render_log_coherent_source_path', coherentSourcePath);
emit('ios_render_log_coherent_source_size_bytes', coherentSourceSizeBytes);
emit('ios_render_log_marker_status', renderMarker ? 'pass' : 'fail');
emit('ios_render_log_marker_source', renderMarkerSource);
emit('ios_render_log_html_len', htmlLen);
emit('ios_render_log_metal_marker_status', metalMarker ? 'pass' : 'fail');
emit('ios_render_log_fallback_marker_status', fallbackMarker ? 'fail' : 'pass');
emit('ios_render_log_tauri_context_status', tauriIosContext ? 'pass' : 'fail');
emit('ios_render_log_metal_context_status', metalContext ? 'pass' : 'fail');
emit('ios_render_log_failure_marker_status', failureMarker ? 'fail' : 'pass');

if (reason !== 'pass') {
  process.exit(1);
}
