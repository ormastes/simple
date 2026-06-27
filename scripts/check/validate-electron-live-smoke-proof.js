#!/usr/bin/env node
const fs = require('fs');

function clean(value) {
  if (value === undefined || value === null) return '';
  return String(value).replace(/[\r\n]/g, ' ');
}

function emit(key, value) {
  console.log(`${key}=${clean(value)}`);
}

function decimalIntegerText(value) {
  if (typeof value === 'bigint') return value.toString();
  if (typeof value === 'string' && /^[0-9]+$/.test(value.trim())) return value.trim();
  return null;
}

function integerNumberAtLeast(value, min) {
  return typeof value === 'number' && Number.isInteger(value) && value >= min;
}

function finiteNumberGreaterThan(value, min) {
  return typeof value === 'number' && Number.isFinite(value) && value > min;
}

function finiteNumberAtMost(value, max) {
  return typeof value === 'number' && Number.isFinite(value) && value <= max;
}

function jsonIntegerTextOrBlank(value) {
  return typeof value === 'number' && Number.isInteger(value) ? String(value) : '';
}

function jsonNumberTextOrBlank(value) {
  return typeof value === 'number' && Number.isFinite(value) ? String(value) : '';
}

function jsonBoolTextOrBlank(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return '';
}

function textSample(value) {
  return typeof value === 'string' ? value : '';
}

function versionText(value) {
  return typeof value === 'string' && /^[0-9]+(?:\.[0-9]+)*$/.test(value);
}

const [proofPath, widthText, heightText] = process.argv.slice(2);
if (!proofPath || !widthText || !heightText) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', 'usage-proof-width-height');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(proofPath, 'utf8'));
} catch (err) {
  emit('electron_live_smoke_validation_status', 'fail');
  emit('electron_live_smoke_validation_reason', `invalid-json:${err && err.message ? err.message : err}`);
  process.exit(1);
}

const expectedWidthText = decimalIntegerText(widthText);
const expectedHeightText = decimalIntegerText(heightText);
const expectedWidth = expectedWidthText === null ? NaN : Number(expectedWidthText);
const expectedHeight = expectedHeightText === null ? NaN : Number(expectedHeightText);
const expectedProofSource = 'src/app/ui.electron/bridge.js:electronLiveSmokeProofScript';
const userAgent = textSample(proof.electron_user_agent);
const maxEventTimingMs = 1000;

let reason = 'pass';
if (proof.target !== 'electron') {
  reason = 'unexpected-target';
} else if (proof.surface_id !== 'main') {
  reason = 'unexpected-surface';
} else if (proof.proof_source !== expectedProofSource) {
  reason = 'unexpected-proof-source';
} else if (proof.browser_engine !== 'chromium') {
  reason = 'unexpected-browser-engine';
} else if (!/Electron\/[0-9]/.test(userAgent) || !/(Chrome|Chromium)\/[0-9]/.test(userAgent)) {
  reason = 'missing-electron-chromium-user-agent';
} else if (!versionText(proof.electron_process_version) || !versionText(proof.chrome_process_version)) {
  reason = 'missing-electron-chromium-process-versions';
} else if (!Number.isInteger(expectedWidth) || expectedWidth < 1 || proof.width !== expectedWidth) {
  reason = 'unexpected-width';
} else if (!Number.isInteger(expectedHeight) || expectedHeight < 1 || proof.height !== expectedHeight) {
  reason = 'unexpected-height';
} else if (!integerNumberAtLeast(proof.body_html_length, 1)) {
  reason = 'missing-render-html';
} else if (!integerNumberAtLeast(proof.css_length, 1)) {
  reason = 'missing-render-css';
} else if (proof.app_element_present !== true) {
  reason = 'missing-app-element';
} else if (!integerNumberAtLeast(proof.body_text_length, 1)) {
  reason = 'missing-rendered-text';
} else if (
  textSample(proof.body_text_sample).length < 1 ||
  !textSample(proof.body_text_sample).includes('Hello World from Web!') ||
  textSample(proof.body_text_sample).length > proof.body_text_length
) {
  reason = 'missing-rendered-text-sample';
} else if (
  proof.performance_now_available !== true ||
  !finiteNumberGreaterThan(proof.performance_now_delta_ms, 0) ||
  !finiteNumberAtMost(proof.performance_now_delta_ms, maxEventTimingMs)
) {
  reason = 'missing-performance-now';
} else if (proof.animation_frame_available !== true || !integerNumberAtLeast(proof.animation_frame_count, 2)) {
  reason = 'missing-animation-frames';
} else if (proof.css_animation_probe !== true) {
  reason = 'missing-css-animation';
} else if (
  proof.event_dispatch_available !== true ||
  !integerNumberAtLeast(proof.event_dispatch_count, 1) ||
  proof.event_dispatch_type !== 'simple-electron-live-smoke-event' ||
  proof.event_dispatch_detail !== 'live-smoke-input' ||
  textSample(proof.event_dispatch_error).length > 0
) {
  reason = 'missing-event-dispatch';
} else if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
}

emit('electron_live_smoke_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('electron_live_smoke_validation_reason', reason);
emit('electron_live_smoke_target', proof.target);
emit('electron_live_smoke_surface_id', proof.surface_id);
emit('electron_live_smoke_proof_source', proof.proof_source);
emit('electron_live_smoke_browser_engine', proof.browser_engine);
emit('electron_live_smoke_electron_user_agent', proof.electron_user_agent);
emit('electron_live_smoke_electron_process_version', proof.electron_process_version);
emit('electron_live_smoke_chrome_process_version', proof.chrome_process_version);
emit('electron_live_smoke_width', jsonIntegerTextOrBlank(proof.width));
emit('electron_live_smoke_height', jsonIntegerTextOrBlank(proof.height));
emit('electron_live_smoke_body_html_length', jsonIntegerTextOrBlank(proof.body_html_length));
emit('electron_live_smoke_css_length', jsonIntegerTextOrBlank(proof.css_length));
emit('electron_live_smoke_app_element_present', jsonBoolTextOrBlank(proof.app_element_present));
emit('electron_live_smoke_body_text_length', jsonIntegerTextOrBlank(proof.body_text_length));
emit('electron_live_smoke_body_text_sample', proof.body_text_sample);
emit('electron_live_smoke_performance_now_available', jsonBoolTextOrBlank(proof.performance_now_available));
emit('electron_live_smoke_performance_now_delta_ms', jsonNumberTextOrBlank(proof.performance_now_delta_ms));
emit('electron_live_smoke_animation_frame_available', jsonBoolTextOrBlank(proof.animation_frame_available));
emit('electron_live_smoke_animation_frame_count', jsonIntegerTextOrBlank(proof.animation_frame_count));
emit('electron_live_smoke_css_animation_probe', jsonBoolTextOrBlank(proof.css_animation_probe));
emit('electron_live_smoke_event_dispatch_available', jsonBoolTextOrBlank(proof.event_dispatch_available));
emit('electron_live_smoke_event_dispatch_count', jsonIntegerTextOrBlank(proof.event_dispatch_count));
emit('electron_live_smoke_event_dispatch_type', proof.event_dispatch_type);
emit('electron_live_smoke_event_dispatch_detail', proof.event_dispatch_detail);
emit('electron_live_smoke_event_dispatch_error', proof.event_dispatch_error);
emit('electron_live_smoke_blur_or_tolerance_used', jsonBoolTextOrBlank(proof.blur_or_tolerance_used));

if (reason !== 'pass') {
  process.exit(1);
}
