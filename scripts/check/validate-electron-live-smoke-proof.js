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
  if (typeof value === 'number' && Number.isInteger(value)) return String(value);
  if (typeof value === 'bigint') return value.toString();
  if (typeof value === 'string' && /^[0-9]+$/.test(value.trim())) return value.trim();
  return null;
}

function integerAtLeast(value, min) {
  const text = decimalIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(min);
}

function finiteNumberAtLeast(value, min) {
  return typeof value === 'number' && Number.isFinite(value) && value >= min;
}

function intText(value) {
  const text = decimalIntegerText(value);
  return text === null ? clean(value) : text;
}

function boolText(value) {
  if (value === true) return 'true';
  if (value === false) return 'false';
  return clean(value);
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

const expectedWidth = Number(widthText);
const expectedHeight = Number(heightText);

let reason = 'pass';
if (proof.target !== 'electron') {
  reason = 'unexpected-target';
} else if (proof.surface_id !== 'main') {
  reason = 'unexpected-surface';
} else if (!Number.isInteger(expectedWidth) || expectedWidth < 1 || proof.width !== expectedWidth) {
  reason = 'unexpected-width';
} else if (!Number.isInteger(expectedHeight) || expectedHeight < 1 || proof.height !== expectedHeight) {
  reason = 'unexpected-height';
} else if (!integerAtLeast(proof.body_html_length, 1)) {
  reason = 'missing-render-html';
} else if (proof.app_element_present !== true) {
  reason = 'missing-app-element';
} else if (!integerAtLeast(proof.body_text_length, 1)) {
  reason = 'missing-rendered-text';
} else if (proof.performance_now_available !== true || !finiteNumberAtLeast(proof.performance_now_delta_ms, 0)) {
  reason = 'missing-performance-now';
} else if (proof.animation_frame_available !== true || !integerAtLeast(proof.animation_frame_count, 2)) {
  reason = 'missing-animation-frames';
} else if (proof.css_animation_probe !== true) {
  reason = 'missing-css-animation';
} else if (proof.blur_or_tolerance_used !== false) {
  reason = 'blur-or-tolerance-not-allowed';
}

emit('electron_live_smoke_validation_status', reason === 'pass' ? 'pass' : 'fail');
emit('electron_live_smoke_validation_reason', reason);
emit('electron_live_smoke_target', proof.target);
emit('electron_live_smoke_surface_id', proof.surface_id);
emit('electron_live_smoke_width', intText(proof.width));
emit('electron_live_smoke_height', intText(proof.height));
emit('electron_live_smoke_body_html_length', intText(proof.body_html_length));
emit('electron_live_smoke_app_element_present', boolText(proof.app_element_present));
emit('electron_live_smoke_body_text_length', intText(proof.body_text_length));
emit('electron_live_smoke_body_text_sample', proof.body_text_sample);
emit('electron_live_smoke_performance_now_available', boolText(proof.performance_now_available));
emit('electron_live_smoke_performance_now_delta_ms', clean(proof.performance_now_delta_ms));
emit('electron_live_smoke_animation_frame_available', boolText(proof.animation_frame_available));
emit('electron_live_smoke_animation_frame_count', intText(proof.animation_frame_count));
emit('electron_live_smoke_css_animation_probe', boolText(proof.css_animation_probe));
emit('electron_live_smoke_blur_or_tolerance_used', boolText(proof.blur_or_tolerance_used));

if (reason !== 'pass') {
  process.exit(1);
}
