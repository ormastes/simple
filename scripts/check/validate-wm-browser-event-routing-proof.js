#!/usr/bin/env node
const fs = require('fs');

function clean(value) {
  if (value === undefined || value === null) return '';
  return String(value).replace(/[\r\n]/g, ' ');
}

function boolTrue(value) {
  return value === true;
}

function jsonIntegerText(value) {
  if (typeof value === 'number' && Number.isInteger(value)) return String(value);
  return null;
}

function jsonNumberText(value) {
  if (typeof value === 'number' && Number.isFinite(value)) return String(value);
  return null;
}

function jsonIntegerAtLeast(value, required) {
  const text = jsonIntegerText(value);
  if (text === null) return false;
  return BigInt(text) >= BigInt(required);
}

function jsonDecimalGreaterThan(value, required) {
  const text = jsonNumberText(value);
  if (text === null) return false;
  return Number(text) > required;
}

function jsonDecimalAtLeast(value, required) {
  const text = jsonNumberText(value);
  if (text === null) return false;
  return Number(text) >= required;
}

function jsonDecimalAtMost(value, required) {
  const text = jsonNumberText(value);
  if (text === null) return false;
  return Number(text) <= required;
}

function sameJsonInteger(actual, expected) {
  const a = jsonIntegerText(actual);
  const e = jsonIntegerText(expected);
  if (a === null || e === null) return false;
  return BigInt(a) === BigInt(e);
}

function jsonIntegerTextOrBlank(value) {
  const text = jsonIntegerText(value);
  return text === null ? '' : text;
}

function jsonDecimalTextOrBlank(value) {
  const text = jsonNumberText(value);
  return text === null ? '' : text;
}

function jsonDecimalTextOrClean(value) {
  const text = jsonNumberText(value);
  return text === null ? clean(value) : text;
}

function row(key, value) {
  console.log(`${key}=${clean(value)}`);
}

const expectedEventSequence = [
  'host_wm_pointer:down',
  'window_cmd:focus',
  'window_cmd:move',
  'window_cmd:title_command',
  'window_cmd:maximize',
  'input_event:text_input',
  'input_event:pointer_down',
  'input_event:pointer_up',
];
const expectedProofSource = 'tools/web-render-backend/wm_event_check.js';
const maxEventTimingMs = 1000;

function eventSequenceText(value) {
  if (!Array.isArray(value)) return '';
  return value.map(clean).join(',');
}

function sameEventSequence(value) {
  if (!Array.isArray(value) || value.length !== expectedEventSequence.length) return false;
  return expectedEventSequence.every((entry, index) => value[index] === entry);
}

const jsonPath = process.argv[2];
if (!jsonPath) {
  row('wm_browser_event_routing_validation_status', 'fail');
  row('wm_browser_event_routing_validation_reason', 'usage-json-path');
  process.exit(1);
}

let proof;
try {
  proof = JSON.parse(fs.readFileSync(jsonPath, 'utf8'));
} catch (err) {
  row('wm_browser_event_routing_validation_status', 'fail');
  row('wm_browser_event_routing_validation_reason', 'invalid-json');
  row('wm_browser_event_routing_validation_error', err && err.message ? err.message : err);
  process.exit(1);
}

const move = proof.move_payload || {};
const title = proof.title_payload || {};
const text = proof.text_payload || {};

const rows = {
  proof_source: proof.proof_source,
  ready: proof.ready,
  wm_found: proof.wm_found,
  window_cmd_count: jsonIntegerTextOrBlank(proof.window_cmd_count),
  input_event_count: jsonIntegerTextOrBlank(proof.input_event_count),
  focus_count: jsonIntegerTextOrBlank(proof.focus_count),
  move_count: jsonIntegerTextOrBlank(proof.move_count),
  maximize_count: jsonIntegerTextOrBlank(proof.maximize_count),
  title_command_count: jsonIntegerTextOrBlank(proof.title_command_count),
  text_input_count: jsonIntegerTextOrBlank(proof.text_input_count),
  pointer_down_count: jsonIntegerTextOrBlank(proof.pointer_down_count),
  pointer_up_count: jsonIntegerTextOrBlank(proof.pointer_up_count),
  event_sequence: eventSequenceText(proof.event_sequence),
  performance_now_available: proof.performance_now_available,
  performance_now_delta_ms: jsonDecimalTextOrClean(proof.performance_now_delta_ms),
  input_to_paint_ms: jsonDecimalTextOrClean(proof.input_to_paint_ms),
  animation_frame_available: proof.animation_frame_available,
  animation_frame_count: jsonIntegerTextOrBlank(proof.animation_frame_count),
  css_animation_probe: proof.css_animation_probe,
  title_text: proof.title_text,
  title_context_text: proof.title_context_text,
  traffic_button_count: jsonIntegerTextOrBlank(proof.traffic_button_count),
  title_input_tag: proof.title_input_tag,
  titlebar_height: proof.titlebar_height,
  titlebar_display: proof.titlebar_display,
  titlebar_cursor: proof.titlebar_cursor,
  titlebar_background: proof.titlebar_background,
  title_color: proof.title_color,
  title_font_weight: jsonIntegerTextOrBlank(proof.title_font_weight),
  title_input_min_width: proof.title_input_min_width,
  title_input_width: proof.title_input_width,
  title_input_width_px: jsonDecimalTextOrBlank(proof.title_input_width_px),
  title_input_height: proof.title_input_height,
  title_input_cursor: proof.title_input_cursor,
  title_input_background: proof.title_input_background,
  close_button_background: proof.close_button_background,
  minimize_button_background: proof.minimize_button_background,
  maximize_button_background: proof.maximize_button_background,
  expected_move_x: jsonIntegerTextOrBlank(proof.expected_move_x),
  expected_move_y: jsonIntegerTextOrBlank(proof.expected_move_y),
  move_payload_x: jsonIntegerTextOrBlank(move.x),
  move_payload_y: jsonIntegerTextOrBlank(move.y),
  move_payload_source: move.source,
  move_payload_window_id_hint: move.window_id_hint,
  title_command_text: title.command_text,
  text_input_text: text.event ? text.event.text : undefined,
};

let reason = 'pass';
if (!boolTrue(proof.pass)) {
  reason = 'probe-reported-fail';
} else if (proof.proof_source !== expectedProofSource) {
  reason = 'event-routing-proof-source-missing';
} else if (!boolTrue(proof.ready) || !boolTrue(proof.wm_found)) {
  reason = 'event-routing-ready-missing';
} else if (
  !jsonIntegerAtLeast(proof.focus_count, 1) ||
  !jsonIntegerAtLeast(proof.move_count, 1) ||
  !jsonIntegerAtLeast(proof.maximize_count, 1) ||
  !jsonIntegerAtLeast(proof.title_command_count, 1) ||
  !jsonIntegerAtLeast(proof.text_input_count, 1) ||
  !jsonIntegerAtLeast(proof.pointer_down_count, 1) ||
  !jsonIntegerAtLeast(proof.pointer_up_count, 1)
) {
  reason = 'event-routing-contract-missing';
} else if (!sameEventSequence(proof.event_sequence)) {
  reason = 'event-routing-sequence-contract-missing';
} else if (
  !boolTrue(proof.performance_now_available) ||
  !jsonDecimalGreaterThan(proof.performance_now_delta_ms, 0) ||
  !jsonDecimalAtMost(proof.performance_now_delta_ms, maxEventTimingMs) ||
  !boolTrue(proof.animation_frame_available) ||
  !jsonIntegerAtLeast(proof.animation_frame_count, 2) ||
  !boolTrue(proof.css_animation_probe)
) {
  reason = 'event-routing-performance-animation-contract-missing';
} else if (
  !jsonDecimalGreaterThan(proof.input_to_paint_ms, 0) ||
  !jsonDecimalAtMost(proof.input_to_paint_ms, maxEventTimingMs)
) {
  reason = 'event-routing-interaction-latency-contract-missing';
} else if (
  move.window_id_hint !== 'win1' ||
  move.source !== 'native_event' ||
  !sameJsonInteger(move.x, proof.expected_move_x) ||
  !sameJsonInteger(move.y, proof.expected_move_y) ||
  title.command_text !== '/tmp/project' ||
  !text.event ||
  text.event.text !== 'Hello Simple'
) {
  reason = 'event-routing-payload-contract-missing';
} else if (
  proof.title_text !== 'Terminal' ||
  proof.title_context_text !== 'terminal' ||
  !jsonIntegerAtLeast(proof.traffic_button_count, 3) ||
  proof.title_input_tag !== 'input' ||
  proof.titlebar_height !== '34px' ||
  proof.titlebar_display !== 'flex' ||
  proof.titlebar_cursor !== 'grab' ||
  proof.titlebar_background !== 'rgb(229, 231, 235)' ||
  proof.title_color !== 'rgb(17, 24, 39)' ||
  !jsonIntegerAtLeast(proof.title_font_weight, 700) ||
  proof.title_input_min_width !== '142px' ||
  !jsonDecimalAtLeast(proof.title_input_width_px, 142) ||
  proof.title_input_height !== '24px' ||
  proof.title_input_cursor !== 'text' ||
  proof.title_input_background !== 'rgb(241, 245, 249)' ||
  proof.close_button_background !== 'rgb(239, 68, 68)' ||
  proof.minimize_button_background !== 'rgb(234, 179, 8)' ||
  proof.maximize_button_background !== 'rgb(34, 197, 94)'
) {
  reason = 'event-routing-ui-contract-missing';
}

const status = reason === 'pass' ? 'pass' : 'fail';
row('wm_browser_event_routing_validation_status', status);
row('wm_browser_event_routing_validation_reason', reason);
for (const [key, value] of Object.entries(rows)) {
  row(`wm_browser_event_routing_${key}`, value);
}
process.exit(status === 'pass' ? 0 : 1);
