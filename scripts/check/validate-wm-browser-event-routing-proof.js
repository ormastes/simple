#!/usr/bin/env node
const fs = require('fs');

function clean(value) {
  if (value === undefined || value === null) return '';
  return String(value).replace(/[\r\n]/g, ' ');
}

function numberValue(value) {
  if (typeof value === 'number') return Number.isFinite(value) ? value : NaN;
  if (typeof value === 'string' && value.trim() !== '') return Number(value);
  return NaN;
}

function boolValue(value) {
  return value === true || value === 'true';
}

function min(value, required) {
  const n = numberValue(value);
  return Number.isFinite(n) && n >= required;
}

function equalsNumber(actual, expected) {
  const a = numberValue(actual);
  const e = numberValue(expected);
  return Number.isFinite(a) && Number.isFinite(e) && a === e;
}

function row(key, value) {
  console.log(`${key}=${clean(value)}`);
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
  ready: proof.ready,
  wm_found: proof.wm_found,
  window_cmd_count: proof.window_cmd_count,
  input_event_count: proof.input_event_count,
  focus_count: proof.focus_count,
  move_count: proof.move_count,
  maximize_count: proof.maximize_count,
  title_command_count: proof.title_command_count,
  text_input_count: proof.text_input_count,
  pointer_down_count: proof.pointer_down_count,
  pointer_up_count: proof.pointer_up_count,
  performance_now_available: proof.performance_now_available,
  performance_now_delta_ms: proof.performance_now_delta_ms,
  animation_frame_available: proof.animation_frame_available,
  animation_frame_count: proof.animation_frame_count,
  css_animation_probe: proof.css_animation_probe,
  title_text: proof.title_text,
  title_context_text: proof.title_context_text,
  traffic_button_count: proof.traffic_button_count,
  title_input_tag: proof.title_input_tag,
  titlebar_height: proof.titlebar_height,
  titlebar_display: proof.titlebar_display,
  titlebar_cursor: proof.titlebar_cursor,
  titlebar_background: proof.titlebar_background,
  title_color: proof.title_color,
  title_font_weight: proof.title_font_weight,
  title_input_min_width: proof.title_input_min_width,
  title_input_width: proof.title_input_width,
  title_input_width_px: proof.title_input_width_px,
  title_input_height: proof.title_input_height,
  title_input_cursor: proof.title_input_cursor,
  title_input_background: proof.title_input_background,
  close_button_background: proof.close_button_background,
  minimize_button_background: proof.minimize_button_background,
  maximize_button_background: proof.maximize_button_background,
  expected_move_x: proof.expected_move_x,
  expected_move_y: proof.expected_move_y,
  move_payload_x: move.x,
  move_payload_y: move.y,
  move_payload_source: move.source,
  move_payload_window_id_hint: move.window_id_hint,
  title_command_text: title.command_text,
  text_input_text: text.event ? text.event.text : undefined,
};

let reason = 'pass';
if (!boolValue(proof.pass)) {
  reason = 'probe-reported-fail';
} else if (!boolValue(proof.ready) || !boolValue(proof.wm_found)) {
  reason = 'event-routing-ready-missing';
} else if (
  !min(proof.focus_count, 1) ||
  !min(proof.move_count, 1) ||
  !min(proof.maximize_count, 1) ||
  !min(proof.title_command_count, 1) ||
  !min(proof.text_input_count, 1) ||
  !min(proof.pointer_down_count, 1) ||
  !min(proof.pointer_up_count, 1)
) {
  reason = 'event-routing-contract-missing';
} else if (
  !boolValue(proof.performance_now_available) ||
  !min(proof.performance_now_delta_ms, 0) ||
  !boolValue(proof.animation_frame_available) ||
  !min(proof.animation_frame_count, 2) ||
  !boolValue(proof.css_animation_probe)
) {
  reason = 'event-routing-performance-animation-contract-missing';
} else if (
  move.window_id_hint !== 'win1' ||
  move.source !== 'native_event' ||
  !equalsNumber(move.x, proof.expected_move_x) ||
  !equalsNumber(move.y, proof.expected_move_y) ||
  title.command_text !== '/tmp/project' ||
  !text.event ||
  text.event.text !== 'Hello Simple'
) {
  reason = 'event-routing-payload-contract-missing';
} else if (
  proof.title_text !== 'Terminal' ||
  proof.title_context_text !== 'terminal' ||
  !min(proof.traffic_button_count, 3) ||
  proof.title_input_tag !== 'input' ||
  proof.titlebar_height !== '34px' ||
  proof.titlebar_display !== 'flex' ||
  proof.titlebar_cursor !== 'grab' ||
  proof.titlebar_background !== 'rgb(229, 231, 235)' ||
  proof.title_color !== 'rgb(17, 24, 39)' ||
  !min(proof.title_font_weight, 700) ||
  proof.title_input_min_width !== '142px' ||
  !min(proof.title_input_width_px, 142) ||
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
