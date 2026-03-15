## InputBridge — Implements the 8 engine_input_* WASM imports using Godot's
## Input singleton and viewport mouse queries.
##
## Key codes follow the Simple KeyCode enum which maps 1:1 to Godot's Key enum.
class_name InputBridge
extends RefCounted

var _wasm_memory: PackedByteArray  # reference kept for out-pointer writes
var _viewport: Viewport
var _prev_mouse_pos: Vector2 = Vector2.ZERO
var _mouse_delta: Vector2 = Vector2.ZERO


func _init(viewport: Viewport) -> void:
	_viewport = viewport


## Call once per frame before dispatching game_update so delta is fresh.
func poll() -> void:
	var current := _viewport.get_mouse_position()
	_mouse_delta = current - _prev_mouse_pos
	_prev_mouse_pos = current


## Bind the shared WASM linear memory so out-pointer writes land correctly.
func set_memory(mem: PackedByteArray) -> void:
	_wasm_memory = mem


# --------------------------------------------------------------------------
# engine_input_is_key_pressed(key_code: i32) -> i32
# --------------------------------------------------------------------------
func is_key_pressed(key_code: int) -> int:
	return 1 if Input.is_key_pressed(key_code as Key) else 0


# --------------------------------------------------------------------------
# engine_input_is_key_just_pressed(key_code: i32) -> i32
# --------------------------------------------------------------------------
func is_key_just_pressed(key_code: int) -> int:
	return 1 if Input.is_key_pressed(key_code as Key) and not Input.is_action_just_released(&"") else 0


# --------------------------------------------------------------------------
# engine_input_is_key_just_released(key_code: i32) -> i32
# --------------------------------------------------------------------------
func is_key_just_released(key_code: int) -> int:
	# Godot doesn't expose per-key "just released" directly.
	# The recommended approach is to track state yourself or use Input actions.
	# Placeholder: always returns 0; override via InputMap actions for accuracy.
	return 0


# --------------------------------------------------------------------------
# engine_input_get_mouse_position(out_ptr: i32)
# Writes two f32 values (x, y) at out_ptr in WASM memory.
# --------------------------------------------------------------------------
func get_mouse_position(out_ptr: int) -> void:
	var pos := _viewport.get_mouse_position()
	_write_f32(out_ptr, pos.x)
	_write_f32(out_ptr + 4, pos.y)


# --------------------------------------------------------------------------
# engine_input_get_mouse_delta(out_ptr: i32)
# Writes two f32 values (dx, dy) at out_ptr in WASM memory.
# --------------------------------------------------------------------------
func get_mouse_delta(out_ptr: int) -> void:
	_write_f32(out_ptr, _mouse_delta.x)
	_write_f32(out_ptr + 4, _mouse_delta.y)


# --------------------------------------------------------------------------
# engine_input_is_mouse_button_pressed(button: i32) -> i32
# --------------------------------------------------------------------------
func is_mouse_button_pressed(button: int) -> int:
	return 1 if Input.is_mouse_button_pressed(button as MouseButton) else 0


# --------------------------------------------------------------------------
# engine_input_get_axis(axis_name_ptr: i32, axis_name_len: i32) -> f32
# --------------------------------------------------------------------------
func get_axis(axis_name_ptr: int, axis_name_len: int) -> float:
	var name_str := _read_string(axis_name_ptr, axis_name_len)
	if InputMap.has_action(name_str):
		return Input.get_axis(name_str + "_negative", name_str + "_positive")
	# Fallback: treat as a single action strength
	if InputMap.has_action(name_str):
		return Input.get_action_strength(name_str)
	return 0.0


# --------------------------------------------------------------------------
# engine_input_is_action_pressed(action_ptr: i32, action_len: i32) -> i32
# --------------------------------------------------------------------------
func is_action_pressed(action_ptr: int, action_len: int) -> int:
	var action_str := _read_string(action_ptr, action_len)
	if InputMap.has_action(action_str):
		return 1 if Input.is_action_pressed(action_str) else 0
	return 0


# ============================================================================
# Helpers
# ============================================================================

func _write_f32(offset: int, value: float) -> void:
	if _wasm_memory.size() > offset + 3:
		var buf := PackedFloat32Array([value])
		var bytes := buf.to_byte_array()
		for i in 4:
			_wasm_memory[offset + i] = bytes[i]


func _read_string(ptr: int, length: int) -> String:
	if _wasm_memory.size() < ptr + length:
		return ""
	var slice := _wasm_memory.slice(ptr, ptr + length)
	return slice.get_string_from_utf8()
