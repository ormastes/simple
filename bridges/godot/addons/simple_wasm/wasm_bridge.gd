## WasmBridge — Main EditorPlugin / runtime node for loading Simple-compiled
## WASM modules and bridging all 68 engine_* ABI functions to Godot.
##
## Usage:
##   1. Enable the "Simple WASM Bridge" plugin in Project Settings > Plugins.
##   2. Add a WasmBridge node to your scene.
##   3. Set the `wasm_path` export to your compiled .wasm file.
##   4. The bridge calls game_init(), game_update(dt), game_shutdown() automatically.
##
## Hot-reload: monitors the .wasm file's modification time and reloads on change.
@tool
extends EditorPlugin

## ============================================================================
## WasmBridgeNode — the runtime node added to scenes
## ============================================================================

class WasmBridgeNode:
	extends Node

	## Path to the compiled .wasm file (relative to res:// or absolute).
	@export_file("*.wasm") var wasm_path: String = ""

	## Enable hot-reload (watches file modification time).
	@export var hot_reload: bool = true

	## How often to check for file changes (seconds).
	@export var reload_interval: float = 1.0

	# -- Sub-bridges --
	var _handles: HandleTable
	var _input_bridge: InputBridge
	var _physics_bridge: PhysicsBridge
	var _audio_bridge: AudioBridge
	var _render_bridge: RenderBridge

	# -- WASM runtime (placeholder interface) --
	# In production this would be a GDExtension binding to wasmtime/wasmer.
	# The placeholder exposes the same API so all bridge wiring is real.
	var _wasm_instance: RefCounted = null  # WasmInstance from GDExtension
	var _wasm_memory: PackedByteArray = PackedByteArray()

	# -- Hot-reload state --
	var _last_mod_time: int = 0
	var _reload_timer: float = 0.0

	# -- Lifecycle flags --
	var _initialized: bool = false


	func _ready() -> void:
		_handles = HandleTable.new()
		_input_bridge = InputBridge.new(get_viewport())
		_physics_bridge = PhysicsBridge.new(_handles, self)
		_audio_bridge = AudioBridge.new(self)
		_render_bridge = RenderBridge.new(_handles, self)

		if not wasm_path.is_empty():
			_load_wasm(wasm_path)


	func _process(delta: float) -> void:
		if not _initialized:
			return

		# Hot-reload check
		if hot_reload:
			_reload_timer += delta
			if _reload_timer >= reload_interval:
				_reload_timer = 0.0
				_check_hot_reload()

		# Poll input before calling game logic
		_input_bridge.poll()

		# Call game_update(delta) in the WASM module
		_call_wasm("game_update", [delta])


	func _exit_tree() -> void:
		if _initialized:
			_call_wasm("game_shutdown", [])
			_initialized = false
		_cleanup()


	# ======================================================================
	# WASM Loading
	# ======================================================================

	func _load_wasm(path: String) -> void:
		if _initialized:
			_call_wasm("game_shutdown", [])
			_cleanup()

		var abs_path := path
		if path.begins_with("res://"):
			abs_path = ProjectSettings.globalize_path(path)

		if not FileAccess.file_exists(abs_path) and not FileAccess.file_exists(path):
			push_error("WasmBridge: WASM file not found: %s" % path)
			return

		# Record modification time for hot-reload
		_last_mod_time = _get_file_mod_time(abs_path)

		# --- WASM instantiation (placeholder) ---
		# In a real implementation, this would be:
		#   var engine := WasmEngine.new()
		#   var module := engine.compile_file(abs_path)
		#   _wasm_instance = engine.instantiate(module, _build_imports())
		#   _wasm_memory = _wasm_instance.get_memory("memory")
		#
		# For now we create a placeholder that logs calls.
		_wasm_instance = _create_placeholder_instance()
		_wasm_memory.resize(65536)  # 1 page = 64 KiB

		# Share memory with sub-bridges
		_input_bridge.set_memory(_wasm_memory)
		_physics_bridge.set_memory(_wasm_memory)
		_audio_bridge.set_memory(_wasm_memory)
		_render_bridge.set_memory(_wasm_memory)

		_initialized = true
		print("WasmBridge: loaded %s" % path)

		# Call game_init()
		_call_wasm("game_init", [])


	func _cleanup() -> void:
		# Free all tracked nodes
		for key in _handles._table:
			var obj: Object = _handles._table[key]
			if obj is Node and is_instance_valid(obj):
				(obj as Node).queue_free()
		_handles.clear()
		_wasm_instance = null
		_initialized = false


	# ======================================================================
	# Hot-Reload
	# ======================================================================

	func _check_hot_reload() -> void:
		if wasm_path.is_empty():
			return
		var abs_path := wasm_path
		if wasm_path.begins_with("res://"):
			abs_path = ProjectSettings.globalize_path(wasm_path)

		var current_mod := _get_file_mod_time(abs_path)
		if current_mod > _last_mod_time and current_mod > 0:
			print("WasmBridge: hot-reload detected, reloading %s" % wasm_path)
			_load_wasm(wasm_path)


	func _get_file_mod_time(path: String) -> int:
		if FileAccess.file_exists(path):
			return FileAccess.get_modified_time(path)
		return 0


	# ======================================================================
	# WASM Import Registration — all 68 engine_* functions
	# ======================================================================

	## Build the import dictionary that maps WASM import names to callables.
	## This is passed to the WASM runtime during instantiation.
	func _build_imports() -> Dictionary:
		var imports := {}

		# -- Entity Management (8) --
		imports["engine_entity_create"] = _engine_entity_create
		imports["engine_entity_create_named"] = _engine_entity_create_named
		imports["engine_entity_destroy"] = _engine_entity_destroy
		imports["engine_entity_set_active"] = _engine_entity_set_active
		imports["engine_entity_is_active"] = _engine_entity_is_active
		imports["engine_entity_set_parent"] = _engine_entity_set_parent
		imports["engine_entity_set_name"] = _engine_entity_set_name
		imports["engine_entity_find_by_name"] = _engine_entity_find_by_name

		# -- Transform (12) --
		imports["engine_transform_get_position"] = _engine_transform_get_position
		imports["engine_transform_set_position"] = _engine_transform_set_position
		imports["engine_transform_get_rotation"] = _engine_transform_get_rotation
		imports["engine_transform_set_rotation"] = _engine_transform_set_rotation
		imports["engine_transform_get_scale"] = _engine_transform_get_scale
		imports["engine_transform_set_scale"] = _engine_transform_set_scale
		imports["engine_transform_look_at"] = _engine_transform_look_at
		imports["engine_transform_translate"] = _engine_transform_translate
		imports["engine_transform_rotate"] = _engine_transform_rotate
		imports["engine_transform_get_forward"] = _engine_transform_get_forward
		imports["engine_transform_get_up"] = _engine_transform_get_up
		imports["engine_transform_get_right"] = _engine_transform_get_right

		# -- Rendering (14) --
		imports["engine_render_set_mesh"] = _render_bridge.set_mesh
		imports["engine_render_set_mesh_asset"] = _render_bridge.set_mesh_asset
		imports["engine_render_set_material"] = _render_bridge.set_material
		imports["engine_render_create_material"] = _render_bridge.create_material
		imports["engine_render_set_material_color"] = _render_bridge.set_material_color
		imports["engine_render_set_material_texture"] = _render_bridge.set_material_texture
		imports["engine_render_set_material_float"] = _render_bridge.set_material_float
		imports["engine_render_create_light"] = _render_bridge.create_light
		imports["engine_render_set_light_color"] = _render_bridge.set_light_color
		imports["engine_render_set_light_intensity"] = _render_bridge.set_light_intensity
		imports["engine_render_create_camera"] = _render_bridge.create_camera
		imports["engine_render_set_camera_fov"] = _render_bridge.set_camera_fov
		imports["engine_render_set_camera_active"] = _render_bridge.set_camera_active
		imports["engine_render_create_primitive"] = _render_bridge.create_primitive

		# -- Input (8) --
		imports["engine_input_is_key_pressed"] = _input_bridge.is_key_pressed
		imports["engine_input_is_key_just_pressed"] = _input_bridge.is_key_just_pressed
		imports["engine_input_is_key_just_released"] = _input_bridge.is_key_just_released
		imports["engine_input_get_mouse_position"] = _input_bridge.get_mouse_position
		imports["engine_input_get_mouse_delta"] = _input_bridge.get_mouse_delta
		imports["engine_input_is_mouse_button_pressed"] = _input_bridge.is_mouse_button_pressed
		imports["engine_input_get_axis"] = _input_bridge.get_axis
		imports["engine_input_is_action_pressed"] = _input_bridge.is_action_pressed

		# -- Physics (12) --
		imports["engine_physics_add_rigidbody"] = _physics_bridge.add_rigidbody
		imports["engine_physics_set_mass"] = _physics_bridge.set_mass
		imports["engine_physics_set_velocity"] = _physics_bridge.set_velocity
		imports["engine_physics_get_velocity"] = _physics_bridge.get_velocity
		imports["engine_physics_add_force"] = _physics_bridge.add_force
		imports["engine_physics_add_impulse"] = _physics_bridge.add_impulse
		imports["engine_physics_add_collider_box"] = _physics_bridge.add_collider_box
		imports["engine_physics_add_collider_sphere"] = _physics_bridge.add_collider_sphere
		imports["engine_physics_add_collider_capsule"] = _physics_bridge.add_collider_capsule
		imports["engine_physics_raycast"] = _physics_bridge.raycast
		imports["engine_physics_set_gravity"] = _physics_bridge.set_gravity
		imports["engine_physics_set_collision_layer"] = _physics_bridge.set_collision_layer

		# -- Audio (8) --
		imports["engine_audio_load"] = _audio_bridge.audio_load
		imports["engine_audio_play"] = _audio_bridge.play
		imports["engine_audio_stop"] = _audio_bridge.stop
		imports["engine_audio_set_volume"] = _audio_bridge.set_volume
		imports["engine_audio_set_pitch"] = _audio_bridge.set_pitch
		imports["engine_audio_set_spatial"] = func(audio_id: int, entity: int) -> void:
			_audio_bridge.set_spatial(audio_id, entity, _handles)
		imports["engine_audio_set_position"] = _audio_bridge.set_position
		imports["engine_audio_is_playing"] = _audio_bridge.is_playing

		# -- Asset (4) --
		imports["engine_asset_load"] = _engine_asset_load
		imports["engine_asset_is_loaded"] = _engine_asset_is_loaded
		imports["engine_asset_unload"] = _engine_asset_unload
		imports["engine_asset_load_texture"] = _engine_asset_load_texture

		# -- Debug (2) --
		imports["engine_debug_log"] = _engine_debug_log
		imports["engine_debug_draw_line"] = _engine_debug_draw_line

		return imports


	# ======================================================================
	# Entity Management Implementations
	# ======================================================================

	func _engine_entity_create() -> int:
		var node := Node3D.new()
		node.name = "Entity_%d" % _handles._next_id
		add_child(node)
		return _handles.add(node)


	func _engine_entity_create_named(name_ptr: int, name_len: int) -> int:
		var entity_name := _read_wasm_string(name_ptr, name_len)
		var node := Node3D.new()
		node.name = entity_name if not entity_name.is_empty() else "Entity_%d" % _handles._next_id
		add_child(node)
		return _handles.add(node)


	func _engine_entity_destroy(entity: int) -> void:
		var obj := _handles.remove(entity)
		if obj is Node and is_instance_valid(obj):
			(obj as Node).queue_free()


	func _engine_entity_set_active(entity: int, active: int) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			node.visible = (active != 0)
			node.set_process(active != 0)
			node.set_physics_process(active != 0)


	func _engine_entity_is_active(entity: int) -> int:
		var node := _handles.get_node3d(entity)
		if node != null:
			return 1 if node.visible else 0
		return 0


	func _engine_entity_set_parent(entity: int, parent_handle: int) -> void:
		var node := _handles.get_node3d(entity)
		var parent_node := _handles.get_node3d(parent_handle)
		if node != null and parent_node != null:
			if node.get_parent():
				node.get_parent().remove_child(node)
			parent_node.add_child(node)


	func _engine_entity_set_name(entity: int, name_ptr: int, name_len: int) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			var n := _read_wasm_string(name_ptr, name_len)
			if not n.is_empty():
				node.name = n


	func _engine_entity_find_by_name(name_ptr: int, name_len: int) -> int:
		var target_name := _read_wasm_string(name_ptr, name_len)
		if target_name.is_empty():
			return -1
		for key in _handles._table:
			var obj: Object = _handles._table[key]
			if obj is Node and (obj as Node).name == target_name:
				return key
		return -1


	# ======================================================================
	# Transform Implementations
	# ======================================================================

	func _engine_transform_get_position(entity: int, out_ptr: int) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			_write_vec3(out_ptr, node.global_position)


	func _engine_transform_set_position(entity: int, x: float, y: float, z: float) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			node.global_position = Vector3(x, y, z)


	func _engine_transform_get_rotation(entity: int, out_ptr: int) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			var q := node.quaternion
			_write_f32(out_ptr, q.x)
			_write_f32(out_ptr + 4, q.y)
			_write_f32(out_ptr + 8, q.z)
			_write_f32(out_ptr + 12, q.w)


	func _engine_transform_set_rotation(entity: int, x: float, y: float, z: float, w: float) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			node.quaternion = Quaternion(x, y, z, w)


	func _engine_transform_get_scale(entity: int, out_ptr: int) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			_write_vec3(out_ptr, node.scale)


	func _engine_transform_set_scale(entity: int, x: float, y: float, z: float) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			node.scale = Vector3(x, y, z)


	func _engine_transform_look_at(entity: int, x: float, y: float, z: float) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			var target := Vector3(x, y, z)
			if not node.global_position.is_equal_approx(target):
				node.look_at(target, Vector3.UP)


	func _engine_transform_translate(entity: int, dx: float, dy: float, dz: float) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			node.global_position += Vector3(dx, dy, dz)


	func _engine_transform_rotate(entity: int, axis_x: float, axis_y: float, axis_z: float, angle: float) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			var axis := Vector3(axis_x, axis_y, axis_z).normalized()
			if axis.length_squared() > 0.001:
				node.rotate(axis, angle)


	func _engine_transform_get_forward(entity: int, out_ptr: int) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			_write_vec3(out_ptr, -node.global_basis.z)


	func _engine_transform_get_up(entity: int, out_ptr: int) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			_write_vec3(out_ptr, node.global_basis.y)


	func _engine_transform_get_right(entity: int, out_ptr: int) -> void:
		var node := _handles.get_node3d(entity)
		if node != null:
			_write_vec3(out_ptr, node.global_basis.x)


	# ======================================================================
	# Asset Management Implementations
	# ======================================================================

	func _engine_asset_load(path_ptr: int, path_len: int, asset_type: int) -> int:
		var path := _read_wasm_string(path_ptr, path_len)
		if path.is_empty():
			return -1
		var resource := ResourceLoader.load(path)
		if resource == null:
			push_warning("WasmBridge: failed to load asset '%s'" % path)
			return -1
		return _handles.add(resource)


	func _engine_asset_is_loaded(asset_id: int) -> int:
		# Synchronous loading — if the handle exists, it's loaded.
		return 1 if _handles.has(asset_id) else 0


	func _engine_asset_unload(asset_id: int) -> void:
		_handles.remove(asset_id)


	func _engine_asset_load_texture(path_ptr: int, path_len: int) -> int:
		var path := _read_wasm_string(path_ptr, path_len)
		if path.is_empty():
			return -1
		var tex := ResourceLoader.load(path) as Texture2D
		if tex == null:
			push_warning("WasmBridge: failed to load texture '%s'" % path)
			return -1
		return _handles.add(tex)


	# ======================================================================
	# Debug Implementations
	# ======================================================================

	func _engine_debug_log(msg_ptr: int, msg_len: int) -> void:
		var msg := _read_wasm_string(msg_ptr, msg_len)
		print("[WASM] %s" % msg)


	func _engine_debug_draw_line(x1: float, y1: float, z1: float,
			x2: float, y2: float, z2: float,
			r: float, g: float, b: float) -> void:
		# Use DebugDraw3D if available, otherwise ImmediateMesh fallback.
		# For now, log the draw call (visual debug drawing requires a
		# persistent ImmediateMesh node or a plugin like DebugDraw3D).
		var from := Vector3(x1, y1, z1)
		var to := Vector3(x2, y2, z2)
		var color := Color(r, g, b)

		# Create a one-frame debug line using an ImmediateMesh
		var im := ImmediateMesh.new()
		im.surface_begin(Mesh.PRIMITIVE_LINES)
		im.surface_set_color(color)
		im.surface_add_vertex(from)
		im.surface_add_vertex(to)
		im.surface_end()

		var mi := MeshInstance3D.new()
		mi.mesh = im
		mi.cast_shadow = GeometryInstance3D.SHADOW_CASTING_SETTING_OFF
		add_child(mi)

		# Auto-remove after one frame
		get_tree().create_timer(0.0).timeout.connect(func() -> void:
			if is_instance_valid(mi):
				mi.queue_free()
		)


	# ======================================================================
	# WASM Memory Helpers
	# ======================================================================

	func _read_wasm_string(ptr: int, length: int) -> String:
		if _wasm_memory.size() < ptr + length or length <= 0:
			return ""
		var slice := _wasm_memory.slice(ptr, ptr + length)
		return slice.get_string_from_utf8()


	func _write_f32(offset: int, value: float) -> void:
		if _wasm_memory.size() > offset + 3:
			var buf := PackedFloat32Array([value])
			var bytes := buf.to_byte_array()
			for i in 4:
				_wasm_memory[offset + i] = bytes[i]


	func _write_vec3(offset: int, v: Vector3) -> void:
		_write_f32(offset, v.x)
		_write_f32(offset + 4, v.y)
		_write_f32(offset + 8, v.z)


	# ======================================================================
	# WASM Call Dispatcher (placeholder)
	# ======================================================================

	func _call_wasm(func_name: String, args: Array) -> Variant:
		if _wasm_instance == null:
			return null
		# In production:
		#   return _wasm_instance.call_function(func_name, args)
		# Placeholder: just log
		if OS.is_debug_build():
			pass  # Suppress noisy per-frame logging; uncomment for debugging:
			# print("WasmBridge: call %s(%s)" % [func_name, str(args)])
		return null


	func _create_placeholder_instance() -> RefCounted:
		# Returns a dummy RefCounted. Replace with actual wasmtime GDExtension.
		return RefCounted.new()


# ============================================================================
# EditorPlugin lifecycle
# ============================================================================

func _enter_tree() -> void:
	add_custom_type(
		"WasmBridge",
		"Node",
		preload("wasm_bridge.gd").WasmBridgeNode,
		preload("res://addons/simple_wasm/icon.svg") if FileAccess.file_exists("res://addons/simple_wasm/icon.svg") else null
	)


func _exit_tree() -> void:
	remove_custom_type("WasmBridge")
