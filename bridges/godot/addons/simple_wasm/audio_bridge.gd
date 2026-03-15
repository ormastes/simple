## AudioBridge — Implements the 8 engine_audio_* WASM imports.
##
## Uses AudioStreamPlayer / AudioStreamPlayer3D for playback.
## Audio clips are loaded via ResourceLoader and tracked in an internal table.
class_name AudioBridge
extends RefCounted

var _scene_root: Node
var _wasm_memory: PackedByteArray

# audio_id -> Dictionary { "stream": AudioStream, "player": AudioStreamPlayer or AudioStreamPlayer3D }
var _clips: Dictionary = {}
var _next_id: int = 1


func _init(scene_root: Node) -> void:
	_scene_root = scene_root


func set_memory(mem: PackedByteArray) -> void:
	_wasm_memory = mem


# --------------------------------------------------------------------------
# engine_audio_load(path_ptr: i32, path_len: i32) -> i32
# --------------------------------------------------------------------------
func audio_load(path_ptr: int, path_len: int) -> int:
	var path := _read_string(path_ptr, path_len)
	if path.is_empty():
		return -1

	var stream := ResourceLoader.load(path) as AudioStream
	if stream == null:
		push_warning("AudioBridge: failed to load audio at '%s'" % path)
		return -1

	var id := _next_id
	_next_id += 1

	# Create a non-spatial player by default; set_spatial can upgrade it later.
	var player := AudioStreamPlayer.new()
	player.stream = stream
	_scene_root.add_child(player)

	_clips[id] = { "stream": stream, "player": player, "spatial": null }
	return id


# --------------------------------------------------------------------------
# engine_audio_play(audio_id: i32)
# --------------------------------------------------------------------------
func play(audio_id: int) -> void:
	var entry := _get_entry(audio_id)
	if entry == null:
		return
	# Prefer the spatial player if one exists
	if entry["spatial"] != null:
		(entry["spatial"] as AudioStreamPlayer3D).play()
	else:
		(entry["player"] as AudioStreamPlayer).play()


# --------------------------------------------------------------------------
# engine_audio_stop(audio_id: i32)
# --------------------------------------------------------------------------
func stop(audio_id: int) -> void:
	var entry := _get_entry(audio_id)
	if entry == null:
		return
	if entry["spatial"] != null:
		(entry["spatial"] as AudioStreamPlayer3D).stop()
	else:
		(entry["player"] as AudioStreamPlayer).stop()


# --------------------------------------------------------------------------
# engine_audio_set_volume(audio_id: i32, volume: f32)
# Volume is linear 0.0-1.0; convert to dB for Godot.
# --------------------------------------------------------------------------
func set_volume(audio_id: int, volume: float) -> void:
	var entry := _get_entry(audio_id)
	if entry == null:
		return
	var db := linear_to_db(clampf(volume, 0.0, 1.0))
	if entry["spatial"] != null:
		(entry["spatial"] as AudioStreamPlayer3D).volume_db = db
	else:
		(entry["player"] as AudioStreamPlayer).volume_db = db


# --------------------------------------------------------------------------
# engine_audio_set_pitch(audio_id: i32, pitch: f32)
# --------------------------------------------------------------------------
func set_pitch(audio_id: int, pitch: float) -> void:
	var entry := _get_entry(audio_id)
	if entry == null:
		return
	if entry["spatial"] != null:
		(entry["spatial"] as AudioStreamPlayer3D).pitch_scale = pitch
	else:
		(entry["player"] as AudioStreamPlayer).pitch_scale = pitch


# --------------------------------------------------------------------------
# engine_audio_set_spatial(audio_id: i32, entity: i32)
# Attaches (or re-attaches) the clip to a Node3D via AudioStreamPlayer3D.
# --------------------------------------------------------------------------
func set_spatial(audio_id: int, entity_handle: int, handles: HandleTable) -> void:
	var entry := _get_entry(audio_id)
	if entry == null:
		return
	var target := handles.get_node3d(entity_handle)
	if target == null:
		return

	# Create spatial player if it doesn't exist yet
	if entry["spatial"] == null:
		var spatial := AudioStreamPlayer3D.new()
		spatial.stream = entry["stream"] as AudioStream
		target.add_child(spatial)
		entry["spatial"] = spatial
		# Mute the non-spatial player
		(entry["player"] as AudioStreamPlayer).stop()
	else:
		# Re-parent to new entity
		var spatial := entry["spatial"] as AudioStreamPlayer3D
		if spatial.get_parent():
			spatial.get_parent().remove_child(spatial)
		target.add_child(spatial)


# --------------------------------------------------------------------------
# engine_audio_set_position(audio_id: i32, x: f32, y: f32, z: f32)
# For spatial audio: sets the global position directly.
# --------------------------------------------------------------------------
func set_position(audio_id: int, x: float, y: float, z: float) -> void:
	var entry := _get_entry(audio_id)
	if entry == null:
		return
	if entry["spatial"] != null:
		(entry["spatial"] as AudioStreamPlayer3D).global_position = Vector3(x, y, z)


# --------------------------------------------------------------------------
# engine_audio_is_playing(audio_id: i32) -> i32
# --------------------------------------------------------------------------
func is_playing(audio_id: int) -> int:
	var entry := _get_entry(audio_id)
	if entry == null:
		return 0
	if entry["spatial"] != null:
		return 1 if (entry["spatial"] as AudioStreamPlayer3D).playing else 0
	return 1 if (entry["player"] as AudioStreamPlayer).playing else 0


# ============================================================================
# Helpers
# ============================================================================

func _get_entry(audio_id: int) -> Variant:
	if _clips.has(audio_id):
		return _clips[audio_id]
	return null


func _read_string(ptr: int, length: int) -> String:
	if _wasm_memory.size() < ptr + length:
		return ""
	var slice := _wasm_memory.slice(ptr, ptr + length)
	return slice.get_string_from_utf8()
