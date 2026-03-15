## RenderBridge — Implements the 14 engine_render_* WASM imports.
##
## Creates MeshInstance3D with primitive meshes, StandardMaterial3D,
## Light3D variants, and Camera3D — all tracked via HandleTable.
class_name RenderBridge
extends RefCounted

# Primitive type constants (must match Simple PrimitiveType enum)
const PRIM_CUBE := 0
const PRIM_SPHERE := 1
const PRIM_CYLINDER := 2
const PRIM_CAPSULE := 3
const PRIM_PLANE := 4
const PRIM_QUAD := 5

# Light type constants (must match Simple LightType enum)
const LIGHT_DIRECTIONAL := 0
const LIGHT_POINT := 1
const LIGHT_SPOT := 2

var _handles: HandleTable
var _scene_root: Node
var _wasm_memory: PackedByteArray

# Separate handle space for materials (not scene nodes)
var _mat_handles: HandleTable


func _init(handles: HandleTable, scene_root: Node) -> void:
	_handles = handles
	_scene_root = scene_root
	_mat_handles = HandleTable.new()


func set_memory(mem: PackedByteArray) -> void:
	_wasm_memory = mem


# --------------------------------------------------------------------------
# engine_render_set_mesh(entity: i32, mesh_type: i32)
# --------------------------------------------------------------------------
func set_mesh(entity: int, mesh_type: int) -> void:
	var node := _handles.get_node3d(entity)
	if node == null:
		return

	# Find or create a MeshInstance3D child
	var mi := _get_or_create_mesh_instance(node)
	mi.mesh = _create_primitive_mesh(mesh_type)


# --------------------------------------------------------------------------
# engine_render_set_mesh_asset(entity: i32, asset_id: i32)
# --------------------------------------------------------------------------
func set_mesh_asset(entity: int, asset_id: int) -> void:
	var node := _handles.get_node3d(entity)
	if node == null:
		return
	# asset_id should point to a loaded Mesh resource in the asset table.
	# The main bridge is responsible for resolving asset_id -> Resource.
	# Here we accept it as a handle from the main handle table.
	var asset_obj := _handles.get_obj(asset_id)
	if asset_obj is Mesh:
		var mi := _get_or_create_mesh_instance(node)
		mi.mesh = asset_obj as Mesh


# --------------------------------------------------------------------------
# engine_render_set_material(entity: i32, material_id: i32)
# --------------------------------------------------------------------------
func set_material(entity: int, material_id: int) -> void:
	var node := _handles.get_node3d(entity)
	if node == null:
		return
	var mat := _mat_handles.get_obj(material_id)
	if mat == null or not (mat is StandardMaterial3D):
		return

	var mi := _find_mesh_instance(node)
	if mi != null:
		mi.material_override = mat as StandardMaterial3D


# --------------------------------------------------------------------------
# engine_render_create_material() -> i32
# --------------------------------------------------------------------------
func create_material() -> int:
	var mat := StandardMaterial3D.new()
	return _mat_handles.add(mat)


# --------------------------------------------------------------------------
# engine_render_set_material_color(material: i32, r,g,b,a: f32)
# --------------------------------------------------------------------------
func set_material_color(material: int, r: float, g: float, b: float, a: float) -> void:
	var mat := _mat_handles.get_obj(material)
	if mat is StandardMaterial3D:
		var m := mat as StandardMaterial3D
		m.albedo_color = Color(r, g, b, a)
		if a < 1.0:
			m.transparency = BaseMaterial3D.TRANSPARENCY_ALPHA


# --------------------------------------------------------------------------
# engine_render_set_material_texture(material: i32, slot: i32, texture_id: i32)
# --------------------------------------------------------------------------
func set_material_texture(material: int, slot: int, texture_id: int) -> void:
	var mat := _mat_handles.get_obj(material)
	if not (mat is StandardMaterial3D):
		return
	var m := mat as StandardMaterial3D

	# texture_id should resolve to a Texture2D in the main handle table
	var tex_obj := _handles.get_obj(texture_id)
	if not (tex_obj is Texture2D):
		return
	var tex := tex_obj as Texture2D

	match slot:
		0:  # TEX_SLOT_ALBEDO
			m.albedo_texture = tex
		1:  # TEX_SLOT_NORMAL
			m.normal_enabled = true
			m.normal_texture = tex
		2:  # TEX_SLOT_ROUGHNESS
			m.roughness_texture = tex
		3:  # TEX_SLOT_METALLIC
			m.metallic_texture = tex
		4:  # TEX_SLOT_EMISSIVE
			m.emission_enabled = true
			m.emission_texture = tex


# --------------------------------------------------------------------------
# engine_render_set_material_float(material: i32, param: i32, value: f32)
# --------------------------------------------------------------------------
func set_material_float(material: int, param: int, value: float) -> void:
	var mat := _mat_handles.get_obj(material)
	if not (mat is StandardMaterial3D):
		return
	var m := mat as StandardMaterial3D

	match param:
		0:  # MAT_PARAM_ROUGHNESS
			m.roughness = value
		1:  # MAT_PARAM_METALLIC
			m.metallic = value
		2:  # MAT_PARAM_EMISSIVE
			m.emission_energy_multiplier = value


# --------------------------------------------------------------------------
# engine_render_create_light(light_type: i32) -> i32
# --------------------------------------------------------------------------
func create_light(light_type: int) -> int:
	var light: Light3D
	match light_type:
		LIGHT_DIRECTIONAL:
			light = DirectionalLight3D.new()
		LIGHT_POINT:
			light = OmniLight3D.new()
		LIGHT_SPOT:
			light = SpotLight3D.new()
		_:
			light = OmniLight3D.new()

	_scene_root.add_child(light)
	return _handles.add(light)


# --------------------------------------------------------------------------
# engine_render_set_light_color(light: i32, r,g,b: f32)
# --------------------------------------------------------------------------
func set_light_color(light_handle: int, r: float, g: float, b: float) -> void:
	var node := _handles.get_obj(light_handle)
	if node is Light3D:
		(node as Light3D).light_color = Color(r, g, b)


# --------------------------------------------------------------------------
# engine_render_set_light_intensity(light: i32, intensity: f32)
# --------------------------------------------------------------------------
func set_light_intensity(light_handle: int, intensity: float) -> void:
	var node := _handles.get_obj(light_handle)
	if node is Light3D:
		(node as Light3D).light_energy = intensity


# --------------------------------------------------------------------------
# engine_render_create_camera() -> i32
# --------------------------------------------------------------------------
func create_camera() -> int:
	var cam := Camera3D.new()
	_scene_root.add_child(cam)
	return _handles.add(cam)


# --------------------------------------------------------------------------
# engine_render_set_camera_fov(camera: i32, fov: f32)
# --------------------------------------------------------------------------
func set_camera_fov(camera_handle: int, fov: float) -> void:
	var node := _handles.get_obj(camera_handle)
	if node is Camera3D:
		(node as Camera3D).fov = fov


# --------------------------------------------------------------------------
# engine_render_set_camera_active(camera: i32, active: i32)
# --------------------------------------------------------------------------
func set_camera_active(camera_handle: int, active: int) -> void:
	var node := _handles.get_obj(camera_handle)
	if node is Camera3D:
		var cam := node as Camera3D
		if active != 0:
			cam.make_current()
		else:
			cam.clear_current()


# --------------------------------------------------------------------------
# engine_render_create_primitive(prim_type: i32) -> i32
# Creates a Node3D + MeshInstance3D child with the given primitive mesh.
# --------------------------------------------------------------------------
func create_primitive(prim_type: int) -> int:
	var node := Node3D.new()
	node.name = "Primitive_%d" % prim_type
	_scene_root.add_child(node)

	var mi := MeshInstance3D.new()
	mi.mesh = _create_primitive_mesh(prim_type)
	node.add_child(mi)

	return _handles.add(node)


# ============================================================================
# Helpers
# ============================================================================

func _create_primitive_mesh(prim_type: int) -> Mesh:
	match prim_type:
		PRIM_CUBE:
			return BoxMesh.new()
		PRIM_SPHERE:
			return SphereMesh.new()
		PRIM_CYLINDER:
			return CylinderMesh.new()
		PRIM_CAPSULE:
			return CapsuleMesh.new()
		PRIM_PLANE:
			return PlaneMesh.new()
		PRIM_QUAD:
			return QuadMesh.new()
		_:
			return BoxMesh.new()


func _get_or_create_mesh_instance(parent: Node3D) -> MeshInstance3D:
	var mi := _find_mesh_instance(parent)
	if mi != null:
		return mi
	mi = MeshInstance3D.new()
	parent.add_child(mi)
	return mi


func _find_mesh_instance(parent: Node3D) -> MeshInstance3D:
	for child in parent.get_children():
		if child is MeshInstance3D:
			return child as MeshInstance3D
	return null
