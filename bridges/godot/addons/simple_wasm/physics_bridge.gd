## PhysicsBridge — Implements the 12 engine_physics_* WASM imports.
##
## Maps entity handles to Godot RigidBody3D / StaticBody3D / CharacterBody3D
## nodes, and manages CollisionShape3D children for colliders.
class_name PhysicsBridge
extends RefCounted

const BODY_STATIC := 0
const BODY_KINEMATIC := 1
const BODY_DYNAMIC := 2

var _handles: HandleTable
var _scene_root: Node
var _wasm_memory: PackedByteArray


func _init(handles: HandleTable, scene_root: Node) -> void:
	_handles = handles
	_scene_root = scene_root


func set_memory(mem: PackedByteArray) -> void:
	_wasm_memory = mem


# --------------------------------------------------------------------------
# engine_physics_add_rigidbody(entity: i32, body_type: i32)
# --------------------------------------------------------------------------
func add_rigidbody(entity: int, body_type: int) -> void:
	var node := _handles.get_node3d(entity)
	if node == null:
		return
	# If the node is a plain Node3D, we need to replace it with a physics body.
	# Strategy: create a physics body, reparent children, swap in handle table.
	var body: PhysicsBody3D
	match body_type:
		BODY_STATIC:
			body = StaticBody3D.new()
		BODY_KINEMATIC:
			body = CharacterBody3D.new()
		BODY_DYNAMIC, _:
			body = RigidBody3D.new()

	body.name = node.name
	body.transform = node.transform

	# Move existing children to the new body
	for child in node.get_children():
		node.remove_child(child)
		body.add_child(child)

	# Swap in scene tree
	var parent := node.get_parent()
	if parent:
		parent.add_child(body)
		parent.remove_child(node)
	else:
		_scene_root.add_child(body)

	node.queue_free()

	# Update handle table to point at the new body
	_handles._table[entity] = body


# --------------------------------------------------------------------------
# engine_physics_set_mass(entity: i32, mass: f32)
# --------------------------------------------------------------------------
func set_mass(entity: int, mass: float) -> void:
	var node := _handles.get_obj(entity)
	if node is RigidBody3D:
		(node as RigidBody3D).mass = mass


# --------------------------------------------------------------------------
# engine_physics_set_velocity(entity: i32, vx: f32, vy: f32, vz: f32)
# --------------------------------------------------------------------------
func set_velocity(entity: int, vx: float, vy: float, vz: float) -> void:
	var node := _handles.get_obj(entity)
	if node is RigidBody3D:
		(node as RigidBody3D).linear_velocity = Vector3(vx, vy, vz)
	elif node is CharacterBody3D:
		(node as CharacterBody3D).velocity = Vector3(vx, vy, vz)


# --------------------------------------------------------------------------
# engine_physics_get_velocity(entity: i32, out_ptr: i32)
# Writes 3 x f32 at out_ptr.
# --------------------------------------------------------------------------
func get_velocity(entity: int, out_ptr: int) -> void:
	var vel := Vector3.ZERO
	var node := _handles.get_obj(entity)
	if node is RigidBody3D:
		vel = (node as RigidBody3D).linear_velocity
	elif node is CharacterBody3D:
		vel = (node as CharacterBody3D).velocity
	_write_vec3(out_ptr, vel)


# --------------------------------------------------------------------------
# engine_physics_add_force(entity: i32, fx: f32, fy: f32, fz: f32)
# --------------------------------------------------------------------------
func add_force(entity: int, fx: float, fy: float, fz: float) -> void:
	var node := _handles.get_obj(entity)
	if node is RigidBody3D:
		(node as RigidBody3D).apply_force(Vector3(fx, fy, fz))


# --------------------------------------------------------------------------
# engine_physics_add_impulse(entity: i32, ix: f32, iy: f32, iz: f32)
# --------------------------------------------------------------------------
func add_impulse(entity: int, ix: float, iy: float, iz: float) -> void:
	var node := _handles.get_obj(entity)
	if node is RigidBody3D:
		(node as RigidBody3D).apply_impulse(Vector3(ix, iy, iz))


# --------------------------------------------------------------------------
# engine_physics_add_collider_box(entity: i32, hx: f32, hy: f32, hz: f32)
# --------------------------------------------------------------------------
func add_collider_box(entity: int, hx: float, hy: float, hz: float) -> void:
	var node := _handles.get_node3d(entity)
	if node == null:
		return
	var shape := BoxShape3D.new()
	shape.size = Vector3(hx * 2.0, hy * 2.0, hz * 2.0)
	var col := CollisionShape3D.new()
	col.shape = shape
	node.add_child(col)


# --------------------------------------------------------------------------
# engine_physics_add_collider_sphere(entity: i32, radius: f32)
# --------------------------------------------------------------------------
func add_collider_sphere(entity: int, radius: float) -> void:
	var node := _handles.get_node3d(entity)
	if node == null:
		return
	var shape := SphereShape3D.new()
	shape.radius = radius
	var col := CollisionShape3D.new()
	col.shape = shape
	node.add_child(col)


# --------------------------------------------------------------------------
# engine_physics_add_collider_capsule(entity: i32, radius: f32, height: f32)
# --------------------------------------------------------------------------
func add_collider_capsule(entity: int, radius: float, height: float) -> void:
	var node := _handles.get_node3d(entity)
	if node == null:
		return
	var shape := CapsuleShape3D.new()
	shape.radius = radius
	shape.height = height
	var col := CollisionShape3D.new()
	col.shape = shape
	node.add_child(col)


# --------------------------------------------------------------------------
# engine_physics_raycast(ox,oy,oz, dx,dy,dz, max_dist, out_ptr) -> i32
# Writes [entity_id, px,py,pz, nx,ny,nz, distance] (8 x f32) at out_ptr.
# Returns 1 on hit, 0 on miss.
# --------------------------------------------------------------------------
func raycast(ox: float, oy: float, oz: float,
		dx: float, dy: float, dz: float,
		max_dist: float, out_ptr: int) -> int:
	var space := _scene_root.get_viewport().world_3d.direct_space_state
	if space == null:
		return 0

	var origin := Vector3(ox, oy, oz)
	var direction := Vector3(dx, dy, dz).normalized()
	var end := origin + direction * max_dist

	var query := PhysicsRayQueryParameters3D.create(origin, end)
	var result := space.intersect_ray(query)

	if result.is_empty():
		return 0

	var hit_pos: Vector3 = result["position"]
	var hit_normal: Vector3 = result["normal"]
	var collider: Object = result["collider"]
	var distance := origin.distance_to(hit_pos)

	# Find the handle for the collider (or its parent)
	var entity_id: float = -1.0
	if collider is Node3D:
		# Search handle table for this node or its ancestors
		var node: Node = collider as Node
		while node != null:
			for key in _handles._table:
				if _handles._table[key] == node:
					entity_id = float(key)
					break
			if entity_id >= 0.0:
				break
			node = node.get_parent()

	_write_f32(out_ptr,      entity_id)
	_write_f32(out_ptr + 4,  hit_pos.x)
	_write_f32(out_ptr + 8,  hit_pos.y)
	_write_f32(out_ptr + 12, hit_pos.z)
	_write_f32(out_ptr + 16, hit_normal.x)
	_write_f32(out_ptr + 20, hit_normal.y)
	_write_f32(out_ptr + 24, hit_normal.z)
	_write_f32(out_ptr + 28, distance)
	return 1


# --------------------------------------------------------------------------
# engine_physics_set_gravity(gx: f32, gy: f32, gz: f32)
# --------------------------------------------------------------------------
func set_gravity(gx: float, gy: float, gz: float) -> void:
	PhysicsServer3D.area_set_param(
		_scene_root.get_viewport().world_3d.space,
		PhysicsServer3D.AREA_PARAM_GRAVITY_VECTOR,
		Vector3(gx, gy, gz)
	)


# --------------------------------------------------------------------------
# engine_physics_set_collision_layer(entity: i32, layer: i32, mask: i32)
# --------------------------------------------------------------------------
func set_collision_layer(entity: int, layer: int, mask: int) -> void:
	var node := _handles.get_obj(entity)
	if node is PhysicsBody3D:
		var body := node as PhysicsBody3D
		body.collision_layer = layer
		body.collision_mask = mask


# ============================================================================
# Helpers
# ============================================================================

func _write_vec3(offset: int, v: Vector3) -> void:
	_write_f32(offset, v.x)
	_write_f32(offset + 4, v.y)
	_write_f32(offset + 8, v.z)


func _write_f32(offset: int, value: float) -> void:
	if _wasm_memory.size() > offset + 3:
		var buf := PackedFloat32Array([value])
		var bytes := buf.to_byte_array()
		for i in 4:
			_wasm_memory[offset + i] = bytes[i]
