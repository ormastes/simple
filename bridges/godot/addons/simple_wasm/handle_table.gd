## HandleTable — Maps i32 WASM handles to Godot Objects/Nodes.
##
## All engine_* bridge functions use i32 handles as entity/object references.
## This table owns the mapping; the WASM guest never sees Godot pointers.
class_name HandleTable
extends RefCounted

var _next_id: int = 1
var _table: Dictionary = {}  # int -> Object


## Add an object and return its new handle.
func add(obj: Object) -> int:
	var id := _next_id
	_next_id += 1
	_table[id] = obj
	return id


## Retrieve an object by handle.  Returns null if the handle is invalid.
func get_obj(handle: int) -> Object:
	if _table.has(handle):
		return _table[handle]
	return null


## Retrieve an object cast to Node3D.  Returns null if invalid or wrong type.
func get_node3d(handle: int) -> Node3D:
	var obj := get_obj(handle)
	if obj is Node3D:
		return obj as Node3D
	return null


## Remove a handle from the table and return the object (or null).
func remove(handle: int) -> Object:
	if _table.has(handle):
		var obj: Object = _table[handle]
		_table.erase(handle)
		return obj
	return null


## Check whether a handle exists.
func has(handle: int) -> bool:
	return _table.has(handle)


## Number of live handles.
func size() -> int:
	return _table.size()


## Clear all handles.
func clear() -> void:
	_table.clear()
	_next_id = 1
