# Direct FFI Calls Without Wrappers - Audit Report

## Summary

This report identifies all direct calls to FFI functions (rt_*) that should ideally use wrapper functions following the two-tier pattern.

## FFI Call Analysis

### Direct FFI Calls by File


#### `rust/lib/std/src/browser.disabled/dom.spl`

- **Line 212**: `rt_before()`
  ```simple
  fn insert_before(new_node: Element, ref_node: Element):
  ```

#### `rust/lib/std/src/browser.disabled/fetch.spl`

- **Line 404**: `rt_after()`
  ```simple
  fn abort_after(controller: AbortController, ms: i64):
  ```

#### `rust/lib/std/src/cli/file.spl`

- **Line 295**: `rt_loading()`
  ```simple
  handle.start_loading()
  ```
- **Line 309**: `rt_loading()`
  ```simple
  handle.start_loading()
  ```
- **Line 323**: `rt_file_exists()`
  ```simple
  return rt_file_exists(path)
  ```
- **Line 326**: `rt_file_exists()`
  ```simple
  val does_exist = rt_file_exists(path)
  ```
- **Line 342**: `rt_file_canonicalize()`
  ```simple
  return rt_file_canonicalize(path)
  ```

#### `rust/lib/std/src/cli/parser.spl`

- **Line 295**: `rt_matches()`
  ```simple
  val name = parts[0].trim_start_matches("--")
  ```
- **Line 320**: `rt_matches()`
  ```simple
  val name = arg.trim_start_matches("--")
  ```
- **Line 485**: `rt_loading()`
  ```simple
  handle.start_loading()
  ```

#### `rust/lib/std/src/collections/btreemap.spl`

- **Line 100**: `rt_btreemap_new()`
  ```simple
  extern fn __rt_btreemap_new() -> any
  ```
- **Line 101**: `rt_btreemap_insert()`
  ```simple
  extern fn __rt_btreemap_insert(handle: any, key: any, value: any) -> bool
  ```
- **Line 102**: `rt_btreemap_get()`
  ```simple
  extern fn __rt_btreemap_get(handle: any, key: any) -> any
  ```
- **Line 103**: `rt_btreemap_contains_key()`
  ```simple
  extern fn __rt_btreemap_contains_key(handle: any, key: any) -> bool
  ```
- **Line 104**: `rt_btreemap_remove()`
  ```simple
  extern fn __rt_btreemap_remove(handle: any, key: any) -> any
  ```
- **Line 105**: `rt_btreemap_len()`
  ```simple
  extern fn __rt_btreemap_len(handle: any) -> i64
  ```
- **Line 106**: `rt_btreemap_clear()`
  ```simple
  extern fn __rt_btreemap_clear(handle: any) -> bool
  ```
- **Line 107**: `rt_btreemap_keys()`
  ```simple
  extern fn __rt_btreemap_keys(handle: any) -> [any]
  ```
- **Line 108**: `rt_btreemap_values()`
  ```simple
  extern fn __rt_btreemap_values(handle: any) -> [any]
  ```
- **Line 109**: `rt_btreemap_entries()`
  ```simple
  extern fn __rt_btreemap_entries(handle: any) -> [[any]]
  ```
- **Line 110**: `rt_btreemap_first_key()`
  ```simple
  extern fn __rt_btreemap_first_key(handle: any) -> any
  ```
- **Line 111**: `rt_btreemap_last_key()`
  ```simple
  extern fn __rt_btreemap_last_key(handle: any) -> any
  ```
- **Line 19**: `rt_btreemap_new()`
  ```simple
  val handle = __rt_btreemap_new()
  ```
- **Line 25**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(self.handle, key, value)
  ```
- **Line 30**: `rt_btreemap_get()`
  ```simple
  __rt_btreemap_get(self.handle, key)
  ```
- **Line 34**: `rt_btreemap_contains_key()`
  ```simple
  __rt_btreemap_contains_key(self.handle, key)
  ```
- **Line 39**: `rt_btreemap_remove()`
  ```simple
  __rt_btreemap_remove(self.handle, key)
  ```
- **Line 43**: `rt_btreemap_len()`
  ```simple
  __rt_btreemap_len(self.handle)
  ```
- **Line 51**: `rt_btreemap_clear()`
  ```simple
  __rt_btreemap_clear(self.handle)
  ```
- **Line 55**: `rt_btreemap_keys()`
  ```simple
  __rt_btreemap_keys(self.handle)
  ```
- **Line 59**: `rt_btreemap_values()`
  ```simple
  __rt_btreemap_values(self.handle)
  ```
- **Line 63**: `rt_btreemap_entries()`
  ```simple
  __rt_btreemap_entries(self.handle)
  ```
- **Line 67**: `rt_btreemap_first_key()`
  ```simple
  __rt_btreemap_first_key(self.handle)
  ```
- **Line 71**: `rt_btreemap_last_key()`
  ```simple
  __rt_btreemap_last_key(self.handle)
  ```

#### `rust/lib/std/src/collections/btreeset.spl`

- **Line 112**: `rt_btreeset_new()`
  ```simple
  extern fn __rt_btreeset_new() -> any
  ```
- **Line 113**: `rt_btreeset_insert()`
  ```simple
  extern fn __rt_btreeset_insert(handle: any, value: any) -> bool
  ```
- **Line 114**: `rt_btreeset_contains()`
  ```simple
  extern fn __rt_btreeset_contains(handle: any, value: any) -> bool
  ```
- **Line 115**: `rt_btreeset_remove()`
  ```simple
  extern fn __rt_btreeset_remove(handle: any, value: any) -> bool
  ```
- **Line 116**: `rt_btreeset_len()`
  ```simple
  extern fn __rt_btreeset_len(handle: any) -> i64
  ```
- **Line 117**: `rt_btreeset_clear()`
  ```simple
  extern fn __rt_btreeset_clear(handle: any) -> bool
  ```
- **Line 118**: `rt_btreeset_to_array()`
  ```simple
  extern fn __rt_btreeset_to_array(handle: any) -> [any]
  ```
- **Line 119**: `rt_btreeset_first()`
  ```simple
  extern fn __rt_btreeset_first(handle: any) -> any
  ```
- **Line 120**: `rt_btreeset_last()`
  ```simple
  extern fn __rt_btreeset_last(handle: any) -> any
  ```
- **Line 121**: `rt_btreeset_union()`
  ```simple
  extern fn __rt_btreeset_union(handle1: any, handle2: any) -> any
  ```
- **Line 122**: `rt_btreeset_intersection()`
  ```simple
  extern fn __rt_btreeset_intersection(handle1: any, handle2: any) -> any
  ```
- **Line 123**: `rt_btreeset_difference()`
  ```simple
  extern fn __rt_btreeset_difference(handle1: any, handle2: any) -> any
  ```
- **Line 124**: `rt_btreeset_symmetric_difference()`
  ```simple
  extern fn __rt_btreeset_symmetric_difference(handle1: any, handle2: any) -> any
  ```
- **Line 125**: `rt_btreeset_is_subset()`
  ```simple
  extern fn __rt_btreeset_is_subset(handle1: any, handle2: any) -> bool
  ```
- **Line 126**: `rt_btreeset_is_superset()`
  ```simple
  extern fn __rt_btreeset_is_superset(handle1: any, handle2: any) -> bool
  ```
- **Line 19**: `rt_btreeset_new()`
  ```simple
  val handle = __rt_btreeset_new()
  ```
- **Line 25**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(self.handle, value)
  ```
- **Line 29**: `rt_btreeset_contains()`
  ```simple
  __rt_btreeset_contains(self.handle, value)
  ```
- **Line 34**: `rt_btreeset_remove()`
  ```simple
  __rt_btreeset_remove(self.handle, value)
  ```
- **Line 38**: `rt_btreeset_len()`
  ```simple
  __rt_btreeset_len(self.handle)
  ```
- **Line 46**: `rt_btreeset_clear()`
  ```simple
  __rt_btreeset_clear(self.handle)
  ```
- **Line 50**: `rt_btreeset_to_array()`
  ```simple
  __rt_btreeset_to_array(self.handle)
  ```
- **Line 54**: `rt_btreeset_first()`
  ```simple
  __rt_btreeset_first(self.handle)
  ```
- **Line 58**: `rt_btreeset_last()`
  ```simple
  __rt_btreeset_last(self.handle)
  ```
- **Line 62**: `rt_btreeset_union()`
  ```simple
  val handle = __rt_btreeset_union(self.handle, other.handle)
  ```
- **Line 67**: `rt_btreeset_intersection()`
  ```simple
  val handle = __rt_btreeset_intersection(self.handle, other.handle)
  ```
- **Line 72**: `rt_btreeset_difference()`
  ```simple
  val handle = __rt_btreeset_difference(self.handle, other.handle)
  ```
- **Line 77**: `rt_btreeset_symmetric_difference()`
  ```simple
  val handle = __rt_btreeset_symmetric_difference(self.handle, other.handle)
  ```
- **Line 82**: `rt_btreeset_is_subset()`
  ```simple
  __rt_btreeset_is_subset(self.handle, other.handle)
  ```
- **Line 86**: `rt_btreeset_is_superset()`
  ```simple
  __rt_btreeset_is_superset(self.handle, other.handle)
  ```

#### `rust/lib/std/src/collections/hashmap.spl`

- **Line 17**: `rt_hashmap_new()`
  ```simple
  val handle = __rt_hashmap_new()
  ```
- **Line 23**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(self.handle, key, value)
  ```
- **Line 28**: `rt_hashmap_get()`
  ```simple
  __rt_hashmap_get(self.handle, key)
  ```
- **Line 32**: `rt_hashmap_contains_key()`
  ```simple
  __rt_hashmap_contains_key(self.handle, key)
  ```
- **Line 37**: `rt_hashmap_remove()`
  ```simple
  __rt_hashmap_remove(self.handle, key)
  ```
- **Line 41**: `rt_hashmap_len()`
  ```simple
  __rt_hashmap_len(self.handle)
  ```
- **Line 49**: `rt_hashmap_clear()`
  ```simple
  __rt_hashmap_clear(self.handle)
  ```
- **Line 53**: `rt_hashmap_keys()`
  ```simple
  __rt_hashmap_keys(self.handle)
  ```
- **Line 57**: `rt_hashmap_values()`
  ```simple
  __rt_hashmap_values(self.handle)
  ```
- **Line 61**: `rt_hashmap_entries()`
  ```simple
  __rt_hashmap_entries(self.handle)
  ```
- **Line 90**: `rt_hashmap_new()`
  ```simple
  extern fn __rt_hashmap_new() -> any
  ```
- **Line 91**: `rt_hashmap_insert()`
  ```simple
  extern fn __rt_hashmap_insert(handle: any, key: any, value: any) -> bool
  ```
- **Line 92**: `rt_hashmap_get()`
  ```simple
  extern fn __rt_hashmap_get(handle: any, key: any) -> any
  ```
- **Line 93**: `rt_hashmap_contains_key()`
  ```simple
  extern fn __rt_hashmap_contains_key(handle: any, key: any) -> bool
  ```
- **Line 94**: `rt_hashmap_remove()`
  ```simple
  extern fn __rt_hashmap_remove(handle: any, key: any) -> any
  ```
- **Line 95**: `rt_hashmap_len()`
  ```simple
  extern fn __rt_hashmap_len(handle: any) -> i64
  ```
- **Line 96**: `rt_hashmap_clear()`
  ```simple
  extern fn __rt_hashmap_clear(handle: any) -> bool
  ```
- **Line 97**: `rt_hashmap_keys()`
  ```simple
  extern fn __rt_hashmap_keys(handle: any) -> [any]
  ```
- **Line 98**: `rt_hashmap_values()`
  ```simple
  extern fn __rt_hashmap_values(handle: any) -> [any]
  ```
- **Line 99**: `rt_hashmap_entries()`
  ```simple
  extern fn __rt_hashmap_entries(handle: any) -> [[any]]
  ```

#### `rust/lib/std/src/collections/hashset.spl`

- **Line 104**: `rt_hashset_new()`
  ```simple
  extern fn __rt_hashset_new() -> any
  ```
- **Line 105**: `rt_hashset_insert()`
  ```simple
  extern fn __rt_hashset_insert(handle: any, value: any) -> bool
  ```
- **Line 106**: `rt_hashset_contains()`
  ```simple
  extern fn __rt_hashset_contains(handle: any, value: any) -> bool
  ```
- **Line 107**: `rt_hashset_remove()`
  ```simple
  extern fn __rt_hashset_remove(handle: any, value: any) -> bool
  ```
- **Line 108**: `rt_hashset_len()`
  ```simple
  extern fn __rt_hashset_len(handle: any) -> i64
  ```
- **Line 109**: `rt_hashset_clear()`
  ```simple
  extern fn __rt_hashset_clear(handle: any) -> bool
  ```
- **Line 110**: `rt_hashset_to_array()`
  ```simple
  extern fn __rt_hashset_to_array(handle: any) -> [any]
  ```
- **Line 111**: `rt_hashset_union()`
  ```simple
  extern fn __rt_hashset_union(handle1: any, handle2: any) -> any
  ```
- **Line 112**: `rt_hashset_intersection()`
  ```simple
  extern fn __rt_hashset_intersection(handle1: any, handle2: any) -> any
  ```
- **Line 113**: `rt_hashset_difference()`
  ```simple
  extern fn __rt_hashset_difference(handle1: any, handle2: any) -> any
  ```
- **Line 114**: `rt_hashset_symmetric_difference()`
  ```simple
  extern fn __rt_hashset_symmetric_difference(handle1: any, handle2: any) -> any
  ```
- **Line 115**: `rt_hashset_is_subset()`
  ```simple
  extern fn __rt_hashset_is_subset(handle1: any, handle2: any) -> bool
  ```
- **Line 116**: `rt_hashset_is_superset()`
  ```simple
  extern fn __rt_hashset_is_superset(handle1: any, handle2: any) -> bool
  ```
- **Line 19**: `rt_hashset_new()`
  ```simple
  val handle = __rt_hashset_new()
  ```
- **Line 25**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(self.handle, value)
  ```
- **Line 29**: `rt_hashset_contains()`
  ```simple
  __rt_hashset_contains(self.handle, value)
  ```
- **Line 34**: `rt_hashset_remove()`
  ```simple
  __rt_hashset_remove(self.handle, value)
  ```
- **Line 38**: `rt_hashset_len()`
  ```simple
  __rt_hashset_len(self.handle)
  ```
- **Line 46**: `rt_hashset_clear()`
  ```simple
  __rt_hashset_clear(self.handle)
  ```
- **Line 50**: `rt_hashset_to_array()`
  ```simple
  __rt_hashset_to_array(self.handle)
  ```
- **Line 54**: `rt_hashset_union()`
  ```simple
  val handle = __rt_hashset_union(self.handle, other.handle)
  ```
- **Line 59**: `rt_hashset_intersection()`
  ```simple
  val handle = __rt_hashset_intersection(self.handle, other.handle)
  ```
- **Line 64**: `rt_hashset_difference()`
  ```simple
  val handle = __rt_hashset_difference(self.handle, other.handle)
  ```
- **Line 69**: `rt_hashset_symmetric_difference()`
  ```simple
  val handle = __rt_hashset_symmetric_difference(self.handle, other.handle)
  ```
- **Line 74**: `rt_hashset_is_subset()`
  ```simple
  __rt_hashset_is_subset(self.handle, other.handle)
  ```
- **Line 78**: `rt_hashset_is_superset()`
  ```simple
  __rt_hashset_is_superset(self.handle, other.handle)
  ```

#### `rust/lib/std/src/concurrency/actors.spl`

- **Line 80**: `rt_count()`
  ```simple
  fn get_restart_count(self) -> i32
  ```

#### `rust/lib/std/src/concurrency/channels.spl`

- **Line 36**: `rt_channel_new()`
  ```simple
  val id = rt_channel_new()
  ```
- **Line 40**: `rt_channel_send()`
  ```simple
  rt_channel_send(self._id, value)
  ```
- **Line 43**: `rt_channel_try_recv()`
  ```simple
  return rt_channel_try_recv(self._id)
  ```
- **Line 46**: `rt_channel_recv()`
  ```simple
  return rt_channel_recv(self._id)
  ```
- **Line 49**: `rt_channel_close()`
  ```simple
  rt_channel_close(self._id)
  ```
- **Line 52**: `rt_channel_is_closed()`
  ```simple
  return rt_channel_is_closed(self._id) == 1
  ```
- **Line 58**: `rt_channel_close()`
  ```simple
  rt_channel_close(self._id)
  ```
- **Line 74**: `rt_channel_new()`
  ```simple
  val id = rt_channel_new()
  ```

#### `rust/lib/std/src/concurrency/threads.spl`

- **Line 109**: `rt_thread_is_done()`
  ```simple
  return rt_thread_is_done(self._handle) == 1
  ```
- **Line 113**: `rt_thread_id()`
  ```simple
  return rt_thread_id(self._handle)
  ```
- **Line 119**: `rt_thread_free()`
  ```simple
  rt_thread_free(self._handle)
  ```
- **Line 157**: `rt_thread_spawn_isolated()`
  ```simple
  val handle = rt_thread_spawn_isolated(closure as i64, data)
  ```
- **Line 197**: `rt_thread_join_limited()`
  ```simple
  return rt_thread_join_limited(self._handle)
  ```
- **Line 201**: `rt_thread_is_done_limited()`
  ```simple
  return rt_thread_is_done_limited(self._handle) == 1
  ```
- **Line 209**: `rt_thread_id_limited()`
  ```simple
  return rt_thread_id_limited(self._handle)
  ```
- **Line 213**: `rt_thread_free_limited()`
  ```simple
  rt_thread_free_limited(self._handle)
  ```
- **Line 221**: `rt_thread_was_killed()`
  ```simple
  return rt_thread_was_killed(self._handle) == 1
  ```
- **Line 232**: `rt_thread_get_violation_type()`
  ```simple
  val violation_type = rt_thread_get_violation_type(self._handle)
  ```
- **Line 233**: `rt_thread_get_violation_value()`
  ```simple
  val violation_value = rt_thread_get_violation_value(self._handle)
  ```
- **Line 327**: `rt_thread_spawn_limited()`
  ```simple
  val handle = rt_thread_spawn_limited(closure as i64, data, cpu, mem, fd, threads)
  ```
- **Line 376**: `rt_thread_available_parallelism()`
  ```simple
  return rt_thread_available_parallelism()
  ```
- **Line 386**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(millis)
  ```
- **Line 399**: `rt_thread_yield()`
  ```simple
  rt_thread_yield()
  ```
- **Line 98**: `rt_thread_join()`
  ```simple
  return rt_thread_join(self._handle)
  ```

#### `rust/lib/std/src/context_manager.spl`

- **Line 174**: `rt_file_open()`
  ```simple
  val fd = rt_file_open(path, mode_int)
  ```
- **Line 179**: `rt_file_close()`
  ```simple
  rt_file_close(handle as i32)
  ```
- **Line 182**: `rt_time_now_seconds()`
  ```simple
  return rt_time_now_seconds()
  ```

#### `rust/lib/std/src/db/atomic.spl`

- **Line 105**: `rt_file_atomic_write()`
  ```simple
  val success = rt_file_atomic_write(path, content)
  ```
- **Line 122**: `rt_file_unlock()`
  ```simple
  rt_file_unlock(lock_path)
  ```
- **Line 127**: `rt_dir_glob()`
  ```simple
  val files = rt_dir_glob(pattern)
  ```
- **Line 129**: `rt_file_remove()`
  ```simple
  rt_file_remove(file)
  ```
- **Line 28**: `rt_file_lock()`
  ```simple
  val lock_path = rt_file_lock(path, timeout_secs)
  ```
- **Line 37**: `rt_file_unlock()`
  ```simple
  rt_file_unlock(self.lock_path)
  ```
- **Line 60**: `rt_file_exists()`
  ```simple
  if rt_file_exists(path)
  ```
- **Line 61**: `rt_file_read_text()`
  ```simple
  content = rt_file_read_text(path)
  ```
- **Line 67**: `rt_file_atomic_write()`
  ```simple
  val success = rt_file_atomic_write(path, new_content)
  ```
- **Line 86**: `rt_file_exists()`
  ```simple
  if not rt_file_exists(path)
  ```
- **Line 90**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text(path)
  ```

#### `rust/lib/std/src/db/persistence.spl`

- **Line 249**: `rt_dir_glob()`
  ```simple
  val files = rt_dir_glob(pattern)
  ```
- **Line 251**: `rt_file_remove()`
  ```simple
  rt_file_remove(file)
  ```

#### `rust/lib/std/src/diagram/integration.spl`

- **Line 19**: `rt_diagram_recording()`
  ```simple
  fn start_diagram_recording(test_name: text, config: DiagramConfig) -> void:
  ```
- **Line 70**: `rt_diagram_recording()`
  ```simple
  start_diagram_recording(test_name, config)
  ```

#### `rust/lib/std/src/doctest.disabled/parser.spl`

- **Line 520**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 522**: `rt_file_read_text()`
  ```simple
  return _rt_file_read_text(path.ptr(), path.len())
  ```

#### `rust/lib/std/src/electron.disabled/app.spl`

- **Line 107**: `rt_monitoring()`
  ```simple
  start_monitoring()
  ```

#### `rust/lib/std/src/file/async_handle.spl`

- **Line 10**: `rt_loading()`
  ```simple
  extern fn native_async_file_start_loading(handle_id: i64) -> ()
  ```
- **Line 152**: `rt_loading()`
  ```simple
  pub fn start_loading(mut self)
  ```
- **Line 153**: `rt_loading()`
  ```simple
  native_async_file_start_loading(self.handle_id)
  ```

#### `rust/lib/std/src/file/context.spl`

- **Line 69**: `rt_loading()`
  ```simple
  self.start_loading()
  ```

#### `rust/lib/std/src/file/__init__.spl`

- **Line 106**: `rt_check_file_path()`
  ```simple
  return rt_check_file_path(path)
  ```
- **Line 114**: `rt_file_open()`
  ```simple
  val fd = rt_file_open(path, mode_int)
  ```
- **Line 121**: `rt_file_get_size()`
  ```simple
  val size = rt_file_get_size(fd)
  ```
- **Line 128**: `rt_file_close()`
  ```simple
  rt_file_close(fd)
  ```
- **Line 132**: `rt_file_mmap()`
  ```simple
  val ptr = rt_file_mmap(addr, length as i32, prot, flags, fd, offset as i32)
  ```
- **Line 139**: `rt_file_munmap()`
  ```simple
  val result = rt_file_munmap(addr, length as i32)
  ```
- **Line 146**: `rt_file_madvise()`
  ```simple
  val result = rt_file_madvise(addr, length as i32, advice)
  ```
- **Line 40**: `rt_loading()`
  ```simple
  handle.start_loading()
  ```
- **Line 46**: `rt_loading()`
  ```simple
  handle.start_loading()
  ```

#### `rust/lib/std/src/fs/mod.spl`

- **Line 102**: `rt_file_canonicalize()`
  ```simple
  val result = rt_file_canonicalize(path)
  ```
- **Line 116**: `rt_dir_create()`
  ```simple
  if rt_dir_create(path, recursive)
  ```
- **Line 128**: `rt_dir_list()`
  ```simple
  val result = rt_dir_list(path)
  ```
- **Line 135**: `rt_dir_remove()`
  ```simple
  if rt_dir_remove(path, recursive)
  ```
- **Line 148**: `rt_file_find()`
  ```simple
  val result = rt_file_find(dir, pattern, recursive)
  ```
- **Line 156**: `rt_dir_glob()`
  ```simple
  val result = rt_dir_glob(dir, pattern)
  ```
- **Line 167**: `rt_path_basename()`
  ```simple
  val result = rt_path_basename(path)
  ```
- **Line 174**: `rt_path_dirname()`
  ```simple
  val result = rt_path_dirname(path)
  ```
- **Line 181**: `rt_path_ext()`
  ```simple
  val result = rt_path_ext(path)
  ```
- **Line 186**: `rt_path_absolute()`
  ```simple
  val result = rt_path_absolute(path)
  ```
- **Line 196**: `rt_path_separator()`
  ```simple
  val result = rt_path_separator()
  ```
- **Line 227**: `rt_dir_list()`
  ```simple
  val result = rt_dir_list(path)
  ```
- **Line 236**: `rt_dir_list()`
  ```simple
  val result = rt_dir_list(path)
  ```
- **Line 40**: `rt_file_exists()`
  ```simple
  rt_file_exists(path)
  ```
- **Line 50**: `rt_file_read_text()`
  ```simple
  val result = rt_file_read_text(path)
  ```
- **Line 58**: `rt_file_write_text()`
  ```simple
  if rt_file_write_text(path, content)
  ```
- **Line 81**: `rt_file_copy()`
  ```simple
  if rt_file_copy(src, dest)
  ```
- **Line 88**: `rt_file_remove()`
  ```simple
  if rt_file_remove(path)
  ```
- **Line 95**: `rt_file_rename()`
  ```simple
  if rt_file_rename(source, dest)
  ```

#### `rust/lib/std/src/godot.disabled/animation.spl`

- **Line 674**: `rt_key()`
  ```simple
  self.animation.track_insert_key(self.current_track, time, value)
  ```
- **Line 88**: `rt_key()`
  ```simple
  pub fn track_insert_key(mut self, track_idx: i32, time: f64, value: variant.Variant):
  ```

#### `rust/lib/std/src/godot.disabled/cli.spl`

- **Line 258**: `rt_file_watcher()`
  ```simple
  start_file_watcher()
  ```
- **Line 265**: `rt_file_watcher()`
  ```simple
  fn start_file_watcher()
  ```
- **Line 271**: `rt_platform_name()`
  ```simple
  fn _rt_platform_name() -> text
  ```
- **Line 273**: `rt_platform_name()`
  ```simple
  val platform = _rt_platform_name()
  ```
- **Line 282**: `rt_polling_watcher()`
  ```simple
  start_polling_watcher()
  ```
- **Line 288**: `rt_polling_watcher()`
  ```simple
  start_polling_watcher()
  ```
- **Line 291**: `rt_polling_watcher()`
  ```simple
  start_polling_watcher()
  ```
- **Line 295**: `rt_polling_watcher()`
  ```simple
  fn start_polling_watcher()
  ```

#### `rust/lib/std/src/godot.disabled/hotreload.spl`

- **Line 199**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 209**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(
  ```
- **Line 393**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 396**: `rt_fnv_hash()`
  ```simple
  fn _rt_fnv_hash(data_ptr: &u8, data_len: u64) -> u64
  ```
- **Line 399**: `rt_file_read_text()`
  ```simple
  val content = _rt_file_read_text(path.ptr(), path.len())
  ```
- **Line 405**: `rt_fnv_hash()`
  ```simple
  val hash = _rt_fnv_hash(content.ptr(), content.len())
  ```
- **Line 421**: `rt_dir_list()`
  ```simple
  fn _rt_dir_list(path_ptr: &u8, path_len: u64) -> Any
  ```
- **Line 424**: `rt_file_stat()`
  ```simple
  fn _rt_file_stat(
  ```
- **Line 436**: `rt_path_ext()`
  ```simple
  fn _rt_path_ext(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 441**: `rt_dir_list()`
  ```simple
  val entries = _rt_dir_list(dir.ptr(), dir.len())
  ```
- **Line 458**: `rt_file_stat()`
  ```simple
  _rt_file_stat(
  ```
- **Line 476**: `rt_path_ext()`
  ```simple
  val file_ext = _rt_path_ext(full_path.ptr(), full_path.len())
  ```
- **Line 485**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 487**: `rt_time_now_unix_micros()`
  ```simple
  val micros = _rt_time_now_unix_micros()
  ```
- **Line 497**: `rt_thread_sleep()`
  ```simple
  fn _rt_thread_sleep(millis: i64)
  ```
- **Line 500**: `rt_thread_sleep()`
  ```simple
  _rt_thread_sleep(millis)
  ```

#### `rust/lib/std/src/godot.disabled/input.spl`

- **Line 119**: `rt_joy_vibration()`
  ```simple
  pub fn start_joy_vibration(mut self, device: i32, weak: f64, strong: f64, duration: f64):
  ```
- **Line 210**: `rt_joy_vibration()`
  ```simple
  self.start_joy_vibration(device, intensity, intensity, duration)
  ```

#### `rust/lib/std/src/godot.disabled/saveload.spl`

- **Line 664**: `rt_file_remove()`
  ```simple
  fn _rt_file_remove(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 667**: `rt_file_remove()`
  ```simple
  val success = _rt_file_remove(path.ptr(), path.len())
  ```

#### `rust/lib/std/src/godot.disabled/scene.spl`

- **Line 643**: `rt_thread_sleep()`
  ```simple
  fn _rt_thread_sleep(ms: i64)
  ```
- **Line 646**: `rt_thread_sleep()`
  ```simple
  _rt_thread_sleep(ms)
  ```

#### `rust/lib/std/src/gpu/kernel/math.spl`

- **Line 117**: `rt_math_floor()`
  ```simple
  return rt_math_floor(x)
  ```
- **Line 122**: `rt_math_ceil()`
  ```simple
  return rt_math_ceil(x)
  ```
- **Line 21**: `rt_math_sqrt()`
  ```simple
  return rt_math_sqrt(x)
  ```
- **Line 27**: `rt_math_sin()`
  ```simple
  return rt_math_sin(x)
  ```
- **Line 32**: `rt_math_cos()`
  ```simple
  return rt_math_cos(x)
  ```
- **Line 37**: `rt_math_tan()`
  ```simple
  return rt_math_tan(x)
  ```
- **Line 43**: `rt_math_asin()`
  ```simple
  return rt_math_asin(x)
  ```
- **Line 48**: `rt_math_acos()`
  ```simple
  return rt_math_acos(x)
  ```
- **Line 53**: `rt_math_atan()`
  ```simple
  return rt_math_atan(x)
  ```
- **Line 64**: `rt_math_exp()`
  ```simple
  return rt_math_exp(x)
  ```
- **Line 73**: `rt_math_log()`
  ```simple
  return rt_math_log(x)
  ```
- **Line 89**: `rt_math_pow()`
  ```simple
  return rt_math_pow(base, exp)
  ```

#### `rust/lib/std/src/graphics.disabled/loaders/obj.spl`

- **Line 192**: `rt_vertex()`
  ```simple
  val v0 = self.convert_vertex(face.indices[0])?
  ```
- **Line 193**: `rt_vertex()`
  ```simple
  val v1 = self.convert_vertex(face.indices[i])?
  ```
- **Line 194**: `rt_vertex()`
  ```simple
  val v2 = self.convert_vertex(face.indices[i + 1])?
  ```
- **Line 218**: `rt_vertex()`
  ```simple
  fn convert_vertex(obj_vertex: ObjVertex) -> Result<MeshVertex, text>:
  ```

#### `rust/lib/std/src/graphics.disabled/render/batching.spl`

- **Line 179**: `rt_by()`
  ```simple
  batches.sort_by(a, b
  ```

#### `rust/lib/std/src/graphics.disabled/scene/lod.spl`

- **Line 125**: `rt_by()`
  ```simple
  self.levels.sort_by(fn(a: LODLevel, b: LODLevel) -> i32:
  ```

#### `rust/lib/std/src/graphics.disabled/ui/scene3d.spl`

- **Line 84**: `rt_mut()`
  ```simple
  pub fn get_viewport_mut(mut self) -> Viewport3D
  ```

#### `rust/lib/std/src/host/async_nogc_mut/datetime.spl`

- **Line 143**: `rt_time_now_unix_micros()`
  ```simple
  val micros = rt_time_now_unix_micros()
  ```
- **Line 145**: `rt_timestamp_get_hour()`
  ```simple
  hour=rt_timestamp_get_hour(micros),
  ```
- **Line 146**: `rt_timestamp_get_minute()`
  ```simple
  minute=rt_timestamp_get_minute(micros),
  ```
- **Line 147**: `rt_timestamp_get_second()`
  ```simple
  second=rt_timestamp_get_second(micros),
  ```
- **Line 148**: `rt_timestamp_get_microsecond()`
  ```simple
  microsecond=rt_timestamp_get_microsecond(micros)
  ```
- **Line 208**: `rt_time_now_unix_micros()`
  ```simple
  val micros = rt_time_now_unix_micros()
  ```
- **Line 210**: `rt_timestamp_get_year()`
  ```simple
  rt_timestamp_get_year(micros),
  ```
- **Line 211**: `rt_timestamp_get_month()`
  ```simple
  rt_timestamp_get_month(micros),
  ```
- **Line 212**: `rt_timestamp_get_day()`
  ```simple
  rt_timestamp_get_day(micros)
  ```
- **Line 297**: `rt_timestamp_from_components()`
  ```simple
  val micros = rt_timestamp_from_components(self.year, self.month, self.day, 0, 0, 0, 0)
  ```
- **Line 298**: `rt_timestamp_add_days()`
  ```simple
  val new_micros = rt_timestamp_add_days(micros, days)
  ```
- **Line 300**: `rt_timestamp_get_year()`
  ```simple
  rt_timestamp_get_year(new_micros),
  ```
- **Line 301**: `rt_timestamp_get_month()`
  ```simple
  rt_timestamp_get_month(new_micros),
  ```
- **Line 302**: `rt_timestamp_get_day()`
  ```simple
  rt_timestamp_get_day(new_micros)
  ```
- **Line 307**: `rt_timestamp_from_components()`
  ```simple
  val micros1 = rt_timestamp_from_components(self.year, self.month, self.day, 0, 0, 0, 0)
  ```
- **Line 308**: `rt_timestamp_from_components()`
  ```simple
  val micros2 = rt_timestamp_from_components(other.year, other.month, other.day, 0, 0, 0, 0)
  ```
- **Line 309**: `rt_timestamp_diff_days()`
  ```simple
  return rt_timestamp_diff_days(micros1, micros2)
  ```
- **Line 335**: `rt_time_now_unix_micros()`
  ```simple
  val micros = rt_time_now_unix_micros()
  ```
- **Line 337**: `rt_timestamp_get_year()`
  ```simple
  rt_timestamp_get_year(micros),
  ```
- **Line 338**: `rt_timestamp_get_month()`
  ```simple
  rt_timestamp_get_month(micros),
  ```
- **Line 339**: `rt_timestamp_get_day()`
  ```simple
  rt_timestamp_get_day(micros),
  ```
- **Line 340**: `rt_timestamp_get_hour()`
  ```simple
  rt_timestamp_get_hour(micros),
  ```
- **Line 341**: `rt_timestamp_get_minute()`
  ```simple
  rt_timestamp_get_minute(micros),
  ```
- **Line 342**: `rt_timestamp_get_second()`
  ```simple
  rt_timestamp_get_second(micros),
  ```
- **Line 343**: `rt_timestamp_get_microsecond()`
  ```simple
  rt_timestamp_get_microsecond(micros)
  ```
- **Line 349**: `rt_timestamp_get_year()`
  ```simple
  rt_timestamp_get_year(timestamp),
  ```
- **Line 350**: `rt_timestamp_get_month()`
  ```simple
  rt_timestamp_get_month(timestamp),
  ```
- **Line 351**: `rt_timestamp_get_day()`
  ```simple
  rt_timestamp_get_day(timestamp),
  ```
- **Line 352**: `rt_timestamp_get_hour()`
  ```simple
  rt_timestamp_get_hour(timestamp),
  ```
- **Line 353**: `rt_timestamp_get_minute()`
  ```simple
  rt_timestamp_get_minute(timestamp),
  ```
- **Line 354**: `rt_timestamp_get_second()`
  ```simple
  rt_timestamp_get_second(timestamp),
  ```
- **Line 355**: `rt_timestamp_get_microsecond()`
  ```simple
  rt_timestamp_get_microsecond(timestamp)
  ```
- **Line 360**: `rt_timestamp_from_components()`
  ```simple
  return rt_timestamp_from_components(
  ```

#### `rust/lib/std/src/host/async_nogc_mut/io/fs/file.spl`

- **Line 391**: `rt_tracking()`
  ```simple
  file._start_tracking("File.open_sync("{resolved_path}")")
  ```
- **Line 48**: `rt_tracking()`
  ```simple
  file._start_tracking("File.open("{resolved_path}")")
  ```

#### `rust/lib/std/src/host/async_nogc_mut/io/stdio.spl`

- **Line 11**: `rt_read_stdin_line()`
  ```simple
  match rt_read_stdin_line()
  ```
- **Line 31**: `rt_read_stdin_line()`
  ```simple
  match rt_read_stdin_line()
  ```

#### `rust/lib/std/src/host/async_nogc_mut/sys_simple.spl`

- **Line 17**: `rt_stdout_write()`
  ```simple
  val written = rt_stdout_write(s)
  ```
- **Line 24**: `rt_stdout_flush()`
  ```simple
  val result = rt_stdout_flush()
  ```
- **Line 45**: `rt_get_args()`
  ```simple
  return rt_get_args()
  ```
- **Line 56**: `rt_get_args()`
  ```simple
  return rt_get_args().len()
  ```
- **Line 67**: `rt_get_args()`
  ```simple
  return rt_get_args().len() > 1
  ```
- **Line 84**: `rt_exit()`
  ```simple
  rt_exit(code)
  ```

#### `rust/lib/std/src/host/async_nogc_mut/sys.spl`

- **Line 136**: `rt_get_args()`
  ```simple
  return rt_get_args()
  ```
- **Line 152**: `rt_get_args()`
  ```simple
  return rt_get_args().len()
  ```
- **Line 167**: `rt_get_args()`
  ```simple
  val args = rt_get_args()
  ```
- **Line 182**: `rt_get_args()`
  ```simple
  val args = rt_get_args()
  ```
- **Line 197**: `rt_get_args()`
  ```simple
  return rt_get_args().len() > 1
  ```
- **Line 214**: `rt_exit()`
  ```simple
  rt_exit(code)
  ```

#### `rust/lib/std/src/host/common/io/styled_text.spl`

- **Line 37**: `rt_count()`
  ```simple
  pub fn part_count(self) -> u64
  ```
- **Line 51**: `rt_count()`
  ```simple
  return self.part_count() == 0
  ```
- **Line 59**: `rt_count()`
  ```simple
  return "StyledString: {self.part_count()} parts"
  ```

#### `rust/lib/std/src/host/common/net/tcp.spl`

- **Line 120**: `rt_tracking()`
  ```simple
  stream._start_tracking("TcpStream.connect_timeout("{addr}")")
  ```
- **Line 42**: `rt_tracking()`
  ```simple
  listener._start_tracking("TcpListener.bind("{addr}")")
  ```
- **Line 65**: `rt_tracking()`
  ```simple
  stream._start_tracking("TcpListener.accept() -> {peer_addr}")
  ```
- **Line 98**: `rt_tracking()`
  ```simple
  stream._start_tracking("TcpStream.connect("{addr}")")
  ```

#### `rust/lib/std/src/host/common/net/udp.spl`

- **Line 21**: `rt_tracking()`
  ```simple
  socket._start_tracking("UdpSocket.bind("{addr}")")
  ```

#### `rust/lib/std/src/infra/alloc.spl`

- **Line 103**: `rt_arena_free()`
  ```simple
  rt_arena_free(self._handle)
  ```
- **Line 304**: `rt_pool_new()`
  ```simple
  val handle = rt_pool_new(object_size, capacity)
  ```
- **Line 314**: `rt_pool_acquire()`
  ```simple
  return rt_pool_acquire(self._handle)
  ```
- **Line 318**: `rt_pool_release()`
  ```simple
  rt_pool_release(self._handle, ptr)
  ```
- **Line 322**: `rt_pool_available()`
  ```simple
  return rt_pool_available(self._handle)
  ```
- **Line 326**: `rt_pool_capacity()`
  ```simple
  return rt_pool_capacity(self._handle)
  ```
- **Line 334**: `rt_pool_free()`
  ```simple
  rt_pool_free(self._handle)
  ```
- **Line 549**: `rt_arena_new()`
  ```simple
  val buffer = rt_arena_new(capacity)
  ```
- **Line 570**: `rt_arena_free()`
  ```simple
  rt_arena_free(self._buffer)
  ```
- **Line 76**: `rt_arena_new()`
  ```simple
  val handle = rt_arena_new(capacity)
  ```
- **Line 82**: `rt_arena_alloc()`
  ```simple
  return rt_arena_alloc(self._handle, size)
  ```
- **Line 87**: `rt_arena_reset()`
  ```simple
  rt_arena_reset(self._handle)
  ```
- **Line 91**: `rt_arena_used()`
  ```simple
  return rt_arena_used(self._handle)
  ```
- **Line 95**: `rt_arena_capacity()`
  ```simple
  return rt_arena_capacity(self._handle)
  ```

#### `rust/lib/std/src/infra/atomic.spl`

- **Line 176**: `rt_atomic_int_new()`
  ```simple
  val ptr = rt_atomic_int_new(value)
  ```
- **Line 181**: `rt_atomic_int_load()`
  ```simple
  return rt_atomic_int_load(self._ptr, ordering_to_int(ordering))
  ```
- **Line 185**: `rt_atomic_int_store()`
  ```simple
  rt_atomic_int_store(self._ptr, value, ordering_to_int(ordering))
  ```
- **Line 189**: `rt_atomic_int_swap()`
  ```simple
  return rt_atomic_int_swap(self._ptr, value, ordering_to_int(ordering))
  ```
- **Line 200**: `rt_atomic_int_compare_exchange()`
  ```simple
  val result = rt_atomic_int_compare_exchange(
  ```
- **Line 214**: `rt_atomic_int_fetch_add()`
  ```simple
  return rt_atomic_int_fetch_add(self._ptr, value, ordering_to_int(ordering))
  ```
- **Line 218**: `rt_atomic_int_fetch_sub()`
  ```simple
  return rt_atomic_int_fetch_sub(self._ptr, value, ordering_to_int(ordering))
  ```
- **Line 222**: `rt_atomic_int_fetch_and()`
  ```simple
  return rt_atomic_int_fetch_and(self._ptr, value, ordering_to_int(ordering))
  ```
- **Line 226**: `rt_atomic_int_fetch_or()`
  ```simple
  return rt_atomic_int_fetch_or(self._ptr, value, ordering_to_int(ordering))
  ```
- **Line 230**: `rt_atomic_int_fetch_xor()`
  ```simple
  return rt_atomic_int_fetch_xor(self._ptr, value, ordering_to_int(ordering))
  ```
- **Line 242**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(self._ptr)
  ```
- **Line 292**: `rt_atomic_bool_new()`
  ```simple
  val ptr = rt_atomic_bool_new(int_val)
  ```
- **Line 296**: `rt_atomic_bool_load()`
  ```simple
  return rt_atomic_bool_load(self._ptr, ordering_to_int(ordering)) == 1
  ```
- **Line 300**: `rt_atomic_bool_store()`
  ```simple
  rt_atomic_bool_store(self._ptr, int_val, ordering_to_int(ordering))
  ```
- **Line 304**: `rt_atomic_bool_swap()`
  ```simple
  return rt_atomic_bool_swap(self._ptr, int_val, ordering_to_int(ordering)) == 1
  ```
- **Line 312**: `rt_atomic_bool_free()`
  ```simple
  rt_atomic_bool_free(self._ptr)
  ```
- **Line 360**: `rt_atomic_flag_new()`
  ```simple
  val ptr = rt_atomic_flag_new()
  ```
- **Line 367**: `rt_atomic_flag_test_and_set()`
  ```simple
  return rt_atomic_flag_test_and_set(self._ptr, ordering_to_int(ordering)) == 1
  ```
- **Line 371**: `rt_atomic_flag_clear()`
  ```simple
  rt_atomic_flag_clear(self._ptr, ordering_to_int(ordering))
  ```
- **Line 374**: `rt_atomic_flag_free()`
  ```simple
  rt_atomic_flag_free(self._ptr)
  ```
- **Line 519**: `rt_spin_loop_hint()`
  ```simple
  rt_spin_loop_hint()
  ```

#### `rust/lib/std/src/infra/concurrent.spl`

- **Line 104**: `rt_concurrent_map_clear()`
  ```simple
  rt_concurrent_map_clear(self._handle)
  ```
- **Line 130**: `rt_concurrent_map_free()`
  ```simple
  rt_concurrent_map_free(self._handle)
  ```
- **Line 293**: `rt_concurrent_queue_new()`
  ```simple
  val handle = rt_concurrent_queue_new()
  ```
- **Line 298**: `rt_concurrent_queue_push()`
  ```simple
  rt_concurrent_queue_push(self._handle, value as i64)
  ```
- **Line 304**: `rt_concurrent_queue_pop()`
  ```simple
  val value = rt_concurrent_queue_pop(self._handle)
  ```
- **Line 309**: `rt_concurrent_queue_is_empty()`
  ```simple
  return rt_concurrent_queue_is_empty(self._handle) == 1
  ```
- **Line 313**: `rt_concurrent_queue_len()`
  ```simple
  return rt_concurrent_queue_len(self._handle)
  ```
- **Line 317**: `rt_concurrent_queue_free()`
  ```simple
  rt_concurrent_queue_free(self._handle)
  ```
- **Line 388**: `rt_concurrent_stack_new()`
  ```simple
  val handle = rt_concurrent_stack_new()
  ```
- **Line 393**: `rt_concurrent_stack_push()`
  ```simple
  rt_concurrent_stack_push(self._handle, value as i64)
  ```
- **Line 399**: `rt_concurrent_stack_pop()`
  ```simple
  val value = rt_concurrent_stack_pop(self._handle)
  ```
- **Line 404**: `rt_concurrent_stack_is_empty()`
  ```simple
  return rt_concurrent_stack_is_empty(self._handle) == 1
  ```
- **Line 408**: `rt_concurrent_stack_free()`
  ```simple
  rt_concurrent_stack_free(self._handle)
  ```
- **Line 66**: `rt_concurrent_map_new()`
  ```simple
  val handle = rt_concurrent_map_new()
  ```
- **Line 71**: `rt_concurrent_map_insert()`
  ```simple
  val prev = rt_concurrent_map_insert(self._handle, key as i64, value as i64)
  ```
- **Line 78**: `rt_concurrent_map_get()`
  ```simple
  val value = rt_concurrent_map_get(self._handle, key as i64)
  ```
- **Line 85**: `rt_concurrent_map_remove()`
  ```simple
  val value = rt_concurrent_map_remove(self._handle, key as i64)
  ```
- **Line 92**: `rt_concurrent_map_contains()`
  ```simple
  return rt_concurrent_map_contains(self._handle, key as i64) == 1
  ```
- **Line 96**: `rt_concurrent_map_len()`
  ```simple
  return rt_concurrent_map_len(self._handle)
  ```

#### `rust/lib/std/src/infra/config_env.spl`

- **Line 258**: `rt_env_all()`
  ```simple
  rt_env_all()
  ```

#### `rust/lib/std/src/infra/file_io.spl`

- **Line 111**: `rt_file_atomic_write()`
  ```simple
  val success = rt_file_atomic_write(path, content)
  ```
- **Line 119**: `rt_file_atomic_write()`
  ```simple
  rt_file_atomic_write(path, content)
  ```
- **Line 126**: `rt_file_append_text()`
  ```simple
  val success = rt_file_append_text(path, content)
  ```
- **Line 134**: `rt_file_append_text()`
  ```simple
  rt_file_append_text(path, content)
  ```
- **Line 141**: `rt_file_write_bytes()`
  ```simple
  val success = rt_file_write_bytes(path, data)
  ```
- **Line 149**: `rt_file_write_bytes()`
  ```simple
  rt_file_write_bytes(path, data)
  ```
- **Line 163**: `rt_file_copy()`
  ```simple
  val success = rt_file_copy(source, dest)
  ```
- **Line 16**: `rt_file_exists()`
  ```simple
  rt_file_exists(path)
  ```
- **Line 174**: `rt_file_remove()`
  ```simple
  val success = rt_file_remove(path)
  ```
- **Line 185**: `rt_file_rename()`
  ```simple
  val success = rt_file_rename(old_path, new_path)
  ```
- **Line 198**: `rt_file_move()`
  ```simple
  val success = rt_file_move(source, dest)
  ```
- **Line 209**: `rt_file_canonicalize()`
  ```simple
  rt_file_canonicalize(path)
  ```
- **Line 20**: `rt_file_exists()`
  ```simple
  rt_file_exists(path)
  ```
- **Line 220**: `rt_dir_create()`
  ```simple
  val success = rt_dir_create(path)
  ```
- **Line 234**: `rt_dir_list()`
  ```simple
  val entries = rt_dir_list(path)
  ```
- **Line 239**: `rt_dir_list()`
  ```simple
  rt_dir_list(path)
  ```
- **Line 246**: `rt_dir_remove()`
  ```simple
  val success = rt_dir_remove(path)
  ```
- **Line 257**: `rt_file_find()`
  ```simple
  rt_file_find(dir, pattern)
  ```
- **Line 264**: `rt_dir_glob()`
  ```simple
  rt_dir_glob(pattern)
  ```
- **Line 271**: `rt_dir_create_all()`
  ```simple
  val success = rt_dir_create_all(path)
  ```
- **Line 27**: `rt_file_stat()`
  ```simple
  val stat = rt_file_stat(path)
  ```
- **Line 284**: `rt_dir_walk()`
  ```simple
  val entries = rt_dir_walk(path)
  ```
- **Line 289**: `rt_dir_walk()`
  ```simple
  rt_dir_walk(path)
  ```
- **Line 296**: `rt_current_dir()`
  ```simple
  rt_current_dir()
  ```
- **Line 303**: `rt_set_current_dir()`
  ```simple
  val success = rt_set_current_dir(path)
  ```
- **Line 314**: `rt_dir_remove_all()`
  ```simple
  val success = rt_dir_remove_all(path)
  ```
- **Line 329**: `rt_path_basename()`
  ```simple
  rt_path_basename(path)
  ```
- **Line 336**: `rt_path_dirname()`
  ```simple
  rt_path_dirname(path)
  ```
- **Line 343**: `rt_path_ext()`
  ```simple
  rt_path_ext(path)
  ```
- **Line 355**: `rt_path_absolute()`
  ```simple
  rt_path_absolute(path)
  ```
- **Line 362**: `rt_path_separator()`
  ```simple
  rt_path_separator()
  ```
- **Line 369**: `rt_path_stem()`
  ```simple
  rt_path_stem(path)
  ```
- **Line 376**: `rt_path_relative()`
  ```simple
  rt_path_relative(path, base)
  ```
- **Line 383**: `rt_path_join()`
  ```simple
  rt_path_join(path1, path2)
  ```
- **Line 394**: `rt_file_open()`
  ```simple
  val fd = rt_file_open(path, mode)
  ```
- **Line 405**: `rt_file_get_size()`
  ```simple
  val size = rt_file_get_size(fd)
  ```
- **Line 416**: `rt_file_close()`
  ```simple
  val success = rt_file_close(fd)
  ```
- **Line 433**: `rt_dir_list()`
  ```simple
  val entries = rt_dir_list(path)
  ```
- **Line 45**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text(path)
  ```
- **Line 50**: `rt_file_read_text()`
  ```simple
  rt_file_read_text(path)
  ```
- **Line 59**: `rt_file_read_lines()`
  ```simple
  val lines = rt_file_read_lines(path)
  ```
- **Line 64**: `rt_file_read_lines()`
  ```simple
  rt_file_read_lines(path)
  ```
- **Line 73**: `rt_file_read_bytes()`
  ```simple
  val bytes = rt_file_read_bytes(path)
  ```
- **Line 78**: `rt_file_read_bytes()`
  ```simple
  rt_file_read_bytes(path)
  ```
- **Line 89**: `rt_file_write_text()`
  ```simple
  val success = rt_file_write_text(path, content)
  ```
- **Line 97**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(path, content)
  ```

#### `rust/lib/std/src/infra/hash.spl`

- **Line 232**: `rt_xxhash_new()`
  ```simple
  val handle = rt_xxhash_new()
  ```
- **Line 236**: `rt_xxhash_new_with_seed()`
  ```simple
  val handle = rt_xxhash_new_with_seed(seed as i64)
  ```
- **Line 240**: `rt_xxhash_write()`
  ```simple
  rt_xxhash_write(self._handle, data as i64, len(data))
  ```
- **Line 257**: `rt_xxhash_finish()`
  ```simple
  return rt_xxhash_finish(self._handle) as u64
  ```
- **Line 260**: `rt_xxhash_reset()`
  ```simple
  rt_xxhash_reset(self._handle)
  ```
- **Line 263**: `rt_xxhash_free()`
  ```simple
  rt_xxhash_free(self._handle)
  ```
- **Line 293**: `rt_fnv_hash()`
  ```simple
  return rt_fnv_hash(bytes as i64, len(bytes)) as u64
  ```

#### `rust/lib/std/src/infra/synchronization.spl`

- **Line 103**: `rt_mutex_lock()`
  ```simple
  rt_mutex_lock(self._handle)
  ```
- **Line 105**: `rt_mutex_unlock()`
  ```simple
  rt_mutex_unlock(self._handle)
  ```
- **Line 123**: `rt_mutex_free()`
  ```simple
  rt_mutex_free(self._handle)
  ```
- **Line 158**: `rt_rwlock_new()`
  ```simple
  val handle = rt_rwlock_new()
  ```
- **Line 166**: `rt_rwlock_read()`
  ```simple
  rt_rwlock_read(self._handle)
  ```
- **Line 168**: `rt_rwlock_unlock_read()`
  ```simple
  rt_rwlock_unlock_read(self._handle)
  ```
- **Line 175**: `rt_rwlock_try_read()`
  ```simple
  if rt_rwlock_try_read(self._handle) == 1
  ```
- **Line 177**: `rt_rwlock_unlock_read()`
  ```simple
  rt_rwlock_unlock_read(self._handle)
  ```
- **Line 186**: `rt_rwlock_write()`
  ```simple
  rt_rwlock_write(self._handle)
  ```
- **Line 188**: `rt_rwlock_unlock_write()`
  ```simple
  rt_rwlock_unlock_write(self._handle)
  ```
- **Line 195**: `rt_rwlock_try_write()`
  ```simple
  if rt_rwlock_try_write(self._handle) == 1
  ```
- **Line 197**: `rt_rwlock_unlock_write()`
  ```simple
  rt_rwlock_unlock_write(self._handle)
  ```
- **Line 205**: `rt_rwlock_write()`
  ```simple
  rt_rwlock_write(self._handle)
  ```
- **Line 207**: `rt_rwlock_unlock_write()`
  ```simple
  rt_rwlock_unlock_write(self._handle)
  ```
- **Line 222**: `rt_rwlock_free()`
  ```simple
  rt_rwlock_free(self._handle)
  ```
- **Line 262**: `rt_condvar_new()`
  ```simple
  val handle = rt_condvar_new()
  ```
- **Line 271**: `rt_condvar_wait()`
  ```simple
  rt_condvar_wait(self._handle, mutex._handle)
  ```
- **Line 278**: `rt_condvar_wait_timeout()`
  ```simple
  return rt_condvar_wait_timeout(self._handle, mutex._handle, millis) == 1
  ```
- **Line 284**: `rt_condvar_notify_one()`
  ```simple
  rt_condvar_notify_one(self._handle)
  ```
- **Line 290**: `rt_condvar_notify_all()`
  ```simple
  rt_condvar_notify_all(self._handle)
  ```
- **Line 293**: `rt_condvar_free()`
  ```simple
  rt_condvar_free(self._handle)
  ```
- **Line 330**: `rt_once_new()`
  ```simple
  val handle = rt_once_new()
  ```
- **Line 339**: `rt_once_call()`
  ```simple
  rt_once_call(self._handle, func as i64)
  ```
- **Line 357**: `rt_once_is_completed()`
  ```simple
  return self._completed or rt_once_is_completed(self._handle) == 1
  ```
- **Line 360**: `rt_once_free()`
  ```simple
  rt_once_free(self._handle)
  ```
- **Line 468**: `rt_thread_local_new()`
  ```simple
  val handle = rt_thread_local_new()
  ```
- **Line 475**: `rt_thread_local_get()`
  ```simple
  val ptr = rt_thread_local_get(self._handle)
  ```
- **Line 478**: `rt_thread_local_set()`
  ```simple
  rt_thread_local_set(self._handle, value as i64)
  ```
- **Line 486**: `rt_thread_local_set()`
  ```simple
  rt_thread_local_set(self._handle, value as i64)
  ```
- **Line 495**: `rt_thread_local_free()`
  ```simple
  rt_thread_local_free(self._handle)
  ```
- **Line 75**: `rt_mutex_new()`
  ```simple
  val handle = rt_mutex_new()
  ```
- **Line 83**: `rt_mutex_lock()`
  ```simple
  rt_mutex_lock(self._handle)
  ```
- **Line 85**: `rt_mutex_unlock()`
  ```simple
  rt_mutex_unlock(self._handle)
  ```
- **Line 93**: `rt_mutex_try_lock()`
  ```simple
  if rt_mutex_try_lock(self._handle) == 1
  ```
- **Line 95**: `rt_mutex_unlock()`
  ```simple
  rt_mutex_unlock(self._handle)
  ```

#### `rust/lib/std/src/lms/error.spl`

- **Line 152**: `rt_error()`
  ```simple
  pub fn is_transport_error(self) -> bool
  ```
- **Line 159**: `rt_error()`
  ```simple
  LmsError.TransportError("conn").is_transport_error()  # → true
  ```

#### `rust/lib/std/src/lms/server.spl`

- **Line 541**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 544**: `rt_file_exists()`
  ```simple
  fn _rt_file_exists(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 547**: `rt_file_exists()`
  ```simple
  if not _rt_file_exists(path.ptr(), path.len())
  ```
- **Line 551**: `rt_file_read_text()`
  ```simple
  val content = _rt_file_read_text(path.ptr(), path.len())
  ```

#### `rust/lib/std/src/lms/sys.spl`

- **Line 24**: `rt_env_get()`
  ```simple
  fn _rt_env_get(name_ptr: &u8, name_len: u64) -> Any
  ```
- **Line 26**: `rt_env_get()`
  ```simple
  val result = _rt_env_get(name.ptr(), name.len())
  ```

#### `rust/lib/std/src/mcp/mcp_common.spl`

- **Line 10**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```

#### `rust/lib/std/src/mcp/mcp_extended.spl`

- **Line 56**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 60**: `rt_time_now_unix_micros()`
  ```simple
  timestamp: _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```

#### `rust/lib/std/src/mcp/mcp_transform.spl`

- **Line 41**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```

#### `rust/lib/std/src/mcp/multi_lang/base_provider.spl`

- **Line 125**: `rt_item()`
  ```simple
  pub fn make_import_item(path: &str) -> McpItem:
  ```

#### `rust/lib/std/src/mcp/multi_lang/__init__.spl`

- **Line 660**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> Any
  ```
- **Line 662**: `rt_file_read_text()`
  ```simple
  val result = _rt_file_read_text(path.ptr(), path.len())
  ```

#### `rust/lib/std/src/mcp/multi_lang/javascript.spl`

- **Line 36**: `rt_item()`
  ```simple
  output.add_item(make_import_item("import"))
  ```

#### `rust/lib/std/src/mcp/multi_lang/python.spl`

- **Line 39**: `rt_path()`
  ```simple
  val path = self.get_import_path(&node, source)
  ```
- **Line 40**: `rt_item()`
  ```simple
  output.add_item(make_import_item(&path))
  ```
- **Line 59**: `rt_path()`
  ```simple
  fn get_import_path(node: &TreeNode, source: &str) -> text:
  ```

#### `rust/lib/std/src/mcp/multi_lang/rust_provider.spl`

- **Line 409**: `rt_byte()`
  ```simple
  extern fn ts_node_start_byte(node: i64) -> u32
  ```

#### `rust/lib/std/src/mcp/multi_lang/rust_treesitter.spl`

- **Line 126**: `rt_byte()`
  ```simple
  val start = ts_node_start_byte(handle)
  ```
- **Line 149**: `rt_byte()`
  ```simple
  fn start_byte() -> u32
  ```

#### `rust/lib/std/src/mcp/simple_lang/dependencies.spl`

- **Line 127**: `rt_alias()`
  ```simple
  val alias = parse_import_alias(stripped)
  ```
- **Line 188**: `rt_alias()`
  ```simple
  fn parse_import_alias(line: text) -> text:
  ```

#### `rust/lib/std/src/mcp/simple_lang/symbol_table.spl`

- **Line 541**: `rt_target()`
  ```simple
  val imported = extract_import_target(stripped)
  ```
- **Line 576**: `rt_target()`
  ```simple
  fn extract_import_target(line: text) -> text:
  ```

#### `rust/lib/std/src/mcp/tooling.spl`

- **Line 11**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 172**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 209**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 242**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 459**: `rt_task()`
  ```simple
  self.task_manager.start_task(new_task_id.clone())
  ```
- **Line 578**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 579**: `rt_time_now_unix_micros()`
  ```simple
  return _rt_time_now_unix_micros() as u64
  ```

#### `rust/lib/std/src/mixins/common.spl`

- **Line 52**: `rt_description()`
  ```simple
  fn short_description() -> text
  ```

#### `rust/lib/std/src/ml.disabled/engine/handlers.spl`

- **Line 213**: `rt_torch_save_checkpoint()`
  ```simple
  @rt_torch_save_checkpoint(model_handle, path.as_ptr(), path.len() as i32)
  ```
- **Line 270**: `rt_torch_clip_grad_norm()`
  ```simple
  return @rt_torch_clip_grad_norm(
  ```
- **Line 277**: `rt_torch_clip_grad_value()`
  ```simple
  @rt_torch_clip_grad_value(
  ```
- **Line 496**: `rt_torch_model_param_count()`
  ```simple
  val total_params = @rt_torch_model_param_count(model_handle)
  ```
- **Line 497**: `rt_torch_model_trainable_param_count()`
  ```simple
  val trainable_params = @rt_torch_model_trainable_param_count(model_handle)
  ```

#### `rust/lib/std/src/ml.disabled/engine/__init__.spl`

- **Line 268**: `rt_handlers_by_priority()`
  ```simple
  _sort_handlers_by_priority(self._event_handlers[event])
  ```
- **Line 95**: `rt_handlers_by_priority()`
  ```simple
  fn _sort_handlers_by_priority(handlers: any):
  ```

#### `rust/lib/std/src/ml.disabled/torch/autograd/__init__.spl`

- **Line 112**: `rt_torch_autograd_context_save_tensor()`
  ```simple
  val _ = @rt_torch_autograd_context_save_tensor(self.handle, tensor.handle)
  ```
- **Line 129**: `rt_torch_autograd_context_get_saved_tensors()`
  ```simple
  val _ = @rt_torch_autograd_context_get_saved_tensors(
  ```
- **Line 156**: `rt_torch_autograd_context_save_value()`
  ```simple
  val _ = @rt_torch_autograd_context_save_value(self.handle, key_ptr, key_len, value)
  ```
- **Line 174**: `rt_torch_autograd_context_get_value()`
  ```simple
  return @rt_torch_autograd_context_get_value(self.handle, key_ptr, key_len)
  ```
- **Line 311**: `rt_torch_checkpoint()`
  ```simple
  val _ = @rt_torch_checkpoint(
  ```
- **Line 97**: `rt_torch_autograd_context_new()`
  ```simple
  self.handle = @rt_torch_autograd_context_new()
  ```

#### `rust/lib/std/src/ml.disabled/torch/cache/__init__.spl`

- **Line 559**: `rt_async_load()`
  ```simple
  self.vocab_handle = self._start_async_load(vocab_path, prefault=true)
  ```
- **Line 562**: `rt_async_load()`
  ```simple
  self.merges_handle = self._start_async_load(merges_path, prefault=true)
  ```
- **Line 618**: `rt_async_load()`
  ```simple
  fn _start_async_load(path: str, prefault: bool) -> i64:
  ```
- **Line 632**: `rt_loading()`
  ```simple
  native_async_file_start_loading(handle)
  ```
- **Line 660**: `rt_loading()`
  ```simple
  extern fn native_async_file_start_loading(handle: i64) -> i32
  ```

#### `rust/lib/std/src/ml.disabled/torch/checkpoint.spl`

- **Line 117**: `rt_torch_checkpoint_len()`
  ```simple
  val count = rt_torch_checkpoint_len(handle)
  ```
- **Line 121**: `rt_torch_checkpoint_key()`
  ```simple
  val key = rt_torch_checkpoint_key(handle, i)
  ```
- **Line 124**: `rt_torch_checkpoint_value_type()`
  ```simple
  val value_type = rt_torch_checkpoint_value_type(handle, i)
  ```
- **Line 129**: `rt_torch_checkpoint_get_tensor()`
  ```simple
  val tensor_handle = rt_torch_checkpoint_get_tensor(handle, i)
  ```
- **Line 133**: `rt_torch_checkpoint_get_int()`
  ```simple
  val int_val = rt_torch_checkpoint_get_int(handle, i)
  ```
- **Line 137**: `rt_torch_checkpoint_get_float()`
  ```simple
  val float_val = rt_torch_checkpoint_get_float(handle, i)
  ```
- **Line 141**: `rt_torch_checkpoint_get_string()`
  ```simple
  val str_val = rt_torch_checkpoint_get_string(handle, i)
  ```
- **Line 145**: `rt_torch_checkpoint_get_nested()`
  ```simple
  val nested_handle = rt_torch_checkpoint_get_nested(handle, i)
  ```
- **Line 53**: `rt_torch_save()`
  ```simple
  val result = rt_torch_save(keys.as_ptr(), values.as_ptr(), keys.len() as i32, path.as_ptr(), path.len() as i32)
  ```
- **Line 88**: `rt_torch_load()`
  ```simple
  val handle = rt_torch_load(path.as_ptr(), path.len() as i32, device_code(device))
  ```
- **Line 97**: `rt_torch_checkpoint_free()`
  ```simple
  rt_torch_checkpoint_free(handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/data.spl`

- **Line 441**: `rt_torch_mnist_download()`
  ```simple
  val result = rt_torch_mnist_download(root_ptr, root_len)
  ```
- **Line 456**: `rt_torch_mnist_load()`
  ```simple
  val result = rt_torch_mnist_load(root_ptr, root_len, is_train, &images_handle, &labels_handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/device.spl`

- **Line 117**: `rt_name()`
  ```simple
  pub fn short_name(self) -> text
  ```
- **Line 124**: `rt_name()`
  ```simple
  Device.CUDA(0).short_name()  # → "cuda"
  ```
- **Line 125**: `rt_name()`
  ```simple
  Device.CPU.short_name()  # → "cpu"
  ```

#### `rust/lib/std/src/ml.disabled/torch/distributed/collective.spl`

- **Line 125**: `rt_torch_dist_broadcast()`
  ```simple
  val _ = @rt_torch_dist_broadcast(
  ```
- **Line 170**: `rt_torch_dist_reduce_scatter()`
  ```simple
  val _ = @rt_torch_dist_reduce_scatter(
  ```
- **Line 44**: `rt_torch_dist_all_reduce()`
  ```simple
  val _ = @rt_torch_dist_all_reduce(
  ```
- **Line 83**: `rt_torch_dist_all_gather()`
  ```simple
  val _ = @rt_torch_dist_all_gather(
  ```

#### `rust/lib/std/src/ml.disabled/torch/distributed/ddp.spl`

- **Line 103**: `rt_torch_dist_ddp_free()`
  ```simple
  val _ = @rt_torch_dist_ddp_free(self.handle)
  ```
- **Line 156**: `rt_torch_dist_ddp_set_sync()`
  ```simple
  val _ = @rt_torch_dist_ddp_set_sync(self.ddp.handle, 0)
  ```
- **Line 160**: `rt_torch_dist_ddp_set_sync()`
  ```simple
  val _ = @rt_torch_dist_ddp_set_sync(self.ddp.handle, 1)
  ```
- **Line 81**: `rt_torch_dist_ddp_new()`
  ```simple
  val _ = @rt_torch_dist_ddp_new(
  ```

#### `rust/lib/std/src/ml.disabled/torch/distributed/process_group.spl`

- **Line 121**: `rt_torch_dist_is_available()`
  ```simple
  return @rt_torch_dist_is_available() != 0
  ```
- **Line 151**: `rt_torch_dist_barrier()`
  ```simple
  val _ = @rt_torch_dist_barrier(_global_process_group.handle, timeout_seconds)
  ```
- **Line 40**: `rt_torch_dist_destroy_process_group()`
  ```simple
  val _ = @rt_torch_dist_destroy_process_group(self.handle)
  ```
- **Line 86**: `rt_torch_dist_init_process_group()`
  ```simple
  val _ = @rt_torch_dist_init_process_group(
  ```

#### `rust/lib/std/src/ml.disabled/torch/factory.spl`

- **Line 156**: `rt_torch_stack()`
  ```simple
  val result_handle = rt_torch_stack(handles.as_ptr(), handles.len() as i32, dim)
  ```
- **Line 191**: `rt_torch_where()`
  ```simple
  val result_handle = rt_torch_where(condition.handle, a.handle, b.handle)
  ```
- **Line 55**: `rt_torch_tensor()`
  ```simple
  val handle = rt_torch_tensor(flat_data.data_ptr(), flat_data.len() as i64, shape.data_ptr(), shape.len() as i32, dtype_code(dtype), device_code(device))
  ```

#### `rust/lib/std/src/ml.disabled/torch/fft.spl`

- **Line 107**: `rt_torch_irfft()`
  ```simple
  val handle = @rt_torch_irfft(x.handle, n, dim, norm)
  ```
- **Line 128**: `rt_torch_fftn()`
  ```simple
  val handle = @rt_torch_fftn(x.handle, dims.as_ptr() as u64, dims.len() as i32, norm)
  ```
- **Line 146**: `rt_torch_fftshift()`
  ```simple
  val handle = @rt_torch_fftshift(x.handle, dim)
  ```
- **Line 164**: `rt_torch_ifftshift()`
  ```simple
  val handle = @rt_torch_ifftshift(x.handle, dim)
  ```
- **Line 47**: `rt_torch_fft()`
  ```simple
  val handle = @rt_torch_fft(x.handle, n, dim, norm)
  ```
- **Line 67**: `rt_torch_ifft()`
  ```simple
  val handle = @rt_torch_ifft(x.handle, n, dim, norm)
  ```
- **Line 87**: `rt_torch_rfft()`
  ```simple
  val handle = @rt_torch_rfft(x.handle, n, dim, norm)
  ```

#### `rust/lib/std/src/ml.disabled/torch/linalg.spl`

- **Line 48**: `rt_torch_linalg_det()`
  ```simple
  val handle = @rt_torch_linalg_det(x.handle)
  ```
- **Line 66**: `rt_torch_linalg_inv()`
  ```simple
  val handle = @rt_torch_linalg_inv(x.handle)
  ```
- **Line 84**: `rt_torch_linalg_solve()`
  ```simple
  val handle = @rt_torch_linalg_solve(A.handle, b.handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/activations.spl`

- **Line 110**: `rt_torch_elu()`
  ```simple
  val handle = @rt_torch_elu(x.handle, alpha)
  ```
- **Line 127**: `rt_torch_softplus()`
  ```simple
  val handle = @rt_torch_softplus(x.handle, beta, threshold)
  ```
- **Line 143**: `rt_torch_leaky_relu()`
  ```simple
  val handle = @rt_torch_leaky_relu(x.handle, negative_slope)
  ```
- **Line 158**: `rt_torch_tanh()`
  ```simple
  val handle = @rt_torch_tanh(x.handle)
  ```
- **Line 173**: `rt_torch_sigmoid()`
  ```simple
  val handle = @rt_torch_sigmoid(x.handle)
  ```
- **Line 191**: `rt_torch_softmax()`
  ```simple
  val handle = @rt_torch_softmax(x.handle, dim)
  ```
- **Line 44**: `rt_torch_relu()`
  ```simple
  val handle = @rt_torch_relu(x.handle)
  ```
- **Line 62**: `rt_torch_gelu()`
  ```simple
  val handle = @rt_torch_gelu(x.handle)
  ```
- **Line 77**: `rt_torch_silu()`
  ```simple
  val handle = @rt_torch_silu(x.handle)
  ```
- **Line 92**: `rt_torch_mish()`
  ```simple
  val handle = @rt_torch_mish(x.handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/advanced_loss.spl`

- **Line 138**: `rt_torch_label_smoothing_loss()`
  ```simple
  val handle = @rt_torch_label_smoothing_loss(
  ```
- **Line 196**: `rt_torch_huber_loss()`
  ```simple
  val handle = @rt_torch_huber_loss(
  ```
- **Line 251**: `rt_torch_bce_with_logits_loss()`
  ```simple
  val handle = @rt_torch_bce_with_logits_loss(
  ```
- **Line 80**: `rt_torch_focal_loss()`
  ```simple
  val handle = @rt_torch_focal_loss(
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/base.spl`

- **Line 244**: `rt_my_layer_new()`
  ```simple
  self.module_handle = @rt_my_layer_new(config)
  ```
- **Line 248**: `rt_my_layer_forward()`
  ```simple
  val h = @rt_my_layer_forward(self.module_handle, x.handle)
  ```
- **Line 262**: `rt_torch_module_free()`
  ```simple
  val _ = @rt_torch_module_free(self.module_handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/dropout.spl`

- **Line 37**: `rt_torch_dropout_new()`
  ```simple
  self.module_handle = @rt_torch_dropout_new(p, 0)  # inplace=0
  ```
- **Line 49**: `rt_torch_dropout_forward()`
  ```simple
  val handle = @rt_torch_dropout_forward(
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/embedding.spl`

- **Line 41**: `rt_torch_embedding_new()`
  ```simple
  self.module_handle = @rt_torch_embedding_new(
  ```
- **Line 57**: `rt_torch_embedding_forward()`
  ```simple
  val handle = @rt_torch_embedding_forward(self.module_handle, indices.handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/grad.spl`

- **Line 42**: `rt_torch_clip_grad_value()`
  ```simple
  val grad_handle = @rt_torch_clip_grad_value(
  ```
- **Line 97**: `rt_torch_clip_grad_norm()`
  ```simple
  val total_norm = @rt_torch_clip_grad_norm(
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/init.spl`

- **Line 125**: `rt_torch_init_kaiming_uniform()`
  ```simple
  val handle = @rt_torch_init_kaiming_uniform(
  ```
- **Line 164**: `rt_torch_init_kaiming_normal()`
  ```simple
  val handle = @rt_torch_init_kaiming_normal(
  ```
- **Line 200**: `rt_torch_init_uniform()`
  ```simple
  val handle = @rt_torch_init_uniform(tensor.handle, low, high)
  ```
- **Line 225**: `rt_torch_init_normal()`
  ```simple
  val handle = @rt_torch_init_normal(tensor.handle, mean, std)
  ```
- **Line 246**: `rt_torch_init_constant()`
  ```simple
  val handle = @rt_torch_init_constant(tensor.handle, 0.0)
  ```
- **Line 267**: `rt_torch_init_constant()`
  ```simple
  val handle = @rt_torch_init_constant(tensor.handle, 1.0)
  ```
- **Line 289**: `rt_torch_init_constant()`
  ```simple
  val handle = @rt_torch_init_constant(tensor.handle, value)
  ```
- **Line 318**: `rt_torch_init_orthogonal()`
  ```simple
  val handle = @rt_torch_init_orthogonal(tensor.handle, gain)
  ```
- **Line 344**: `rt_torch_init_sparse()`
  ```simple
  val handle = @rt_torch_init_sparse(tensor.handle, sparsity, std)
  ```
- **Line 62**: `rt_torch_init_xavier_uniform()`
  ```simple
  val handle = @rt_torch_init_xavier_uniform(tensor.handle, gain)
  ```
- **Line 87**: `rt_torch_init_xavier_normal()`
  ```simple
  val handle = @rt_torch_init_xavier_normal(tensor.handle, gain)
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/linear.spl`

- **Line 43**: `rt_torch_linear_new()`
  ```simple
  self.module_handle = @rt_torch_linear_new(
  ```
- **Line 59**: `rt_torch_linear_forward()`
  ```simple
  val handle = @rt_torch_linear_forward(self.module_handle, x.handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/loss.spl`

- **Line 119**: `rt_torch_cross_entropy_loss()`
  ```simple
  val handle = @rt_torch_cross_entropy_loss(
  ```
- **Line 166**: `rt_torch_bce_loss()`
  ```simple
  val handle = @rt_torch_bce_loss(
  ```
- **Line 72**: `rt_torch_mse_loss()`
  ```simple
  val handle = @rt_torch_mse_loss(
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/normalization.spl`

- **Line 188**: `rt_torch_layernorm_new()`
  ```simple
  self.module_handle = @rt_torch_layernorm_new(
  ```
- **Line 205**: `rt_torch_layernorm_forward()`
  ```simple
  val handle = @rt_torch_layernorm_forward(self.module_handle, x.handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/recurrent.spl`

- **Line 141**: `rt_torch_lstm_new()`
  ```simple
  self.module_handle = @rt_torch_lstm_new(
  ```
- **Line 174**: `rt_torch_lstm_forward()`
  ```simple
  val _ = @rt_torch_lstm_forward(
  ```
- **Line 223**: `rt_torch_gru_new()`
  ```simple
  self.module_handle = @rt_torch_gru_new(
  ```
- **Line 250**: `rt_torch_gru_forward()`
  ```simple
  val _ = @rt_torch_gru_forward(
  ```
- **Line 67**: `rt_torch_rnn_new()`
  ```simple
  self.module_handle = @rt_torch_rnn_new(
  ```
- **Line 95**: `rt_torch_rnn_forward()`
  ```simple
  val _ = @rt_torch_rnn_forward(
  ```

#### `rust/lib/std/src/ml.disabled/torch/nn/transformer.spl`

- **Line 140**: `rt_torch_positional_encoding_new()`
  ```simple
  val handle = @rt_torch_positional_encoding_new(d_model, max_len)
  ```
- **Line 192**: `rt_torch_transformer_encoder_layer_new()`
  ```simple
  self.module_handle = @rt_torch_transformer_encoder_layer_new(
  ```
- **Line 214**: `rt_torch_transformer_encoder_layer_forward()`
  ```simple
  val handle = @rt_torch_transformer_encoder_layer_forward(
  ```
- **Line 255**: `rt_torch_transformer_decoder_layer_new()`
  ```simple
  self.module_handle = @rt_torch_transformer_decoder_layer_new(
  ```
- **Line 283**: `rt_torch_transformer_decoder_layer_forward()`
  ```simple
  val handle = @rt_torch_transformer_decoder_layer_forward(
  ```
- **Line 65**: `rt_torch_multihead_attention_new()`
  ```simple
  self.module_handle = @rt_torch_multihead_attention_new(
  ```
- **Line 91**: `rt_torch_multihead_attention_forward()`
  ```simple
  val _ = @rt_torch_multihead_attention_forward(
  ```

#### `rust/lib/std/src/ml.disabled/torch/onnx.spl`

- **Line 248**: `rt_onnx()`
  ```simple
  fn export_onnx(
  ```
- **Line 283**: `rt_onnx()`
  ```simple
  onnx.export_onnx(model, dummy_input, "model.onnx")
  ```
- **Line 286**: `rt_onnx()`
  ```simple
  onnx.export_onnx(
  ```
- **Line 299**: `rt_onnx()`
  ```simple
  onnx.export_onnx(
  ```
- **Line 349**: `rt_torch_onnx_export()`
  ```simple
  val result = @rt_torch_onnx_export(
  ```
- **Line 402**: `rt_torch_onnx_load()`
  ```simple
  @rt_torch_onnx_load(
  ```
- **Line 427**: `rt_onnx()`
  ```simple
  onnx.export_onnx(model, dummy_input, "model.onnx")
  ```
- **Line 441**: `rt_torch_onnx_check()`
  ```simple
  val result = @rt_torch_onnx_check(
  ```
- **Line 468**: `rt_torch_onnx_free()`
  ```simple
  @rt_torch_onnx_free(self.handle)
  ```
- **Line 487**: `rt_torch_onnx_run()`
  ```simple
  @rt_torch_onnx_run(
  ```
- **Line 523**: `rt_torch_jit_free()`
  ```simple
  @rt_torch_jit_free(self.handle)
  ```
- **Line 553**: `rt_torch_jit_forward()`
  ```simple
  @rt_torch_jit_forward(
  ```
- **Line 575**: `rt_torch_jit_eval()`
  ```simple
  @rt_torch_jit_eval(self.handle)
  ```
- **Line 583**: `rt_torch_jit_train()`
  ```simple
  @rt_torch_jit_train(self.handle, mode as i32)
  ```
- **Line 621**: `rt_torch_jit_script()`
  ```simple
  @rt_torch_jit_script(
  ```
- **Line 688**: `rt_torch_jit_trace()`
  ```simple
  @rt_torch_jit_trace(
  ```
- **Line 721**: `rt_torch_jit_save()`
  ```simple
  val result = @rt_torch_jit_save(
  ```
- **Line 758**: `rt_torch_jit_load()`
  ```simple
  @rt_torch_jit_load(
  ```

#### `rust/lib/std/src/ml.disabled/torch/optim/__init__.spl`

- **Line 134**: `rt_torch_sgd_new()`
  ```simple
  self.optimizer_handle = @rt_torch_sgd_new(
  ```
- **Line 192**: `rt_torch_adam_new()`
  ```simple
  self.optimizer_handle = @rt_torch_adam_new(
  ```
- **Line 251**: `rt_torch_adamw_new()`
  ```simple
  self.optimizer_handle = @rt_torch_adamw_new(
  ```
- **Line 317**: `rt_torch_rmsprop_new()`
  ```simple
  self.optimizer_handle = @rt_torch_rmsprop_new(
  ```
- **Line 359**: `rt_torch_optimizer_set_lr()`
  ```simple
  @rt_torch_optimizer_set_lr(self.optimizer.optimizer_handle, new_lr)
  ```
- **Line 481**: `rt_torch_cos()`
  ```simple
  val cosine_value = @rt_torch_cos(pi * progress)
  ```
- **Line 596**: `rt_torch_optimizer_set_lr()`
  ```simple
  @rt_torch_optimizer_set_lr(self.optimizer.optimizer_handle, new_lr)
  ```
- **Line 681**: `rt_torch_cos()`
  ```simple
  val cosine_value = @rt_torch_cos(pi * progress)
  ```
- **Line 71**: `rt_torch_optimizer_free()`
  ```simple
  @rt_torch_optimizer_free(self.optimizer_handle)
  ```
- **Line 765**: `rt_torch_cos()`
  ```simple
  val cosine_value = @rt_torch_cos(pi * progress)
  ```
- **Line 79**: `rt_torch_optimizer_zero_grad()`
  ```simple
  @rt_torch_optimizer_zero_grad(self.optimizer_handle)
  ```
- **Line 87**: `rt_torch_optimizer_step()`
  ```simple
  @rt_torch_optimizer_step(self.optimizer_handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/optim/schedulers.spl`

- **Line 144**: `rt_torch_optimizer_set_lr()`
  ```simple
  val _ = @rt_torch_optimizer_set_lr(self.optimizer.optimizer_handle, new_lr)
  ```
- **Line 239**: `rt_torch_optimizer_set_lr()`
  ```simple
  val _ = @rt_torch_optimizer_set_lr(self.optimizer.optimizer_handle, new_lr)
  ```
- **Line 369**: `rt_torch_optimizer_set_lr()`
  ```simple
  val _ = @rt_torch_optimizer_set_lr(self.optimizer.optimizer_handle, new_lr)
  ```
- **Line 440**: `rt_torch_cos()`
  ```simple
  return @rt_torch_cos(x)
  ```

#### `rust/lib/std/src/ml.disabled/torch/simple_math.spl`

- **Line 45**: `rt_torch_clamp()`
  ```simple
  val handle = @rt_torch_clamp(x.handle, min_val, max_val)
  ```
- **Line 64**: `rt_torch_where()`
  ```simple
  val handle = @rt_torch_where(cond.handle, x.handle, y.handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/tensor_class.spl`

- **Line 117**: `rt_torch_to_device()`
  ```simple
  val new_handle = rt_torch_to_device(self.handle, target_code)
  ```
- **Line 130**: `rt_torch_to_cpu()`
  ```simple
  val new_handle = rt_torch_to_cpu(self.handle)
  ```
- **Line 146**: `rt_torch_to_cuda()`
  ```simple
  val new_handle = rt_torch_to_cuda(self.handle, device_id)
  ```
- **Line 184**: `rt_torch_reshape()`
  ```simple
  val new_handle = rt_torch_reshape(self.handle, new_shape.data_ptr(), new_shape.len() as i32)
  ```
- **Line 201**: `rt_torch_transpose()`
  ```simple
  val new_handle = rt_torch_transpose(self.handle, dim0, dim1)
  ```
- **Line 20**: `rt_torch_free()`
  ```simple
  rt_torch_free(self.handle)
  ```
- **Line 25**: `rt_torch_zeros()`
  ```simple
  val handle = rt_torch_zeros(shape.data_ptr(), shape.len() as i32, dtype_code(dtype), device_code(device))
  ```
- **Line 305**: `rt_torch_add()`
  ```simple
  return Tensor(rt_torch_add(self.handle, other.handle))
  ```
- **Line 309**: `rt_torch_sub()`
  ```simple
  return Tensor(rt_torch_sub(self.handle, other.handle))
  ```
- **Line 30**: `rt_torch_ones()`
  ```simple
  val handle = rt_torch_ones(shape.data_ptr(), shape.len() as i32, dtype_code(dtype), device_code(device))
  ```
- **Line 313**: `rt_torch_mul()`
  ```simple
  return Tensor(rt_torch_mul(self.handle, other.handle))
  ```
- **Line 317**: `rt_torch_div()`
  ```simple
  return Tensor(rt_torch_div(self.handle, other.handle))
  ```
- **Line 321**: `rt_torch_matmul()`
  ```simple
  return Tensor(rt_torch_matmul(self.handle, other.handle))
  ```
- **Line 337**: `rt_torch_add_scalar()`
  ```simple
  return Tensor(rt_torch_add_scalar(self.handle, scalar))
  ```
- **Line 352**: `rt_torch_add_scalar()`
  ```simple
  return Tensor(rt_torch_add_scalar(self.handle, -scalar))
  ```
- **Line 35**: `rt_torch_randn()`
  ```simple
  val handle = rt_torch_randn(shape.data_ptr(), shape.len() as i32, dtype_code(dtype), device_code(device))
  ```
- **Line 367**: `rt_torch_mul_scalar()`
  ```simple
  return Tensor(rt_torch_mul_scalar(self.handle, scalar))
  ```
- **Line 382**: `rt_torch_mul_scalar()`
  ```simple
  return Tensor(rt_torch_mul_scalar(self.handle, 1.0 / scalar))
  ```
- **Line 394**: `rt_torch_mul_scalar()`
  ```simple
  return Tensor(rt_torch_mul_scalar(self.handle, -1.0))
  ```
- **Line 41**: `rt_torch_numel()`
  ```simple
  return rt_torch_numel(self.handle)
  ```
- **Line 430**: `rt_torch_sqrt()`
  ```simple
  return Tensor(rt_torch_sqrt(self.handle))
  ```
- **Line 453**: `rt_torch_gt()`
  ```simple
  return Tensor(rt_torch_gt(self.handle, other.handle))
  ```
- **Line 537**: `rt_torch_allclose()`
  ```simple
  return rt_torch_allclose(self.handle, other.handle, rtol, atol) != 0
  ```
- **Line 542**: `rt_torch_sum()`
  ```simple
  return Tensor(rt_torch_sum(self.handle, -1, 0))
  ```
- **Line 546**: `rt_torch_mean()`
  ```simple
  return Tensor(rt_torch_mean(self.handle, -1, 0))
  ```
- **Line 558**: `rt_torch_max()`
  ```simple
  return Tensor(rt_torch_max(self.handle, -1, 0))
  ```
- **Line 55**: `rt_torch_shape()`
  ```simple
  val ndim = rt_torch_shape(self.handle, buf.data_ptr(), 8)
  ```
- **Line 574**: `rt_torch_max()`
  ```simple
  return Tensor(rt_torch_max(self.handle, dim as i32, keepdim as i32))
  ```
- **Line 586**: `rt_torch_min()`
  ```simple
  return Tensor(rt_torch_min(self.handle, -1, 0))
  ```
- **Line 602**: `rt_torch_min()`
  ```simple
  return Tensor(rt_torch_min(self.handle, dim as i32, keepdim as i32))
  ```
- **Line 617**: `rt_torch_std()`
  ```simple
  return Tensor(rt_torch_std(self.handle, -1, 0, unbiased as i32))
  ```
- **Line 634**: `rt_torch_std()`
  ```simple
  return Tensor(rt_torch_std(self.handle, dim as i32, keepdim as i32, unbiased as i32))
  ```
- **Line 649**: `rt_torch_var()`
  ```simple
  return Tensor(rt_torch_var(self.handle, -1, 0, unbiased as i32))
  ```
- **Line 666**: `rt_torch_var()`
  ```simple
  return Tensor(rt_torch_var(self.handle, dim as i32, keepdim as i32, unbiased as i32))
  ```
- **Line 682**: `rt_torch_norm()`
  ```simple
  return Tensor(rt_torch_norm(self.handle, p, -1, 0))
  ```
- **Line 699**: `rt_torch_norm()`
  ```simple
  return Tensor(rt_torch_norm(self.handle, p, dim as i32, keepdim as i32))
  ```
- **Line 715**: `rt_torch_index()`
  ```simple
  return Tensor(rt_torch_index(self.handle, idx))
  ```
- **Line 733**: `rt_torch_select()`
  ```simple
  return Tensor(rt_torch_select(self.handle, dim as i32, idx))
  ```
- **Line 752**: `rt_torch_slice()`
  ```simple
  return Tensor(rt_torch_slice(self.handle, dim as i32, start, end, step))
  ```
- **Line 771**: `rt_torch_narrow()`
  ```simple
  return Tensor(rt_torch_narrow(self.handle, dim as i32, start, length))
  ```
- **Line 829**: `rt_torch_item()`
  ```simple
  return rt_torch_item(self.handle)
  ```
- **Line 833**: `rt_torch_clone()`
  ```simple
  return Tensor(rt_torch_clone(self.handle))
  ```
- **Line 838**: `rt_torch_set_requires_grad()`
  ```simple
  rt_torch_set_requires_grad(self.handle, requires_grad as i32)
  ```
- **Line 842**: `rt_torch_requires_grad()`
  ```simple
  return rt_torch_requires_grad(self.handle) != 0
  ```
- **Line 846**: `rt_torch_backward()`
  ```simple
  rt_torch_backward(self.handle, 0u64, 0)
  ```
- **Line 850**: `rt_torch_grad()`
  ```simple
  return Tensor(rt_torch_grad(self.handle))
  ```
- **Line 854**: `rt_torch_detach()`
  ```simple
  return Tensor(rt_torch_detach(self.handle))
  ```
- **Line 86**: `rt_torch_dtype()`
  ```simple
  val code = rt_torch_dtype(self.handle)
  ```
- **Line 99**: `rt_torch_device()`
  ```simple
  val code = rt_torch_device(self.handle)
  ```

#### `rust/lib/std/src/ml.disabled/torch/utils.spl`

- **Line 115**: `rt_torch_tensorboard_add_scalar()`
  ```simple
  @rt_torch_tensorboard_add_scalar(
  ```
- **Line 138**: `rt_torch_tensorboard_add_histogram()`
  ```simple
  @rt_torch_tensorboard_add_histogram(
  ```
- **Line 159**: `rt_torch_tensorboard_add_image()`
  ```simple
  @rt_torch_tensorboard_add_image(
  ```
- **Line 180**: `rt_torch_tensorboard_add_graph()`
  ```simple
  @rt_torch_tensorboard_add_graph(
  ```
- **Line 188**: `rt_torch_tensorboard_flush()`
  ```simple
  @rt_torch_tensorboard_flush(self.handle)
  ```
- **Line 192**: `rt_torch_tensorboard_close()`
  ```simple
  @rt_torch_tensorboard_close(self.handle)
  ```
- **Line 284**: `rt_torch_save_checkpoint()`
  ```simple
  @rt_torch_save_checkpoint(
  ```
- **Line 318**: `rt_torch_load_checkpoint()`
  ```simple
  @rt_torch_load_checkpoint(
  ```
- **Line 376**: `rt_torch_load_pretrained_model()`
  ```simple
  @rt_torch_load_pretrained_model(
  ```
- **Line 599**: `rt_torch_amp_unscale_gradients()`
  ```simple
  @rt_torch_amp_unscale_gradients(optimizer.handle, self.scale)
  ```
- **Line 602**: `rt_torch_amp_check_inf_nan()`
  ```simple
  val has_inf_nan = @rt_torch_amp_check_inf_nan(optimizer.handle)
  ```
- **Line 628**: `rt_model()`
  ```simple
  model = AMP.convert_model(model)
  ```
- **Line 648**: `rt_model()`
  ```simple
  fn convert_model(model: nn.Module) -> nn.Module:
  ```
- **Line 657**: `rt_torch_amp_convert_model()`
  ```simple
  @rt_torch_amp_convert_model(model.handle)
  ```
- **Line 84**: `rt_torch_tensorboard_create()`
  ```simple
  Calls rt_torch_tensorboard_create(log_dir, comment)
  ```
- **Line 93**: `rt_torch_tensorboard_create()`
  ```simple
  self.handle = @rt_torch_tensorboard_create(
  ```

#### `rust/lib/std/src/ml.disabled/torch/vision.spl`

- **Line 146**: `rt_torch_module_forward()`
  ```simple
  @rt_torch_module_forward(self.handle, x.handle, &output_handle)
  ```
- **Line 204**: `rt_torch_module_forward()`
  ```simple
  @rt_torch_module_forward(self.handle, x.handle, &output_handle)
  ```
- **Line 249**: `rt_torch_module_forward()`
  ```simple
  @rt_torch_module_forward(self.handle, x.handle, &output_handle)
  ```
- **Line 298**: `rt_torch_module_forward()`
  ```simple
  @rt_torch_module_forward(self.handle, x.handle, &output_handle)
  ```
- **Line 336**: `rt_torch_module_forward()`
  ```simple
  @rt_torch_module_forward(self.handle, x.handle, &output_handle)
  ```
- **Line 363**: `rt_torch_vision_load_image()`
  ```simple
  @rt_torch_vision_load_image(filepath_ptr, filepath_len, &handle)
  ```
- **Line 383**: `rt_torch_vision_save_image()`
  ```simple
  @rt_torch_vision_save_image(tensor.handle, filepath_ptr, filepath_len)
  ```
- **Line 408**: `rt_torch_vision_preprocess_imagenet()`
  ```simple
  @rt_torch_vision_preprocess_imagenet(image.handle, &output_handle)
  ```
- **Line 501**: `rt_torch_vision_imagenet_count()`
  ```simple
  @rt_torch_vision_imagenet_count(root_ptr, root_len, split_ptr, split_len, &count)
  ```
- **Line 518**: `rt_torch_vision_imagenet_getitem()`
  ```simple
  @rt_torch_vision_imagenet_getitem(
  ```

#### `rust/lib/std/src/ml.disabled/tracking/__init__.spl`

- **Line 283**: `rt_dir_list()`
  ```simple
  val entries = rt_dir_list(path)
  ```
- **Line 569**: `rt_time_now_seconds()`
  ```simple
  val timestamp = rt_time_now_seconds()
  ```
- **Line 576**: `rt_time_now_seconds()`
  ```simple
  val timestamp = rt_time_now_seconds()
  ```

#### `rust/lib/std/src/package_ffi.spl`

- **Line 23**: `rt_package_create_tarball()`
  ```simple
  rt_package_create_tarball(source_dir, output_path) == 0
  ```
- **Line 26**: `rt_package_extract_tarball()`
  ```simple
  rt_package_extract_tarball(tarball_path, dest_dir) == 0
  ```
- **Line 29**: `rt_package_file_size()`
  ```simple
  rt_package_file_size(file_path)
  ```
- **Line 32**: `rt_package_copy_file()`
  ```simple
  rt_package_copy_file(src_path, dst_path) == 0
  ```
- **Line 35**: `rt_package_mkdir_all()`
  ```simple
  rt_package_mkdir_all(dir_path) == 0
  ```
- **Line 38**: `rt_package_remove_dir_all()`
  ```simple
  rt_package_remove_dir_all(dir_path) == 0
  ```
- **Line 41**: `rt_package_create_symlink()`
  ```simple
  rt_package_create_symlink(target, link_path) == 0
  ```
- **Line 44**: `rt_package_chmod()`
  ```simple
  rt_package_chmod(file_path, mode) == 0
  ```
- **Line 47**: `rt_package_exists()`
  ```simple
  rt_package_exists(path) == 1
  ```
- **Line 50**: `rt_package_is_dir()`
  ```simple
  rt_package_is_dir(path) == 1
  ```

#### `rust/lib/std/src/parser.disabled/treesitter/optimize.spl`

- **Line 94**: `rt_time_now_unix_micros()`
  ```simple
  timestamp: _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 9**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```

#### `rust/lib/std/src/physics/collision/gjk.spl`

- **Line 120**: `rt_a()`
  ```simple
  val point_a = support_a(direction)
  ```
- **Line 121**: `rt_b()`
  ```simple
  val point_b = support_b(direction.negate())
  ```

#### `rust/lib/std/src/physics/collision/__init__.spl`

- **Line 359**: `rt_by_axis()`
  ```simple
  var sorted_aabbs = BVH._sort_by_axis(indexed_aabbs, split_axis)
  ```
- **Line 390**: `rt_by_axis()`
  ```simple
  static fn _sort_by_axis(aabbs: [(i64, AABB)], axis: i64) -> [(i64, AABB)]:
  ```

#### `rust/lib/std/src/sdn/document.spl`

- **Line 180**: `rt_file_write_text()`
  ```simple
  val result = rt_file_write_text(path, content)
  ```
- **Line 53**: `rt_file_exists()`
  ```simple
  if not rt_file_exists(path)
  ```
- **Line 56**: `rt_file_read_text()`
  ```simple
  val source = rt_file_read_text(path)
  ```

#### `rust/lib/std/src/sdn/query.spl`

- **Line 253**: `rt_rows()`
  ```simple
  result = self.sort_rows(result, col, self.order_dir)
  ```
- **Line 322**: `rt_rows()`
  ```simple
  fn sort_rows(rows: List<Row>, column: text, order: Order) -> List<Row>:
  ```

#### `rust/lib/std/src/shell.spl`

- **Line 100**: `rt_file_read_text()`
  ```simple
  return rt_file_read_text(path)
  ```
- **Line 103**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(path, content)
  ```
- **Line 106**: `rt_file_read_text()`
  ```simple
  val existing = rt_file_read_text(path)
  ```
- **Line 107**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(path, existing + content)
  ```
- **Line 110**: `rt_file_exists()`
  ```simple
  return rt_file_exists(path)
  ```
- **Line 113**: `rt_file_copy()`
  ```simple
  rt_file_copy(src, dest)
  ```
- **Line 116**: `rt_file_rename()`
  ```simple
  rt_file_rename(src, dest)
  ```
- **Line 119**: `rt_file_remove()`
  ```simple
  rt_file_remove(path)
  ```
- **Line 124**: `rt_dir_walk()`
  ```simple
  val all_files = rt_dir_walk(directory)
  ```
- **Line 129**: `rt_path_basename()`
  ```simple
  val fname = rt_path_basename(fpath)
  ```
- **Line 133**: `rt_file_find()`
  ```simple
  return rt_file_find(directory, pattern, recursive)
  ```
- **Line 153**: `rt_dir_list()`
  ```simple
  return rt_dir_list(path)
  ```
- **Line 156**: `rt_dir_glob()`
  ```simple
  return rt_dir_glob(path, pattern)
  ```
- **Line 159**: `rt_dir_create()`
  ```simple
  rt_dir_create(path, recursive)
  ```
- **Line 162**: `rt_dir_create()`
  ```simple
  rt_dir_create(path, true)
  ```
- **Line 165**: `rt_dir_remove()`
  ```simple
  rt_dir_remove(path, recursive)
  ```
- **Line 168**: `rt_dir_remove()`
  ```simple
  rt_dir_remove(path, true)
  ```
- **Line 171**: `rt_file_exists()`
  ```simple
  return rt_file_exists(path)
  ```
- **Line 179**: `rt_path_separator()`
  ```simple
  val separator = rt_path_separator()
  ```
- **Line 192**: `rt_path_basename()`
  ```simple
  return rt_path_basename(p)
  ```
- **Line 195**: `rt_path_dirname()`
  ```simple
  return rt_path_dirname(p)
  ```
- **Line 198**: `rt_path_ext()`
  ```simple
  return rt_path_ext(p)
  ```
- **Line 201**: `rt_path_absolute()`
  ```simple
  return rt_path_absolute(p)
  ```
- **Line 206**: `rt_env_get()`
  ```simple
  val result = rt_env_get(name)
  ```
- **Line 212**: `rt_env_set()`
  ```simple
  rt_env_set(name, value)
  ```
- **Line 215**: `rt_env_cwd()`
  ```simple
  return rt_env_cwd()
  ```
- **Line 58**: `rt_process_run()`
  ```simple
  val (stdout, stderr, exit_code) = rt_process_run(cmd, args)
  ```

#### `rust/lib/std/src/simd/intrinsics.spl`

- **Line 27**: `rt_math_sqrt()`
  ```simple
  x: rt_math_sqrt(v.x),
  ```
- **Line 28**: `rt_math_sqrt()`
  ```simple
  y: rt_math_sqrt(v.y),
  ```
- **Line 29**: `rt_math_sqrt()`
  ```simple
  z: rt_math_sqrt(v.z),
  ```
- **Line 30**: `rt_math_sqrt()`
  ```simple
  w: rt_math_sqrt(v.w)
  ```
- **Line 38**: `rt_math_sqrt()`
  ```simple
  x: 1.0 / rt_math_sqrt(v.x),
  ```
- **Line 39**: `rt_math_sqrt()`
  ```simple
  y: 1.0 / rt_math_sqrt(v.y),
  ```
- **Line 40**: `rt_math_sqrt()`
  ```simple
  z: 1.0 / rt_math_sqrt(v.z),
  ```
- **Line 41**: `rt_math_sqrt()`
  ```simple
  w: 1.0 / rt_math_sqrt(v.w)
  ```

#### `rust/lib/std/src/spec/coverage/html.spl`

- **Line 310**: `rt_with_source()`
  ```simple
  fn generate_html_report_with_source(calculator: CoverageCalculator, path: text):
  ```

#### `rust/lib/std/src/spec/coverage/json.spl`

- **Line 237**: `rt_coverage_json()`
  ```simple
  fn export_coverage_json(calculator: CoverageCalculator, path: text):
  ```
- **Line 242**: `rt_coverage_json_compact()`
  ```simple
  fn export_coverage_json_compact(calculator: CoverageCalculator, path: text):
  ```
- **Line 252**: `rt_codecov()`
  ```simple
  fn export_codecov(calculator: CoverageCalculator, path: text):
  ```
- **Line 258**: `rt_coveralls()`
  ```simple
  fn export_coveralls(calculator: CoverageCalculator, path: text):
  ```

#### `rust/lib/std/src/spec/diagram.spl`

- **Line 316**: `rt_diagram_trace_method()`
  ```simple
  rt_diagram_trace_method("", name)
  ```
- **Line 321**: `rt_diagram_trace_method_with_args()`
  ```simple
  rt_diagram_trace_method_with_args(class_name, method_name, args_str)
  ```
- **Line 326**: `rt_diagram_trace_return()`
  ```simple
  rt_diagram_trace_return(v)
  ```
- **Line 328**: `rt_diagram_trace_return()`
  ```simple
  rt_diagram_trace_return("")
  ```
- **Line 331**: `rt_diagram_mark_architectural()`
  ```simple
  rt_diagram_mark_architectural(entity)
  ```
- **Line 406**: `rt_diagram_enable()`
  ```simple
  rt_diagram_enable()
  ```
- **Line 409**: `rt_diagram_disable()`
  ```simple
  rt_diagram_disable()
  ```
- **Line 412**: `rt_diagram_clear()`
  ```simple
  rt_diagram_clear()
  ```
- **Line 415**: `rt_diagram_generate_sequence()`
  ```simple
  return rt_diagram_generate_sequence()
  ```
- **Line 418**: `rt_diagram_generate_class()`
  ```simple
  return rt_diagram_generate_class()
  ```
- **Line 421**: `rt_diagram_generate_arch()`
  ```simple
  return rt_diagram_generate_arch()
  ```

#### `rust/lib/std/src/spec/matchers/text.spl`

- **Line 43**: `rt_with()`
  ```simple
  fn start_with(expected_prefix: text) -> StartWithMatcher:
  ```

#### `rust/lib/std/src/spec/mode_config_parser.spl`

- **Line 192**: `rt_file_exists()`
  ```simple
  if not rt_file_exists(toml_path)
  ```
- **Line 196**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text(toml_path)
  ```
- **Line 208**: `rt_file_exists()`
  ```simple
  if not rt_file_exists(sdn_path)
  ```
- **Line 212**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text(sdn_path)
  ```
- **Line 235**: `rt_file_exists()`
  ```simple
  if not rt_file_exists(file_path)
  ```
- **Line 239**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text(file_path)
  ```
- **Line 306**: `rt_path_dirname()`
  ```simple
  var current_dir = rt_path_dirname(file_path)
  ```
- **Line 315**: `rt_file_exists()`
  ```simple
  if rt_file_exists(toml_path)
  ```
- **Line 320**: `rt_file_exists()`
  ```simple
  if rt_file_exists(git_path)
  ```
- **Line 324**: `rt_path_dirname()`
  ```simple
  val parent = rt_path_dirname(current_dir)
  ```
- **Line 339**: `rt_path_dirname()`
  ```simple
  val dirname = rt_path_dirname(file_path)
  ```

#### `rust/lib/std/src/spec/mode_reporter.spl`

- **Line 133**: `rt_timings()`
  ```simple
  val sorted_timings = sort_timings(comparison.mode_timings)
  ```
- **Line 143**: `rt_timings()`
  ```simple
  fn sort_timings(timings: List<ModeTiming>) -> List<ModeTiming>:
  ```

#### `rust/lib/std/src/spec/progress.spl`

- **Line 12**: `rt_progress_init()`
  ```simple
  rt_progress_init()
  ```
- **Line 17**: `rt_progress_reset()`
  ```simple
  rt_progress_reset()
  ```
- **Line 22**: `rt_progress_get_elapsed_seconds()`
  ```simple
  return rt_progress_get_elapsed_seconds()
  ```

#### `rust/lib/std/src/spec/property/runner.spl`

- **Line 143**: `rt_thread_spawn_isolated()`
  ```simple
  val handle = rt_thread_spawn_isolated(f, ())
  ```
- **Line 154**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(poll_interval_ms)
  ```

#### `rust/lib/std/src/spec/screenshot.spl`

- **Line 57**: `rt_screenshot_enable()`
  ```simple
  rt_screenshot_enable()
  ```
- **Line 60**: `rt_screenshot_disable()`
  ```simple
  rt_screenshot_disable()
  ```
- **Line 63**: `rt_screenshot_is_enabled()`
  ```simple
  return rt_screenshot_is_enabled()
  ```
- **Line 66**: `rt_screenshot_set_refresh()`
  ```simple
  rt_screenshot_set_refresh(refresh)
  ```
- **Line 69**: `rt_screenshot_set_output_dir()`
  ```simple
  rt_screenshot_set_output_dir(dir)
  ```
- **Line 72**: `rt_screenshot_set_context()`
  ```simple
  rt_screenshot_set_context(test_file=test_file, test_name=test_name)
  ```
- **Line 75**: `rt_screenshot_clear_context()`
  ```simple
  rt_screenshot_clear_context()
  ```
- **Line 78**: `rt_screenshot_capture_before_terminal()`
  ```simple
  return rt_screenshot_capture_before_terminal(buffer)
  ```
- **Line 81**: `rt_screenshot_capture_after_terminal()`
  ```simple
  return rt_screenshot_capture_after_terminal(buffer)
  ```
- **Line 89**: `rt_screenshot_exists()`
  ```simple
  return rt_screenshot_exists(capture_type)
  ```
- **Line 92**: `rt_screenshot_get_path()`
  ```simple
  return rt_screenshot_get_path(capture_type)
  ```
- **Line 95**: `rt_screenshot_clear_captures()`
  ```simple
  rt_screenshot_clear_captures()
  ```

#### `rust/lib/std/src/spec/snapshot/runner.spl`

- **Line 186**: `rt_reflect_source_file()`
  ```simple
  fn _rt_reflect_source_file() -> text
  ```
- **Line 188**: `rt_reflect_source_file()`
  ```simple
  val file = _rt_reflect_source_file()
  ```
- **Line 198**: `rt_reflect_function_name()`
  ```simple
  fn _rt_reflect_function_name() -> text
  ```
- **Line 200**: `rt_reflect_function_name()`
  ```simple
  val name = _rt_reflect_function_name()
  ```

#### `rust/lib/std/src/sys/args.spl`

- **Line 12**: `rt_args_count()`
  ```simple
  return rt_args_count()
  ```
- **Line 16**: `rt_args_count()`
  ```simple
  if index < 0 or index >= rt_args_count()
  ```
- **Line 18**: `rt_args_get()`
  ```simple
  return Option.some(rt_args_get(index))
  ```
- **Line 22**: `rt_args_all()`
  ```simple
  return rt_args_all()
  ```
- **Line 26**: `rt_args_count()`
  ```simple
  if rt_args_count() > 0
  ```
- **Line 27**: `rt_args_get()`
  ```simple
  return rt_args_get(0)
  ```
- **Line 32**: `rt_args_all()`
  ```simple
  val all_args = rt_args_all()
  ```
- **Line 39**: `rt_args_all()`
  ```simple
  for arg in rt_args_all()
  ```
- **Line 46**: `rt_args_all()`
  ```simple
  val all_args = rt_args_all()
  ```

#### `rust/lib/std/src/sys/env.spl`

- **Line 17**: `rt_env_get()`
  ```simple
  return rt_env_get(name)
  ```
- **Line 21**: `rt_env_get()`
  ```simple
  val value = rt_env_get(name)
  ```
- **Line 28**: `rt_env_exists()`
  ```simple
  if rt_env_exists(name)
  ```
- **Line 29**: `rt_env_get()`
  ```simple
  return Option.some(rt_env_get(name))
  ```
- **Line 34**: `rt_env_set()`
  ```simple
  return rt_env_set(name, value)
  ```
- **Line 38**: `rt_env_remove()`
  ```simple
  return rt_env_remove(name)
  ```
- **Line 42**: `rt_env_exists()`
  ```simple
  return rt_env_exists(name)
  ```
- **Line 46**: `rt_env_all()`
  ```simple
  return rt_env_all()
  ```
- **Line 50**: `rt_env_cwd()`
  ```simple
  return rt_env_cwd()
  ```
- **Line 54**: `rt_env_home()`
  ```simple
  return rt_env_home()
  ```
- **Line 58**: `rt_env_temp()`
  ```simple
  return rt_env_temp()
  ```

#### `rust/lib/std/src/sys/fault_detection.spl`

- **Line 100**: `rt_fault_set_max_recursion_depth()`
  ```simple
  rt_fault_set_max_recursion_depth(config.max_recursion_depth)
  ```
- **Line 102**: `rt_fault_set_timeout()`
  ```simple
  rt_fault_set_timeout(config.timeout_secs)
  ```
- **Line 104**: `rt_fault_set_timeout()`
  ```simple
  rt_fault_set_timeout(0)
  ```
- **Line 106**: `rt_fault_set_execution_limit()`
  ```simple
  rt_fault_set_execution_limit(config.execution_limit)
  ```
- **Line 111**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(true)
  ```
- **Line 112**: `rt_fault_set_max_recursion_depth()`
  ```simple
  rt_fault_set_max_recursion_depth(DEFAULT_MAX_RECURSION_DEPTH)
  ```
- **Line 116**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(false)
  ```
- **Line 120**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(true)
  ```
- **Line 121**: `rt_fault_set_max_recursion_depth()`
  ```simple
  rt_fault_set_max_recursion_depth(depth)
  ```
- **Line 125**: `rt_fault_set_timeout()`
  ```simple
  rt_fault_set_timeout(secs)
  ```
- **Line 129**: `rt_fault_set_execution_limit()`
  ```simple
  rt_fault_set_execution_limit(limit)
  ```
- **Line 98**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(config.stack_overflow_enabled)
  ```

#### `rust/lib/std/src/sys.spl`

- **Line 51**: `rt_get_args()`
  ```simple
  return rt_get_args()
  ```
- **Line 55**: `rt_exit()`
  ```simple
  rt_exit(code as i32)
  ```
- **Line 60**: `rt_exit()`
  ```simple
  rt_exit(code)
  ```

#### `rust/lib/std/src/testing/fuzz.spl`

- **Line 98**: `rt_time_now_seconds()`
  ```simple
  (random.rt_time_now_seconds() * 1000000.0) as i32
  ```

#### `rust/lib/std/src/testing/helpers.spl`

- **Line 102**: `rt_contains()`
  ```simple
  assert_contains(users, "Alice", "Should contain Alice")
  ```
- **Line 116**: `rt_not_contains()`
  ```simple
  assert_not_contains(blocked_users, "Alice", "Should not be blocked")
  ```
- **Line 129**: `rt_empty()`
  ```simple
  assert_empty(errors, "Should have no errors")
  ```
- **Line 143**: `rt_len()`
  ```simple
  assert_len(results, 5, "Should have 5 results")
  ```
- **Line 164**: `rt_ok()`
  ```simple
  val data = assert_ok(parse_json(input), "Should parse successfully")
  ```
- **Line 17**: `rt_eq()`
  ```simple
  assert_eq(result, 42, "Result should be 42")
  ```
- **Line 181**: `rt_err()`
  ```simple
  val error = assert_err(parse_invalid(), "Should fail to parse")
  ```
- **Line 223**: `rt_fast()`
  ```simple
  val result = assert_fast(: quick_lookup(), 1000, "Should be under 1ms")
  ```
- **Line 288**: `rt_called()`
  ```simple
  pub fn assert_called(mock_fn, expected_count: i32):
  ```
- **Line 296**: `rt_called()`
  ```simple
  assert_called(save_mock, 3)
  ```
- **Line 302**: `rt_called_with()`
  ```simple
  pub fn assert_called_with(mock_fn, expected_args: List<text>):
  ```
- **Line 310**: `rt_called_with()`
  ```simple
  assert_called_with(save_mock, ["user123", "data"])
  ```
- **Line 31**: `rt_ne()`
  ```simple
  assert_ne(result, 0, "Result should not be zero")
  ```
- **Line 320**: `rt_not_called()`
  ```simple
  pub fn assert_not_called(mock_fn)
  ```
- **Line 327**: `rt_not_called()`
  ```simple
  assert_not_called(error_handler_mock)
  ```
- **Line 36**: `rt_true()`
  ```simple
  pub fn assert_true(condition: bool, message: text):
  ```
- **Line 44**: `rt_true()`
  ```simple
  assert_true(user.is_active(), "User should be active")
  ```
- **Line 49**: `rt_false()`
  ```simple
  pub fn assert_false(condition: bool, message: text):
  ```
- **Line 57**: `rt_false()`
  ```simple
  assert_false(user.is_deleted(), "User should not be deleted")
  ```
- **Line 73**: `rt_some()`
  ```simple
  val user = assert_some(find_user("id123"), "User should exist")
  ```
- **Line 87**: `rt_none()`
  ```simple
  assert_none(find_user("invalid"), "User should not exist")
  ```

#### `rust/lib/std/src/tooling/algorithm_utils.spl`

- **Line 61**: `rt_partition()`
  ```simple
  fn quick_sort_partition(list: List<i32>, low: i32, high: i32) -> (List<i32>, i32):
  ```
- **Line 82**: `rt_helper()`
  ```simple
  fn quick_sort_helper(list: List<i32>, low: i32, high: i32) -> List<i32>:
  ```
- **Line 84**: `rt_partition()`
  ```simple
  val (partitioned, pi) = quick_sort_partition(list=list, low=low, high=high)
  ```
- **Line 85**: `rt_helper()`
  ```simple
  val left_sorted = quick_sort_helper(list=partitioned, low=low, high=pi - 1)
  ```
- **Line 86**: `rt_helper()`
  ```simple
  return quick_sort_helper(list=left_sorted, low=pi + 1, high=high)
  ```
- **Line 95**: `rt_helper()`
  ```simple
  quick_sort_helper(list=list, low=0, high=list.len() - 1)
  ```

#### `rust/lib/std/src/tooling/arg_parsing.spl`

- **Line 34**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(true)
  ```
- **Line 37**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(true)
  ```

#### `rust/lib/std/src/tooling/brief_view.spl`

- **Line 557**: `rt_file_exists()`
  ```simple
  if not rt_file_exists(file_path)
  ```
- **Line 560**: `rt_file_read_text()`
  ```simple
  val source = rt_file_read_text(file_path)
  ```

#### `rust/lib/std/src/tooling/compiler/build_system.spl`

- **Line 509**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 512**: `rt_time_now_unix_micros()`
  ```simple
  val start_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 543**: `rt_time_now_unix_micros()`
  ```simple
  val end_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 768**: `rt_file_exists()`
  ```simple
  fn _rt_file_exists(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 770**: `rt_file_exists()`
  ```simple
  if _rt_file_exists(profile_data.ptr(), profile_data.len())
  ```
- **Line 787**: `rt_platform_name()`
  ```simple
  fn _rt_platform_name() -> text
  ```
- **Line 789**: `rt_platform_name()`
  ```simple
  val platform = _rt_platform_name()
  ```
- **Line 819**: `rt_platform_name()`
  ```simple
  fn _rt_platform_name() -> text
  ```
- **Line 821**: `rt_platform_name()`
  ```simple
  val platform = _rt_platform_name()
  ```
- **Line 846**: `rt_dir_remove()`
  ```simple
  fn _rt_dir_remove(path_ptr: &u8, path_len: u64, recursive: bool) -> bool
  ```
- **Line 855**: `rt_dir_remove()`
  ```simple
  val success = _rt_dir_remove(build_dir.ptr(), build_dir.len(), true)
  ```

#### `rust/lib/std/src/tooling/compiler/compiler_interface.spl`

- **Line 846**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 849**: `rt_time_now_unix_micros()`
  ```simple
  val start_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 876**: `rt_time_now_unix_micros()`
  ```simple
  val end_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```

#### `rust/lib/std/src/tooling/compiler/c.spl`

- **Line 10**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 246**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 273**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 293**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 66**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```

#### `rust/lib/std/src/tooling/compiler/go.spl`

- **Line 10**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 158**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 186**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 205**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 221**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 80**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```

#### `rust/lib/std/src/tooling/compiler/javascript.spl`

- **Line 10**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 167**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 193**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 212**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 89**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```

#### `rust/lib/std/src/tooling/compiler/python.spl`

- **Line 102**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 105**: `rt_time_now_unix_micros()`
  ```simple
  val start_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 119**: `rt_time_now_unix_micros()`
  ```simple
  val end_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 251**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 258**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```

#### `rust/lib/std/src/tooling/compiler/rust.spl`

- **Line 121**: `rt_time_now_unix_micros()`
  ```simple
  val end_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 149**: `rt_platform_name()`
  ```simple
  fn _rt_platform_name() -> text
  ```
- **Line 151**: `rt_platform_name()`
  ```simple
  val platform = _rt_platform_name()
  ```
- **Line 164**: `rt_platform_name()`
  ```simple
  fn _rt_platform_name() -> text
  ```
- **Line 166**: `rt_platform_name()`
  ```simple
  val platform = _rt_platform_name()
  ```
- **Line 79**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 82**: `rt_time_now_unix_micros()`
  ```simple
  val start_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```

#### `rust/lib/std/src/tooling/compiler/simple.spl`

- **Line 102**: `rt_time_now_unix_micros()`
  ```simple
  val start_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 147**: `rt_time_now_unix_micros()`
  ```simple
  val end_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 175**: `rt_platform_name()`
  ```simple
  fn _rt_platform_name() -> text
  ```
- **Line 177**: `rt_platform_name()`
  ```simple
  val platform = _rt_platform_name()
  ```
- **Line 190**: `rt_platform_name()`
  ```simple
  fn _rt_platform_name() -> text
  ```
- **Line 192**: `rt_platform_name()`
  ```simple
  val platform = _rt_platform_name()
  ```
- **Line 99**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```

#### `rust/lib/std/src/tooling/compiler/symbol_analysis.spl`

- **Line 200**: `rt_ratio()`
  ```simple
  fn export_ratio() -> f64
  ```

#### `rust/lib/std/src/tooling/config_env.spl`

- **Line 261**: `rt_env_all()`
  ```simple
  val env_tuples = rt_env_all()
  ```
- **Line 272**: `rt_env_exists()`
  ```simple
  if rt_env_exists(key)
  ```
- **Line 273**: `rt_env_get()`
  ```simple
  return Some(rt_env_get(key))
  ```
- **Line 279**: `rt_env_set()`
  ```simple
  rt_env_set(key, value)
  ```
- **Line 283**: `rt_env_remove()`
  ```simple
  rt_env_remove(key)
  ```
- **Line 287**: `rt_env_home()`
  ```simple
  val home = rt_env_home()
  ```
- **Line 295**: `rt_env_temp()`
  ```simple
  rt_env_temp()
  ```
- **Line 299**: `rt_env_cwd()`
  ```simple
  val cwd = rt_env_cwd()
  ```

#### `rust/lib/std/src/tooling/context_pack.spl`

- **Line 55**: `rt_api_surface_extract()`
  ```simple
  val api_json = rt_api_surface_extract(source_file)
  ```
- **Line 58**: `rt_symbol_usage_find()`
  ```simple
  val usage_json = rt_symbol_usage_find(source_file, target)
  ```

#### `rust/lib/std/src/tooling/coverage.spl`

- **Line 52**: `rt_coverage_enabled()`
  ```simple
  rt_coverage_enabled()
  ```
- **Line 56**: `rt_coverage_clear()`
  ```simple
  rt_coverage_clear()
  ```
- **Line 60**: `rt_coverage_dump_sdn()`
  ```simple
  rt_coverage_dump_sdn()
  ```

#### `rust/lib/std/src/tooling/dashboard/collectors/todo_collector.spl`

- **Line 41**: `rt_to_dashboard_todo()`
  ```simple
  val dashboard_todo = convert_to_dashboard_todo(parser_todo, i)
  ```
- **Line 51**: `rt_to_dashboard_todo()`
  ```simple
  fn convert_to_dashboard_todo(parser_todo: ParserTodoItem, id: i32) -> TodoItem:
  ```

#### `rust/lib/std/src/tooling/dashboard/collectors/vcs_collector.spl`

- **Line 82**: `rt_execute_command()`
  ```simple
  fn _rt_execute_command(cmd_ptr: &u8, cmd_len: u64) -> text:
  ```
- **Line 85**: `rt_execute_command()`
  ```simple
  return _rt_execute_command(cmd.ptr(), cmd.len())
  ```

#### `rust/lib/std/src/tooling/dashboard/config.spl`

- **Line 77**: `rt_config()`
  ```simple
  | "alerts" -> parse_alert_config(key=key, value=value, alerts=config.alerts)
  ```
- **Line 85**: `rt_config()`
  ```simple
  fn parse_alert_config(key: text, value: text, alerts: AlertConfig):
  ```

#### `rust/lib/std/src/tooling/deployment/automation.spl`

- **Line 11**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 148**: `rt_file_size()`
  ```simple
  size_bytes: _rt_file_size(path.ptr(), path.len())
  ```
- **Line 14**: `rt_file_size()`
  ```simple
  fn _rt_file_size(path_ptr: &u8, path_len: u64) -> i64
  ```
- **Line 476**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 538**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 682**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 711**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 853**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 858**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 863**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```

#### `rust/lib/std/src/tooling/deployment/containers.spl`

- **Line 12**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 598**: `rt_file_exists()`
  ```simple
  fn _rt_file_exists(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 604**: `rt_file_exists()`
  ```simple
  if _rt_file_exists(rust_marker.ptr(), rust_marker.len())
  ```
- **Line 609**: `rt_file_exists()`
  ```simple
  if _rt_file_exists(node_marker.ptr(), node_marker.len())
  ```
- **Line 615**: `rt_file_exists()`
  ```simple
  if _rt_file_exists(py_marker1.ptr(), py_marker1.len()) or _rt_file_exists(py_marker2.ptr(), py_marker2.len())
  ```
- **Line 620**: `rt_file_exists()`
  ```simple
  if _rt_file_exists(go_marker.ptr(), go_marker.len())
  ```
- **Line 625**: `rt_file_exists()`
  ```simple
  if _rt_file_exists(simple_marker.ptr(), simple_marker.len())
  ```
- **Line 704**: `rt_file_write_text()`
  ```simple
  _rt_file_write_text(dockerfile_path.ptr(), dockerfile_path.len(), dockerfile.ptr(), dockerfile.len())
  ```
- **Line 713**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 739**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 774**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 784**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 806**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 9**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```

#### `rust/lib/std/src/tooling/deployment/optimization.spl`

- **Line 11**: `rt_file_size()`
  ```simple
  fn _rt_file_size(path_ptr: &u8, path_len: u64) -> i64
  ```
- **Line 592**: `rt_file_size()`
  ```simple
  _rt_file_size(path.ptr(), path.len())
  ```
- **Line 607**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 622**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 638**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 8**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```

#### `rust/lib/std/src/tooling/deployment/packaging.spl`

- **Line 1016**: `rt_file_write_text()`
  ```simple
  _rt_file_write_text(spec_path.ptr(), spec_path.len(), spec_content.ptr(), spec_content.len())
  ```
- **Line 1021**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 1038**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 1041**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 1055**: `rt_file_write_text()`
  ```simple
  _rt_file_write_text(nuspec_path.ptr(), nuspec_path.len(), nuspec_content.ptr(), nuspec_content.len())
  ```
- **Line 1060**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 1077**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 1080**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 1092**: `rt_file_write_text()`
  ```simple
  _rt_file_write_text(pkg_json_path.ptr(), pkg_json_path.len(), pkg_json_content.ptr(), pkg_json_content.len())
  ```
- **Line 1097**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 1114**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 1117**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 1131**: `rt_file_write_text()`
  ```simple
  _rt_file_write_text(setup_path.ptr(), setup_path.len(), setup_content.ptr(), setup_content.len())
  ```
- **Line 1136**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 657**: `rt_glob()`
  ```simple
  fn _rt_glob(pattern_ptr: &u8, pattern_len: u64) -> text
  ```
- **Line 661**: `rt_glob()`
  ```simple
  val smf_files = _rt_glob(smf_pattern.ptr(), smf_pattern.len())
  ```
- **Line 668**: `rt_glob()`
  ```simple
  val exe_files = _rt_glob(exe_pattern.ptr(), exe_pattern.len())
  ```
- **Line 676**: `rt_glob()`
  ```simple
  fn _rt_glob(pattern_ptr: &u8, pattern_len: u64) -> text
  ```
- **Line 679**: `rt_file_stat()`
  ```simple
  fn _rt_file_stat(path_ptr: &u8, path_len: u64, out_exists: &mut bool, out_is_file: &mut bool, out_is_dir: &mut bool, out_is_readable: &mut bool, out_is_writable: &mut bool, out_size: &mut i64)
  ```
- **Line 683**: `rt_glob()`
  ```simple
  val bin_files = _rt_glob(bin_pattern.ptr(), bin_pattern.len())
  ```
- **Line 696**: `rt_file_stat()`
  ```simple
  _rt_file_stat(file.ptr(), file.len(), &mut exists, &mut is_file, &mut is_dir, &mut is_readable, &mut is_writable, &mut size)
  ```
- **Line 707**: `rt_glob()`
  ```simple
  fn _rt_glob(pattern_ptr: &u8, pattern_len: u64) -> text
  ```
- **Line 711**: `rt_glob()`
  ```simple
  val py_files = _rt_glob(py_pattern.ptr(), py_pattern.len())
  ```
- **Line 720**: `rt_glob()`
  ```simple
  val wheel_files = _rt_glob(wheel_pattern.ptr(), wheel_pattern.len())
  ```
- **Line 728**: `rt_glob()`
  ```simple
  fn _rt_glob(pattern_ptr: &u8, pattern_len: u64) -> text
  ```
- **Line 732**: `rt_glob()`
  ```simple
  val dist_files = _rt_glob(dist_pattern.ptr(), dist_pattern.len())
  ```
- **Line 740**: `rt_glob()`
  ```simple
  val css_files = _rt_glob(css_pattern.ptr(), css_pattern.len())
  ```
- **Line 748**: `rt_glob()`
  ```simple
  val map_files = _rt_glob(map_pattern.ptr(), map_pattern.len())
  ```
- **Line 820**: `rt_file_size()`
  ```simple
  fn _rt_file_size(path_ptr: &u8, path_len: u64) -> i64
  ```
- **Line 824**: `rt_file_size()`
  ```simple
  val size = _rt_file_size(src_path.ptr(), src_path.len())
  ```
- **Line 875**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 885**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 902**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 912**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 929**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 932**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 935**: `rt_mkdir()`
  ```simple
  fn _rt_mkdir(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 940**: `rt_mkdir()`
  ```simple
  _rt_mkdir(pkg_dir.ptr(), pkg_dir.len())
  ```
- **Line 943**: `rt_mkdir()`
  ```simple
  _rt_mkdir(debian_dir.ptr(), debian_dir.len())
  ```
- **Line 953**: `rt_file_write_text()`
  ```simple
  _rt_file_write_text(control_path.ptr(), control_path.len(), control_content.ptr(), control_content.len())
  ```
- **Line 960**: `rt_process_run()`
  ```simple
  _rt_process_run(cp_cmd.ptr(), cp_cmd.len(), cp_args.ptr(), cp_args.len())
  ```
- **Line 965**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 982**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 985**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 988**: `rt_mkdir()`
  ```simple
  fn _rt_mkdir(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 992**: `rt_mkdir()`
  ```simple
  _rt_mkdir(rpmbuild_dir.ptr(), rpmbuild_dir.len())
  ```
- **Line 995**: `rt_mkdir()`
  ```simple
  _rt_mkdir(specs_dir.ptr(), specs_dir.len())
  ```
- **Line 998**: `rt_mkdir()`
  ```simple
  _rt_mkdir(sources_dir.ptr(), sources_dir.len())
  ```

#### `rust/lib/std/src/tooling/deployment/pipeline.spl`

- **Line 552**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 555**: `rt_time_now_unix_micros()`
  ```simple
  val start_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 582**: `rt_time_now_unix_micros()`
  ```simple
  val end_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 600**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 602**: `rt_time_now_unix_micros()`
  ```simple
  val start_time = _rt_time_now_unix_micros()
  ```
- **Line 607**: `rt_time_now_unix_micros()`
  ```simple
  val elapsed_micros = _rt_time_now_unix_micros() - start_time
  ```

#### `rust/lib/std/src/tooling/extract_tests.spl`

- **Line 220**: `rt_compiles()`
  ```simple
  output = output + "    assert_compiles()n"
  ```
- **Line 253**: `rt_compiles()`
  ```simple
  output = output + "    assert_compiles()nn"
  ```

#### `rust/lib/std/src/tooling/generics_migrate.spl`

- **Line 335**: `rt_path_exists()`
  ```simple
  fn _rt_path_exists(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 336**: `rt_path_exists()`
  ```simple
  return _rt_path_exists(path.ptr(), path.len())
  ```
- **Line 340**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 341**: `rt_file_read_text()`
  ```simple
  return _rt_file_read_text(path.ptr(), path.len())
  ```
- **Line 345**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> i32
  ```
- **Line 347**: `rt_file_write_text()`
  ```simple
  val result = _rt_file_write_text(path.ptr(), path.len(), content.ptr(), content.len())
  ```
- **Line 355**: `rt_walk_directory()`
  ```simple
  fn _rt_walk_directory(
  ```
- **Line 363**: `rt_walk_directory()`
  ```simple
  return _rt_walk_directory(path.ptr(), path.len(), &include_patterns, &exclude_patterns)
  ```

#### `rust/lib/std/src/tooling/sandbox.spl`

- **Line 293**: `rt_sandbox_reset()`
  ```simple
  rt_sandbox_reset()
  ```
- **Line 297**: `rt_sandbox_set_cpu_time()`
  ```simple
  Some(secs): rt_sandbox_set_cpu_time(secs)
  ```
- **Line 301**: `rt_sandbox_set_memory()`
  ```simple
  Some(bytes): rt_sandbox_set_memory(bytes)
  ```
- **Line 305**: `rt_sandbox_set_fd_limit()`
  ```simple
  Some(count): rt_sandbox_set_fd_limit(count)
  ```
- **Line 309**: `rt_sandbox_set_thread_limit()`
  ```simple
  Some(count): rt_sandbox_set_thread_limit(count)
  ```
- **Line 314**: `rt_sandbox_disable_network()`
  ```simple
  rt_sandbox_disable_network()
  ```
- **Line 316**: `rt_sandbox_set_network_allowlist()`
  ```simple
  rt_sandbox_set_network_allowlist()
  ```
- **Line 318**: `rt_sandbox_add_allowed_domain()`
  ```simple
  rt_sandbox_add_allowed_domain(domain)
  ```
- **Line 320**: `rt_sandbox_set_network_blocklist()`
  ```simple
  rt_sandbox_set_network_blocklist()
  ```
- **Line 322**: `rt_sandbox_add_blocked_domain()`
  ```simple
  rt_sandbox_add_blocked_domain(domain)
  ```
- **Line 326**: `rt_sandbox_set_fs_readonly()`
  ```simple
  rt_sandbox_set_fs_readonly()
  ```
- **Line 328**: `rt_sandbox_add_read_path()`
  ```simple
  rt_sandbox_add_read_path(path)
  ```
- **Line 330**: `rt_sandbox_set_fs_restricted()`
  ```simple
  rt_sandbox_set_fs_restricted()
  ```
- **Line 332**: `rt_sandbox_add_read_path()`
  ```simple
  rt_sandbox_add_read_path(path)
  ```
- **Line 334**: `rt_sandbox_add_write_path()`
  ```simple
  rt_sandbox_add_write_path(path)
  ```
- **Line 337**: `rt_sandbox_apply()`
  ```simple
  if rt_sandbox_apply()
  ```

#### `rust/lib/std/src/tooling/spec_gen.spl`

- **Line 149**: `rt_test_name_to_symbols()`
  ```simple
  fn convert_test_name_to_symbols(test_name: text) -> List<text>:
  ```

#### `rust/lib/std/src/tooling/startup.spl`

- **Line 28**: `rt_prefetch()`
  ```simple
  fn start_prefetch(early_config: EarlyConfig, metrics: StartupMetrics) -> (Option<PrefetchHandle>, StartupMetrics):
  ```

#### `rust/lib/std/src/tooling/string_utils.spl`

- **Line 25**: `rt_all()`
  ```simple
  fn trim_start_all(s: text, prefixes: List<text>) -> text:
  ```

#### `rust/lib/std/src/tooling/testing/aggregation.spl`

- **Line 253**: `rt_junit_xml()`
  ```simple
  pub fn export_junit_xml(self, output_file: text):
  ```
- **Line 262**: `rt_junit_xml()`
  ```simple
  aggregator.export_junit_xml("test-results.xml")
  ```
- **Line 265**: `rt_file_write()`
  ```simple
  fn _rt_file_write(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 270**: `rt_file_write()`
  ```simple
  val success = _rt_file_write(
  ```

#### `rust/lib/std/src/tooling/testing/discovery.spl`

- **Line 314**: `rt_file_read()`
  ```simple
  fn _rt_file_read(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 322**: `rt_file_read()`
  ```simple
  val content = _rt_file_read(file.ptr(), file.len())
  ```
- **Line 353**: `rt_file_read()`
  ```simple
  fn _rt_file_read(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 361**: `rt_file_read()`
  ```simple
  val content = _rt_file_read(file.ptr(), file.len())
  ```

#### `rust/lib/std/src/tooling/testing/filter.spl`

- **Line 441**: `rt_file_read()`
  ```simple
  fn _rt_file_read(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 454**: `rt_file_read()`
  ```simple
  val content = _rt_file_read(file.ptr(), file.len())
  ```
- **Line 587**: `rt_file_exists()`
  ```simple
  fn _rt_file_exists(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 594**: `rt_file_exists()`
  ```simple
  if _rt_file_exists(path.ptr(), path.len())
  ```
- **Line 600**: `rt_file_exists()`
  ```simple
  if _rt_file_exists(mod_path.ptr(), mod_path.len())
  ```

#### `rust/lib/std/src/tooling/testing/parallel.spl`

- **Line 312**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 314**: `rt_time_now_unix_micros()`
  ```simple
  val start_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 328**: `rt_time_now_unix_micros()`
  ```simple
  val end_time = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 403**: `rt_thread_spawn_isolated()`
  ```simple
  val handle = rt_thread_spawn_isolated(work_fn, ())
  ```
- **Line 446**: `rt_file_delete()`
  ```simple
  fn _rt_file_delete(path_ptr: &u8, path_len: u64)
  ```
- **Line 447**: `rt_file_delete()`
  ```simple
  _rt_file_delete(temp_path.ptr(), temp_path.len())
  ```
- **Line 464**: `rt_actor_spawn()`
  ```simple
  fn _rt_actor_spawn(fn_ptr: u64, initial_state: Any) -> i64
  ```
- **Line 467**: `rt_actor_send()`
  ```simple
  fn _rt_actor_send(actor: i64, message: Any)
  ```
- **Line 470**: `rt_actor_recv()`
  ```simple
  fn _rt_actor_recv(timeout_ms: i64) -> Any
  ```
- **Line 477**: `rt_actor_recv()`
  ```simple
  val msg = _rt_actor_recv(-1)  # Block until message
  ```
- **Line 482**: `rt_actor_send()`
  ```simple
  _rt_actor_send(state as i64, result)
  ```
- **Line 490**: `rt_actor_spawn()`
  ```simple
  val coordinator_actor = _rt_actor_spawn(0, ())  # Self as coordinator
  ```
- **Line 493**: `rt_actor_spawn()`
  ```simple
  val worker = _rt_actor_spawn(worker_actor as u64, coordinator_actor)
  ```
- **Line 499**: `rt_actor_send()`
  ```simple
  _rt_actor_send(workers[worker_idx], item)
  ```
- **Line 504**: `rt_actor_recv()`
  ```simple
  val result = _rt_actor_recv(30000) as TestRunResult  # 30s timeout
  ```
- **Line 509**: `rt_actor_send()`
  ```simple
  _rt_actor_send(worker, StopMessage)
  ```
- **Line 518**: `rt_file_write()`
  ```simple
  fn _rt_file_write(path_ptr: &u8, path_len: u64, data_ptr: &u8, data_len: u64) -> bool
  ```
- **Line 521**: `rt_file_write()`
  ```simple
  _rt_file_write(path.ptr(), path.len(), json.ptr(), json.len())
  ```

#### `rust/lib/std/src/tooling/testing/runner.spl`

- **Line 444**: `rt_time_now_seconds()`
  ```simple
  (rt_time_now_seconds() * 1000.0) as i64
  ```
- **Line 480**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 488**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 521**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 529**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 564**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 572**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 617**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```
- **Line 625**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```

#### `rust/lib/std/src/tooling/testing/validation.spl`

- **Line 103**: `rt_test_db_cleanup_stale_runs()`
  ```simple
  val result = rt_test_db_cleanup_stale_runs(db_path)
  ```
- **Line 32**: `rt_test_db_enable_validation()`
  ```simple
  rt_test_db_enable_validation(enabled)
  ```
- **Line 58**: `rt_test_db_validate()`
  ```simple
  val result = rt_test_db_validate(db_path)
  ```
- **Line 80**: `rt_test_run_is_stale()`
  ```simple
  rt_test_run_is_stale(run_id, hours_threshold)
  ```

#### `rust/lib/std/src/tooling/time_utils.spl`

- **Line 433**: `rt_time_now_unix_micros()`
  ```simple
  val micros = rt_time_now_unix_micros()
  ```
- **Line 434**: `rt_timestamp_get_year()`
  ```simple
  val year = rt_timestamp_get_year(micros)
  ```
- **Line 435**: `rt_timestamp_get_month()`
  ```simple
  val month = rt_timestamp_get_month(micros)
  ```
- **Line 436**: `rt_timestamp_get_day()`
  ```simple
  val day = rt_timestamp_get_day(micros)
  ```
- **Line 437**: `rt_timestamp_get_hour()`
  ```simple
  val hour = rt_timestamp_get_hour(micros)
  ```
- **Line 438**: `rt_timestamp_get_minute()`
  ```simple
  val minute = rt_timestamp_get_minute(micros)
  ```
- **Line 439**: `rt_timestamp_get_second()`
  ```simple
  val second = rt_timestamp_get_second(micros)
  ```
- **Line 451**: `rt_time_now_unix_micros()`
  ```simple
  val micros = rt_time_now_unix_micros()
  ```
- **Line 452**: `rt_timestamp_get_year()`
  ```simple
  val year = rt_timestamp_get_year(micros)
  ```
- **Line 453**: `rt_timestamp_get_month()`
  ```simple
  val month = rt_timestamp_get_month(micros)
  ```
- **Line 454**: `rt_timestamp_get_day()`
  ```simple
  val day = rt_timestamp_get_day(micros)
  ```

#### `rust/lib/std/src/tooling/todo_parser.spl`

- **Line 412**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> text:
  ```
- **Line 415**: `rt_file_read_text()`
  ```simple
  return _rt_file_read_text(path.ptr(), path.len())
  ```
- **Line 420**: `rt_path_exists()`
  ```simple
  fn _rt_path_exists(path_ptr: &u8, path_len: u64) -> bool:
  ```
- **Line 423**: `rt_path_exists()`
  ```simple
  return _rt_path_exists(path.ptr(), path.len())
  ```
- **Line 428**: `rt_walk_directory()`
  ```simple
  fn _rt_walk_directory(
  ```
- **Line 435**: `rt_walk_directory()`
  ```simple
  return _rt_walk_directory(root.ptr(), root.len(), &include_patterns, &exclude_patterns)
  ```

#### `rust/lib/std/src/tooling/watch/reload.spl`

- **Line 193**: `rt_http_get()`
  ```simple
  fn _rt_http_get(url_ptr: &u8, url_len: u64) -> text
  ```
- **Line 197**: `rt_http_get()`
  ```simple
  val response = _rt_http_get(url.ptr(), url.len())
  ```
- **Line 202**: `rt_event_polling()`
  ```simple
  self.start_event_polling()
  ```
- **Line 206**: `rt_event_polling()`
  ```simple
  fn start_event_polling(self)
  ```
- **Line 212**: `rt_thread_spawn_isolated()`
  ```simple
  rt_thread_spawn_isolated(poll_fn, ())
  ```
- **Line 217**: `rt_http_get()`
  ```simple
  fn _rt_http_get(url_ptr: &u8, url_len: u64) -> text
  ```
- **Line 220**: `rt_thread_sleep()`
  ```simple
  fn _rt_thread_sleep(ms: i64)
  ```
- **Line 224**: `rt_http_get()`
  ```simple
  val response = _rt_http_get(url.ptr(), url.len())
  ```
- **Line 233**: `rt_thread_sleep()`
  ```simple
  _rt_thread_sleep(100)
  ```
- **Line 292**: `rt_thread_spawn_isolated()`
  ```simple
  rt_thread_spawn_isolated(server_fn, ())
  ```
- **Line 297**: `rt_http_server_start()`
  ```simple
  fn _rt_http_server_start(port: i32) -> i64
  ```
- **Line 300**: `rt_http_server_accept()`
  ```simple
  fn _rt_http_server_accept(handle: i64) -> i64
  ```
- **Line 303**: `rt_http_request_path()`
  ```simple
  fn _rt_http_request_path(conn: i64) -> text
  ```
- **Line 306**: `rt_http_response_send()`
  ```simple
  fn _rt_http_response_send(conn: i64, body_ptr: &u8, body_len: u64)
  ```
- **Line 308**: `rt_http_server_start()`
  ```simple
  val server_handle = _rt_http_server_start(self.port)
  ```
- **Line 314**: `rt_http_server_accept()`
  ```simple
  val conn = _rt_http_server_accept(server_handle)
  ```
- **Line 318**: `rt_http_request_path()`
  ```simple
  val path = _rt_http_request_path(conn)
  ```
- **Line 322**: `rt_http_response_send()`
  ```simple
  _rt_http_response_send(conn, "connected".ptr(), 9)
  ```
- **Line 328**: `rt_http_response_send()`
  ```simple
  _rt_http_response_send(conn, events.ptr(), events.len())
  ```
- **Line 330**: `rt_http_response_send()`
  ```simple
  _rt_http_response_send(conn, "none".ptr(), 4)
  ```
- **Line 332**: `rt_http_response_send()`
  ```simple
  _rt_http_response_send(conn, "not found".ptr(), 9)
  ```
- **Line 384**: `rt_websocket_send()`
  ```simple
  fn _rt_websocket_send(conn_id: i64, msg_ptr: &u8, msg_len: u64) -> bool
  ```
- **Line 391**: `rt_websocket_send()`
  ```simple
  val success = _rt_websocket_send(
  ```
- **Line 498**: `rt_file_exists()`
  ```simple
  fn _rt_file_exists(path_ptr: &u8, path_len: u64) -> bool
  ```
- **Line 500**: `rt_file_exists()`
  ```simple
  if not _rt_file_exists(module_path.ptr(), module_path.len())
  ```
- **Line 536**: `rt_module_unload()`
  ```simple
  fn _rt_module_unload(handle: i64)
  ```
- **Line 540**: `rt_module_unload()`
  ```simple
  _rt_module_unload(handle)
  ```
- **Line 559**: `rt_module_load()`
  ```simple
  fn _rt_module_load(path_ptr: &u8, path_len: u64) -> i64
  ```
- **Line 561**: `rt_module_load()`
  ```simple
  val handle = _rt_module_load(compiled_path.ptr(), compiled_path.len())
  ```
- **Line 619**: `rt_file_read()`
  ```simple
  fn _rt_file_read(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 623**: `rt_file_read()`
  ```simple
  val content = _rt_file_read(module_path.ptr(), module_path.len())
  ```
- **Line 823**: `rt_hmr_server()`
  ```simple
  watch_reload.start_hmr_server(3000)
  ```
- **Line 842**: `rt_hmr_server()`
  ```simple
  pub fn start_hmr_server(self, port: i32):
  ```
- **Line 94**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 98**: `rt_time_now_unix_micros()`
  ```simple
  timestamp: _rt_time_now_unix_micros() / 1000,  # Convert microseconds to milliseconds
  ```

#### `rust/lib/std/src/tooling/watch/watcher.spl`

- **Line 12**: `rt_dir_entries()`
  ```simple
  fn _rt_dir_entries(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 277**: `rt_platform_name()`
  ```simple
  fn _rt_platform_name() -> text
  ```
- **Line 279**: `rt_platform_name()`
  ```simple
  val platform = _rt_platform_name()
  ```
- **Line 282**: `rt_inotify_watch()`
  ```simple
  self.start_inotify_watch()
  ```
- **Line 284**: `rt_fsevents_watch()`
  ```simple
  self.start_fsevents_watch()
  ```
- **Line 287**: `rt_polling_watch()`
  ```simple
  self.start_polling_watch()
  ```
- **Line 289**: `rt_polling_watch()`
  ```simple
  fn start_polling_watch(self)
  ```
- **Line 299**: `rt_inotify_watch()`
  ```simple
  fn start_inotify_watch(self)
  ```
- **Line 306**: `rt_inotify_init()`
  ```simple
  fn _rt_inotify_init() -> i64
  ```
- **Line 309**: `rt_inotify_add_watch()`
  ```simple
  fn _rt_inotify_add_watch(fd: i64, path_ptr: &u8, path_len: u64, mask: i32) -> i32
  ```
- **Line 312**: `rt_inotify_read()`
  ```simple
  fn _rt_inotify_read(fd: i64, timeout_ms: i32) -> text
  ```
- **Line 315**: `rt_inotify_close()`
  ```simple
  fn _rt_inotify_close(fd: i64)
  ```
- **Line 321**: `rt_inotify_init()`
  ```simple
  val inotify_fd = _rt_inotify_init()
  ```
- **Line 326**: `rt_polling_watch()`
  ```simple
  self.start_polling_watch()
  ```
- **Line 339**: `rt_inotify_read()`
  ```simple
  val events_raw = _rt_inotify_read(inotify_fd, 100)  # 100ms timeout
  ```
- **Line 349**: `rt_inotify_close()`
  ```simple
  _rt_inotify_close(inotify_fd)
  ```
- **Line 354**: `rt_inotify_add_watch()`
  ```simple
  fn _rt_inotify_add_watch(fd: i64, path_ptr: &u8, path_len: u64, mask: i32) -> i32
  ```
- **Line 360**: `rt_inotify_add_watch()`
  ```simple
  val wd = _rt_inotify_add_watch(inotify_fd, dir.ptr(), dir.len(), mask)
  ```
- **Line 404**: `rt_fsevents_watch()`
  ```simple
  fn start_fsevents_watch(self)
  ```
- **Line 410**: `rt_fsevents_create()`
  ```simple
  fn _rt_fsevents_create(path_ptr: &u8, path_len: u64) -> i64
  ```
- **Line 413**: `rt_fsevents_read()`
  ```simple
  fn _rt_fsevents_read(handle: i64, timeout_ms: i32) -> text
  ```
- **Line 416**: `rt_fsevents_close()`
  ```simple
  fn _rt_fsevents_close(handle: i64)
  ```
- **Line 424**: `rt_fsevents_create()`
  ```simple
  val fsevents_handle = _rt_fsevents_create(paths.ptr(), paths.len())
  ```
- **Line 430**: `rt_polling_watch()`
  ```simple
  self.start_polling_watch()
  ```
- **Line 436**: `rt_fsevents_read()`
  ```simple
  val events_raw = _rt_fsevents_read(fsevents_handle, 100)  # 100ms timeout
  ```
- **Line 446**: `rt_fsevents_close()`
  ```simple
  _rt_fsevents_close(fsevents_handle)
  ```
- **Line 518**: `rt_dir_entries()`
  ```simple
  val entries_raw = _rt_dir_entries(dir.ptr(), dir.len())
  ```
- **Line 532**: `rt_matches()`
  ```simple
  if path.ends_with(pattern.trim_start_matches("*"))
  ```
- **Line 540**: `rt_file_mtime()`
  ```simple
  val current_mtime = _rt_file_mtime(path.ptr(), path.len())
  ```
- **Line 575**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 577**: `rt_time_now_unix_micros()`
  ```simple
  val now = _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 740**: `rt_thread_sleep()`
  ```simple
  fn _rt_thread_sleep(millis: i64)
  ```
- **Line 742**: `rt_thread_sleep()`
  ```simple
  _rt_thread_sleep(ms as i64)
  ```
- **Line 80**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 85**: `rt_time_now_unix_micros()`
  ```simple
  timestamp: _rt_time_now_unix_micros() / 1000  # Convert microseconds to milliseconds
  ```
- **Line 9**: `rt_file_mtime()`
  ```simple
  fn _rt_file_mtime(path_ptr: &u8, path_len: u64) -> i64
  ```

#### `rust/lib/std/src/tooling/web_commands.spl`

- **Line 130**: `rt_value()`
  ```simple
  fn find_port_value(args: List<text>, flag1: text, flag2: text, default_val: u16) -> u16:
  ```
- **Line 76**: `rt_value()`
  ```simple
  val port = find_port_value(args, flag1="-p", flag2="--port", default_val=8000)
  ```

#### `rust/lib/std/src/ui.disabled/common/key_codes.spl`

- **Line 185**: `rt_terminal_key_code()`
  ```simple
  pub fn convert_terminal_key_code(code: term.KeyCode) -> KeyCode:
  ```
- **Line 206**: `rt_key_code()`
  ```simple
  pub fn convert_key_code(code: term.KeyCode) -> KeyCode:
  ```
- **Line 207**: `rt_terminal_key_code()`
  ```simple
  return convert_terminal_key_code(code)
  ```

#### `rust/lib/std/src/ui.disabled/diff.spl`

- **Line 248**: `rt_child()`
  ```simple
  patches.insert_child(parent_id, new_idx, new_child.clone())
  ```
- **Line 271**: `rt_pos()`
  ```simple
  val pos = binary_search_insert_pos(&dp, val)
  ```
- **Line 295**: `rt_pos()`
  ```simple
  fn binary_search_insert_pos(arr: &Array<u64>, val: u64) -> u64:
  ```

#### `rust/lib/std/src/ui.disabled/element.spl`

- **Line 541**: `rt_by()`
  ```simple
  result.sort_by(|a, b| a.tab_index.unwrap_or(0).cmp(&b.tab_index.unwrap_or(0)))
  ```

#### `rust/lib/std/src/ui.disabled/gui/browser.spl`

- **Line 367**: `rt_child_at()`
  ```simple
  await browser_insert_child_at(parent_handle, child_dom, index)
  ```
- **Line 400**: `rt_dom_event()`
  ```simple
  val ui_event = renderer.convert_dom_event(dom_event)
  ```
- **Line 416**: `rt_dom_event()`
  ```simple
  fn convert_dom_event(dom_event: DomEvent) -> Event:
  ```
- **Line 619**: `rt_child_at()`
  ```simple
  extern async fn browser_insert_child_at(parent_handle: DomNodeHandle, child_handle: DomNodeHandle, index: u64) -> Future<()>
  ```

#### `rust/lib/std/src/ui.disabled/gui/vscode.spl`

- **Line 413**: `rt_child_at()`
  ```simple
  await vscode_insert_child_at(parent_handle, child_node, index)
  ```
- **Line 634**: `rt_child_at()`
  ```simple
  extern async fn vscode_insert_child_at(parent: VscodeNodeHandle, child: VscodeNodeHandle, index: u64) -> Future<()>
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan_ffi.spl`

- **Line 235**: `rt_vk_device_create()`
  ```simple
  val handle = rt_vk_device_create()
  ```
- **Line 241**: `rt_vk_device_sync()`
  ```simple
  val result = rt_vk_device_sync(self.handle)
  ```
- **Line 247**: `rt_vk_device_free()`
  ```simple
  val result = rt_vk_device_free(self.handle)
  ```
- **Line 294**: `rt_vk_buffer_alloc()`
  ```simple
  val handle = rt_vk_buffer_alloc(device.handle, size)
  ```
- **Line 300**: `rt_vk_buffer_upload()`
  ```simple
  val result = rt_vk_buffer_upload(self.handle, data.as_ptr(), data.len() as u64)
  ```
- **Line 308**: `rt_vk_buffer_download()`
  ```simple
  val result = rt_vk_buffer_download(self.handle, data.as_mut_ptr(), size)
  ```
- **Line 314**: `rt_vk_buffer_free()`
  ```simple
  val result = rt_vk_buffer_free(self.handle)
  ```
- **Line 399**: `rt_vk_window_create()`
  ```simple
  val handle = rt_vk_window_create(
  ```
- **Line 412**: `rt_vk_window_get_size()`
  ```simple
  rt_vk_window_get_size(self.handle, &mut w, &mut h)
  ```
- **Line 420**: `rt_vk_window_poll_event()`
  ```simple
  val result = rt_vk_window_poll_event(
  ```
- **Line 433**: `rt_vk_window_destroy()`
  ```simple
  val result = rt_vk_window_destroy(self.handle)
  ```
- **Line 564**: `rt_vk_swapchain_create()`
  ```simple
  val handle = rt_vk_swapchain_create(
  ```
- **Line 576**: `rt_vk_swapchain_acquire_next_image()`
  ```simple
  val result = rt_vk_swapchain_acquire_next_image(self.handle, timeout_ns, &mut image_index)
  ```
- **Line 584**: `rt_vk_swapchain_present()`
  ```simple
  val result = rt_vk_swapchain_present(self.handle, image_index)
  ```
- **Line 592**: `rt_vk_swapchain_recreate()`
  ```simple
  val result = rt_vk_swapchain_recreate(self.handle, width, height)
  ```
- **Line 598**: `rt_vk_swapchain_destroy()`
  ```simple
  val result = rt_vk_swapchain_destroy(self.handle)
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan_pipeline.spl`

- **Line 248**: `rt_dynamic()`
  ```simple
  pub fn viewport_dynamic(mut self) -> PipelineBuilder
  ```
- **Line 42**: `rt_dynamic()`
  ```simple
  .viewport_dynamic()
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan_renderer.spl`

- **Line 112**: `rt_dynamic()`
  ```simple
  .viewport_dynamic()
  ```
- **Line 1152**: `rt_key_event()`
  ```simple
  fn convert_key_event(key_code: u32, modifiers: u8) -> KeyEvent:
  ```
- **Line 1198**: `rt_mouse_event()`
  ```simple
  fn convert_mouse_event(x: u16, y: u16, button: u8, kind: u8) -> MouseEvent:
  ```
- **Line 270**: `rt_vk_window_poll_event()`
  ```simple
  val result = rt_vk_window_poll_event(
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan/renderer.spl`

- **Line 284**: `rt_vk_window_get_size()`
  ```simple
  val size_result = rt_vk_window_get_size(
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan_renderer.spl`

- **Line 299**: `rt_key_event()`
  ```simple
  val key_event = convert_key_event(key_code, modifiers)
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan/renderer.spl`

- **Line 306**: `rt_vk_framebuffer_free()`
  ```simple
  rt_vk_framebuffer_free(fb_handle)
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan_renderer.spl`

- **Line 307**: `rt_mouse_event()`
  ```simple
  val mouse_event = convert_mouse_event(x, y, button, kind)
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan/renderer.spl`

- **Line 314**: `rt_vk_framebuffer_create_for_swapchain()`
  ```simple
  val fb_count = rt_vk_framebuffer_create_for_swapchain(
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan_renderer.spl`

- **Line 323**: `rt_vk_window_wait_event()`
  ```simple
  val result = rt_vk_window_wait_event(
  ```
- **Line 354**: `rt_key_event()`
  ```simple
  val key_event = convert_key_event(key_code, modifiers)
  ```
- **Line 362**: `rt_mouse_event()`
  ```simple
  val mouse_event = convert_mouse_event(x, y, button, kind)
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan/resources.spl`

- **Line 117**: `rt_vk_image_free()`
  ```simple
  rt_vk_image_free(handle)
  ```
- **Line 120**: `rt_vk_image_free()`
  ```simple
  rt_vk_image_free(atlas)
  ```
- **Line 164**: `rt_vk_buffer_alloc()`
  ```simple
  val vertex_buf = rt_vk_buffer_alloc(device.handle, 65536)
  ```
- **Line 166**: `rt_vk_buffer_alloc()`
  ```simple
  val index_buf = rt_vk_buffer_alloc(device.handle, 16384)
  ```
- **Line 168**: `rt_vk_buffer_alloc()`
  ```simple
  val uniform_buf = rt_vk_buffer_alloc(device.handle, 256)
  ```
- **Line 188**: `rt_vk_buffer_upload()`
  ```simple
  rt_vk_buffer_upload(vb, vertex_data.as_ptr(), vertex_data.len() as u64)
  ```
- **Line 197**: `rt_vk_buffer_upload()`
  ```simple
  rt_vk_buffer_upload(ib, index_data.as_ptr(), index_data.len() as u64)
  ```
- **Line 224**: `rt_vk_buffer_free()`
  ```simple
  rt_vk_buffer_free(vb)
  ```
- **Line 227**: `rt_vk_buffer_free()`
  ```simple
  rt_vk_buffer_free(ib)
  ```
- **Line 230**: `rt_vk_buffer_free()`
  ```simple
  rt_vk_buffer_free(ub)
  ```
- **Line 309**: `rt_vk_image_upload()`
  ```simple
  val upload_result = rt_vk_image_upload(
  ```
- **Line 316**: `rt_vk_image_free()`
  ```simple
  rt_vk_image_free(atlas_handle)
  ```
- **Line 322**: `rt_vk_sampler_create()`
  ```simple
  val sampler_handle = rt_vk_sampler_create(
  ```
- **Line 341**: `rt_vk_image_free()`
  ```simple
  rt_vk_image_free(atlas)
  ```
- **Line 344**: `rt_vk_sampler_free()`
  ```simple
  rt_vk_sampler_free(samp)
  ```
- **Line 66**: `rt_vk_image_upload()`
  ```simple
  val upload_result = rt_vk_image_upload(
  ```
- **Line 73**: `rt_vk_image_free()`
  ```simple
  rt_vk_image_free(image_handle)
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan.spl`

- **Line 107**: `rt_vk_window_create()`
  ```simple
  val window_handle = rt_vk_window_create(
  ```
- **Line 120**: `rt_vk_window_destroy()`
  ```simple
  rt_vk_window_destroy(window_handle)
  ```
- **Line 128**: `rt_vk_window_destroy()`
  ```simple
  rt_vk_window_destroy(window_handle)
  ```
- **Line 137**: `rt_vk_window_destroy()`
  ```simple
  rt_vk_window_destroy(window_handle)
  ```
- **Line 1492**: `rt_vk_command_buffer_begin()`
  ```simple
  val handle = rt_vk_command_buffer_begin(self.device_handle)
  ```
- **Line 1505**: `rt_vk_command_buffer_end()`
  ```simple
  val result = rt_vk_command_buffer_end(self.command_buffer_handle)
  ```
- **Line 1517**: `rt_vk_command_buffer_submit()`
  ```simple
  val result = rt_vk_command_buffer_submit(self.command_buffer_handle)
  ```
- **Line 1525**: `rt_vk_command_buffer_free()`
  ```simple
  val result = rt_vk_command_buffer_free(self.command_buffer_handle)
  ```
- **Line 1652**: `rt_vk_buffer_alloc()`
  ```simple
  val vb = rt_vk_buffer_alloc(device.handle, 65536)
  ```
- **Line 1656**: `rt_vk_buffer_alloc()`
  ```simple
  val ib = rt_vk_buffer_alloc(device.handle, 16384)
  ```
- **Line 1660**: `rt_vk_buffer_alloc()`
  ```simple
  val ub = rt_vk_buffer_alloc(device.handle, 256)
  ```
- **Line 1683**: `rt_vk_buffer_upload()`
  ```simple
  rt_vk_buffer_upload(vertex_buffer, vertex_data.as_ptr(), vertex_data.len() as u64)
  ```
- **Line 1691**: `rt_vk_buffer_upload()`
  ```simple
  rt_vk_buffer_upload(index_buffer, index_data.as_ptr(), index_data.len() as u64)
  ```
- **Line 1699**: `rt_vk_buffer_upload()`
  ```simple
  rt_vk_buffer_upload(uniform_buffer, uniform_data.as_ptr(), uniform_data.len() as u64)
  ```
- **Line 212**: `rt_vk_window_destroy()`
  ```simple
  rt_vk_window_destroy(self.window_handle)
  ```
- **Line 300**: `rt_vk_cmd_begin_render_pass()`
  ```simple
  rt_vk_cmd_begin_render_pass(
  ```
- **Line 308**: `rt_vk_cmd_end_render_pass()`
  ```simple
  rt_vk_cmd_end_render_pass(cmd_handle)
  ```
- **Line 330**: `rt_vk_window_poll_event()`
  ```simple
  val result = rt_vk_window_poll_event(
  ```
- **Line 345**: `rt_window_event()`
  ```simple
  return Ok(Some(self.convert_window_event(window_event)))
  ```
- **Line 358**: `rt_vk_window_wait_event()`
  ```simple
  val result = rt_vk_window_wait_event(
  ```
- **Line 371**: `rt_window_event()`
  ```simple
  return Ok(self.convert_window_event(window_event))
  ```
- **Line 375**: `rt_window_event()`
  ```simple
  fn convert_window_event(window_event: WindowEvent) -> Event:
  ```
- **Line 428**: `rt_vk_cmd_begin_render_pass()`
  ```simple
  rt_vk_cmd_begin_render_pass(
  ```
- **Line 436**: `rt_vk_cmd_set_viewport()`
  ```simple
  rt_vk_cmd_set_viewport(
  ```
- **Line 444**: `rt_vk_cmd_set_scissor()`
  ```simple
  rt_vk_cmd_set_scissor(
  ```
- **Line 455**: `rt_vk_cmd_bind_pipeline()`
  ```simple
  rt_vk_cmd_bind_pipeline(cmd_handle, draw_call.pipeline_handle as u64)
  ```
- **Line 459**: `rt_vk_cmd_bind_vertex_buffer()`
  ```simple
  rt_vk_cmd_bind_vertex_buffer(cmd_handle, draw_call.vertex_buffer_handle as u64, 0)
  ```
- **Line 463**: `rt_vk_cmd_bind_index_buffer()`
  ```simple
  rt_vk_cmd_bind_index_buffer(cmd_handle, draw_call.index_buffer_handle as u64, 0)
  ```
- **Line 467**: `rt_vk_cmd_draw_indexed()`
  ```simple
  rt_vk_cmd_draw_indexed(
  ```
- **Line 476**: `rt_vk_cmd_draw()`
  ```simple
  rt_vk_cmd_draw(
  ```
- **Line 485**: `rt_vk_cmd_end_render_pass()`
  ```simple
  rt_vk_cmd_end_render_pass(cmd_handle)
  ```
- **Line 523**: `rt_vk_device_create()`
  ```simple
  val device_handle = rt_vk_device_create()
  ```
- **Line 533**: `rt_vk_device_free()`
  ```simple
  val result = rt_vk_device_free(self.handle)
  ```
- **Line 539**: `rt_vk_device_sync()`
  ```simple
  val result = rt_vk_device_sync(self.handle)
  ```
- **Line 641**: `rt_vk_swapchain_create()`
  ```simple
  val swapchain_handle = rt_vk_swapchain_create(device.handle, window_handle, width, height)
  ```
- **Line 645**: `rt_vk_swapchain_get_image_count()`
  ```simple
  val image_count = rt_vk_swapchain_get_image_count(swapchain_handle)
  ```
- **Line 656**: `rt_vk_swapchain_recreate()`
  ```simple
  val result = rt_vk_swapchain_recreate(self.handle, width, height)
  ```
- **Line 665**: `rt_vk_swapchain_acquire_next_image()`
  ```simple
  val result = rt_vk_swapchain_acquire_next_image(self.handle, timeout_ns, &mut image_index)
  ```
- **Line 673**: `rt_vk_swapchain_present()`
  ```simple
  val result = rt_vk_swapchain_present(self.handle, image_index)
  ```
- **Line 681**: `rt_vk_swapchain_destroy()`
  ```simple
  val result = rt_vk_swapchain_destroy(self.handle)
  ```
- **Line 710**: `rt_vk_render_pass_create_simple()`
  ```simple
  val render_pass_handle = rt_vk_render_pass_create_simple(device.handle, VK_FORMAT_B8G8R8A8_SRGB)
  ```
- **Line 719**: `rt_vk_framebuffer_create_for_swapchain()`
  ```simple
  val fb_count = rt_vk_framebuffer_create_for_swapchain(
  ```
- **Line 728**: `rt_vk_render_pass_free()`
  ```simple
  rt_vk_render_pass_free(render_pass_handle)
  ```
- **Line 744**: `rt_vk_framebuffer_free()`
  ```simple
  rt_vk_framebuffer_free(fb_handle)
  ```
- **Line 747**: `rt_vk_render_pass_free()`
  ```simple
  val result = rt_vk_render_pass_free(self.handle)
  ```

#### `rust/lib/std/src/ui.disabled/gui/vulkan_window.spl`

- **Line 103**: `rt_vk_window_poll_event()`
  ```simple
  val result = rt_vk_window_poll_event(
  ```
- **Line 133**: `rt_vk_window_wait_event()`
  ```simple
  val result = rt_vk_window_wait_event(
  ```
- **Line 188**: `rt_vk_window_destroy()`
  ```simple
  val _ = rt_vk_window_destroy(self.handle)
  ```
- **Line 31**: `rt_vk_window_create()`
  ```simple
  val handle = rt_vk_window_create(0, width, height, title.as_ptr(), title.len() as u64)
  ```
- **Line 51**: `rt_vk_window_get_size()`
  ```simple
  val result = rt_vk_window_get_size(self.handle, &mut width, &mut height)
  ```
- **Line 79**: `rt_vk_window_set_fullscreen()`
  ```simple
  val result = rt_vk_window_set_fullscreen(self.handle, mode_code)
  ```

#### `rust/lib/std/src/ui.disabled/patchset.spl`

- **Line 453**: `rt_child()`
  ```simple
  pub fn insert_child(self, parent_id: NodeId, index: u64, element: Element):
  ```

#### `rust/lib/std/src/ui.disabled/tui/backend/ratatui.spl`

- **Line 129**: `rt_char()`
  ```simple
  extern fn ratatui_textbuffer_insert_char(buffer: u64, code: u32)
  ```
- **Line 226**: `rt_char()`
  ```simple
  pub fn textbuffer_insert_char(buffer: TextBufferHandle, ch: char):
  ```
- **Line 229**: `rt_char()`
  ```simple
  ratatui_textbuffer_insert_char(buffer, code)
  ```

#### `rust/lib/std/src/ui.disabled/tui/renderer.spl`

- **Line 244**: `rt_key_code()`
  ```simple
  code: convert_key_code(key.code),
  ```
- **Line 514**: `rt_key_code()`
  ```simple
  fn convert_key_code(code: term.KeyCode) -> KeyCode:
  ```

#### `rust/lib/std/src/ui.disabled/tui/widgets/line_editor.spl`

- **Line 112**: `rt_char()`
  ```simple
  textbuffer_insert_char(self.buffer, ch)
  ```
- **Line 202**: `rt_char()`
  ```simple
  textbuffer_insert_char(self.buffer, ' ')
  ```
- **Line 203**: `rt_char()`
  ```simple
  textbuffer_insert_char(self.buffer, ' ')
  ```
- **Line 204**: `rt_char()`
  ```simple
  textbuffer_insert_char(self.buffer, ' ')
  ```
- **Line 205**: `rt_char()`
  ```simple
  textbuffer_insert_char(self.buffer, ' ')
  ```

#### `rust/lib/std/src/ui.disabled/tui/widgets.spl`

- **Line 255**: `rt_char()`
  ```simple
  pub fn insert_char(self, ch: char):
  ```

#### `rust/lib/std/src/unreal.disabled/editor.spl`

- **Line 446**: `rt_asset()`
  ```simple
  pub fn import_asset(mut self, file_path: text, destination_path: text) -> bool:
  ```
- **Line 447**: `rt_asset()`
  ```simple
  return unreal_editor_import_asset(self.browser_ptr, file_path, destination_path)
  ```
- **Line 518**: `rt_asset()`
  ```simple
  fn unreal_editor_import_asset(browser: ffi.VoidPtr, file_path: text, destination_path: text) -> bool
  ```

#### `rust/lib/std/src/unreal.disabled/live_coding.spl`

- **Line 229**: `rt_session()`
  ```simple
  unreal_live_coding_start_session(self.session_ptr)
  ```
- **Line 446**: `rt_session()`
  ```simple
  fn unreal_live_coding_start_session(session: ffi.VoidPtr)
  ```

#### `rust/lib/std/src/unreal.disabled/tick.spl`

- **Line 79**: `rt_physics()`
  ```simple
  pub fn is_start_physics(self) -> bool
  ```

#### `rust/lib/std/src/unreal.disabled/ubt.spl`

- **Line 597**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 599**: `rt_file_read_text()`
  ```simple
  val content = _rt_file_read_text(version_file.ptr(), version_file.len())
  ```

#### `rust/lib/std/src/verification/lean/verification_checker.spl`

- **Line 107**: `rt_raw_pointer_error()`
  ```simple
  me report_raw_pointer_error(span: diag.Span, func_name: text):
  ```
- **Line 121**: `rt_unsafe_error()`
  ```simple
  me report_unsafe_error(span: diag.Span, operation: text):
  ```
- **Line 135**: `rt_ffi_error()`
  ```simple
  me report_ffi_error(span: diag.Span, func_name: text):
  ```
- **Line 149**: `rt_missing_termination()`
  ```simple
  me report_missing_termination(span: diag.Span, func_name: text):
  ```
- **Line 163**: `rt_contract_side_effect()`
  ```simple
  me report_contract_side_effect(span: diag.Span, clause_type: text):
  ```
- **Line 177**: `rt_ghost_access()`
  ```simple
  me report_ghost_access(span: diag.Span, var_name: text):
  ```
- **Line 193**: `rt_io_error()`
  ```simple
  self.report_io_error(span, func_name)
  ```
- **Line 198**: `rt_contract_side_effect()`
  ```simple
  self.report_contract_side_effect(span, clause_type)
  ```
- **Line 239**: `rt_missing_termination()`
  ```simple
  checker.report_missing_termination(span, func_name)
  ```
- **Line 243**: `rt_io_error()`
  ```simple
  checker.report_io_error(span, io_fn)
  ```
- **Line 247**: `rt_unsafe_error()`
  ```simple
  checker.report_unsafe_error(span, "detected unsafe operation")
  ```
- **Line 93**: `rt_io_error()`
  ```simple
  me report_io_error(span: diag.Span, func_name: text):
  ```

#### `rust/lib/std/src/verification/models/module_resolution.spl`

- **Line 313**: `rt_exists_spec()`
  ```simple
  fn import_exists_spec() -> text
  ```

#### `rust/lib/std/src/verification/models/visibility_export.spl`

- **Line 288**: `rt_requires_access_spec()`
  ```simple
  fn export_requires_access_spec() -> text
  ```

#### `rust/lib/std/src/verification/proofs/checker.spl`

- **Line 114**: `rt_process_run()`
  ```simple
  val (exit_code, stdout, stderr) = _rt_process_run(cmd.ptr(), cmd.len(), args.ptr(), args.len())
  ```
- **Line 12**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 142**: `rt_file_write_text()`
  ```simple
  _rt_file_write_text(temp_file.ptr(), temp_file.len(), content.ptr(), content.len())
  ```
- **Line 9**: `rt_process_run()`
  ```simple
  fn _rt_process_run(cmd_ptr: &u8, cmd_len: u64, args_ptr: &u8, args_len: u64) -> (i32, text, text)
  ```

#### `rust/lib/std/src/vscode/dap.spl`

- **Line 397**: `rt_session()`
  ```simple
  pub fn start_session(self, config: DebugConfiguration): DebugSession =
  ```
- **Line 410**: `rt_session()`
  ```simple
  val session = adapter.start_session(config)
  ```
- **Line 53**: `rt_session()`
  ```simple
  self.session_id = vscode_debug_start_session(config_json)
  ```
- **Line 8**: `rt_session()`
  ```simple
  extern fn vscode_debug_start_session(config: text): i64
  ```

#### `rust/lib/std/src/vscode/document_provider.spl`

- **Line 10**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 203**: `rt_file_read_text()`
  ```simple
  val source = _rt_file_read_text(real_path.ptr(), real_path.len())
  ```
- **Line 230**: `rt_file_read_text()`
  ```simple
  val source = _rt_file_read_text(real_path.ptr(), real_path.len())
  ```

#### `rust/lib/std/src/vscode/manifest.spl`

- **Line 387**: `rt_file_read_text()`
  ```simple
  fn _rt_file_read_text(path_ptr: &u8, path_len: u64) -> text
  ```
- **Line 389**: `rt_file_read_text()`
  ```simple
  val content = _rt_file_read_text(path.ptr(), path.len())
  ```
- **Line 452**: `rt_file_write_text()`
  ```simple
  fn _rt_file_write_text(path_ptr: &u8, path_len: u64, content_ptr: &u8, content_len: u64) -> bool
  ```
- **Line 455**: `rt_file_write_text()`
  ```simple
  _rt_file_write_text(path.ptr(), path.len(), json.ptr(), json.len())
  ```

#### `rust/lib/std/src/web.disabled/middleware.spl`

- **Line 620**: `rt_gzip_compress()`
  ```simple
  val compressed = rt_gzip_compress(bytes)
  ```
- **Line 635**: `rt_gzip_decompress()`
  ```simple
  val decompressed = rt_gzip_decompress(bytes)
  ```

#### `src/app/dashboard/main.spl`

- **Line 209**: `rt_add()`
  ```simple
  fn run_alert_add(args: List<text>):
  ```
- **Line 230**: `rt_list()`
  ```simple
  fn run_alert_list()
  ```
- **Line 240**: `rt_remove()`
  ```simple
  fn run_alert_remove(args: List<text>):
  ```
- **Line 47**: `rt_add()`
  ```simple
  run_alert_add(sub_args)
  ```
- **Line 50**: `rt_list()`
  ```simple
  run_alert_list(sub_args)
  ```
- **Line 53**: `rt_remove()`
  ```simple
  run_alert_remove(sub_args)
  ```

#### `src/app/debug/interpreter_backend.spl`

- **Line 106**: `rt_debug_locals()`
  ```simple
  val raw_locals = rt_debug_locals()
  ```
- **Line 129**: `rt_debug_current_file()`
  ```simple
  val file = rt_debug_current_file()
  ```
- **Line 130**: `rt_debug_current_line()`
  ```simple
  val line = rt_debug_current_line()
  ```
- **Line 49**: `rt_debug_set_active()`
  ```simple
  rt_debug_set_active(1)
  ```
- **Line 53**: `rt_debug_set_active()`
  ```simple
  rt_debug_set_active(0)
  ```
- **Line 54**: `rt_debug_remove_all_breakpoints()`
  ```simple
  rt_debug_remove_all_breakpoints()
  ```
- **Line 61**: `rt_debug_set_active()`
  ```simple
  rt_debug_set_active(1)
  ```
- **Line 64**: `rt_cli_run_file()`
  ```simple
  rt_cli_run_file(self.program_path, self.args, true, false)
  ```
- **Line 68**: `rt_debug_pause()`
  ```simple
  rt_debug_pause()
  ```
- **Line 72**: `rt_debug_continue()`
  ```simple
  rt_debug_continue()
  ```
- **Line 76**: `rt_debug_set_step_mode()`
  ```simple
  rt_debug_set_step_mode(1)  # StepOver
  ```
- **Line 80**: `rt_debug_set_step_mode()`
  ```simple
  rt_debug_set_step_mode(2)  # StepIn
  ```
- **Line 84**: `rt_debug_set_step_mode()`
  ```simple
  rt_debug_set_step_mode(3)  # StepOut
  ```
- **Line 88**: `rt_debug_add_breakpoint()`
  ```simple
  val bp_id = rt_debug_add_breakpoint(file.ptr(), file.len(), line)
  ```
- **Line 92**: `rt_debug_remove_breakpoint()`
  ```simple
  rt_debug_remove_breakpoint(file.ptr(), file.len(), line)
  ```
- **Line 96**: `rt_debug_stack_trace()`
  ```simple
  val raw_frames = rt_debug_stack_trace()
  ```

#### `src/app/debug/native_agent.spl`

- **Line 108**: `rt_ptrace_single_step()`
  ```simple
  rt_ptrace_single_step(self.pid)
  ```
- **Line 117**: `rt_dwarf_line_to_addr()`
  ```simple
  val addr = rt_dwarf_line_to_addr(self.dwarf_handle, file, line)
  ```
- **Line 121**: `rt_ptrace_read_memory()`
  ```simple
  val orig = rt_ptrace_read_memory(self.pid, addr, 1)
  ```
- **Line 124**: `rt_ptrace_write_memory()`
  ```simple
  rt_ptrace_write_memory(self.pid, addr, 0xCC)
  ```
- **Line 134**: `rt_ptrace_write_memory()`
  ```simple
  rt_ptrace_write_memory(self.pid, addr, orig)
  ```
- **Line 146**: `rt_ptrace_get_registers()`
  ```simple
  val regs = rt_ptrace_get_registers(self.pid)
  ```
- **Line 149**: `rt_dwarf_addr_to_line()`
  ```simple
  val loc_str = rt_dwarf_addr_to_line(self.dwarf_handle, rip)
  ```
- **Line 150**: `rt_dwarf_function_at()`
  ```simple
  val func_name = rt_dwarf_function_at(self.dwarf_handle, rip)
  ```
- **Line 161**: `rt_ptrace_get_registers()`
  ```simple
  val regs = rt_ptrace_get_registers(self.pid)
  ```
- **Line 164**: `rt_dwarf_locals_at()`
  ```simple
  val raw = rt_dwarf_locals_at(self.dwarf_handle, rip, rbp)
  ```
- **Line 177**: `rt_ptrace_get_registers()`
  ```simple
  val regs = rt_ptrace_get_registers(self.pid)
  ```
- **Line 179**: `rt_dwarf_addr_to_line()`
  ```simple
  val loc_str = rt_dwarf_addr_to_line(self.dwarf_handle, rip)
  ```
- **Line 180**: `rt_dwarf_function_at()`
  ```simple
  val func_name = rt_dwarf_function_at(self.dwarf_handle, rip)
  ```
- **Line 71**: `rt_dwarf_load()`
  ```simple
  self.dwarf_handle = rt_dwarf_load(program_path)
  ```
- **Line 80**: `rt_ptrace_detach()`
  ```simple
  rt_ptrace_detach(self.pid)
  ```
- **Line 82**: `rt_dwarf_free()`
  ```simple
  rt_dwarf_free(self.dwarf_handle)
  ```
- **Line 91**: `rt_ptrace_continue()`
  ```simple
  rt_ptrace_continue(self.pid)
  ```
- **Line 99**: `rt_ptrace_continue()`
  ```simple
  rt_ptrace_continue(self.pid)
  ```

#### `src/app/debug/smf_agent.spl`

- **Line 109**: `rt_ptrace_read_memory()`
  ```simple
  val orig = rt_ptrace_read_memory(self.pid, addr, 1)
  ```
- **Line 112**: `rt_ptrace_write_memory()`
  ```simple
  rt_ptrace_write_memory(self.pid, addr, 0xCC)  # INT3
  ```
- **Line 124**: `rt_ptrace_write_memory()`
  ```simple
  rt_ptrace_write_memory(self.pid, addr, orig)
  ```
- **Line 69**: `rt_ptrace_detach()`
  ```simple
  rt_ptrace_detach(self.pid)
  ```
- **Line 77**: `rt_ptrace_continue()`
  ```simple
  rt_ptrace_continue(self.pid)
  ```
- **Line 86**: `rt_ptrace_continue()`
  ```simple
  rt_ptrace_continue(self.pid)
  ```
- **Line 95**: `rt_ptrace_single_step()`
  ```simple
  rt_ptrace_single_step(self.pid)
  ```

#### `src/app/depgraph/parser.spl`

- **Line 107**: `rt_path()`
  ```simple
  return Some(parse_import_path(path, ImportKind.TypeUse, line_number))
  ```
- **Line 111**: `rt_path()`
  ```simple
  return Some(parse_import_path(path, ImportKind.Use, line_number))
  ```
- **Line 115**: `rt_path()`
  ```simple
  return Some(parse_import_path(path, ImportKind.ExportUse, line_number))
  ```
- **Line 119**: `rt_path()`
  ```simple
  return Some(parse_import_path(path, ImportKind.CommonUse, line_number))
  ```
- **Line 124**: `rt_path()`
  ```simple
  fn parse_import_path(path: String, kind: ImportKind, line_number: Int) -> ImportEntry:
  ```
- **Line 203**: `rt_line()`
  ```simple
  val import_opt = parse_import_line(line, line_number)
  ```
- **Line 244**: `rt_paths()`
  ```simple
  pub fn get_all_import_paths(result: ParseResult) -> List<String>:
  ```
- **Line 251**: `rt_paths()`
  ```simple
  pub fn get_all_export_paths(result: ParseResult) -> List<String>:
  ```
- **Line 97**: `rt_line()`
  ```simple
  fn parse_import_line(line: String, line_number: Int) -> Option<ImportEntry>:
  ```

#### `src/app/exp/main.spl`

- **Line 72**: `rt_run()`
  ```simple
  val run = start_run(config, tags)
  ```

#### `src/app/ffi_gen/module_gen.spl`

- **Line 122**: `rt_items()`
  ```simple
  fn add_import_items(path: text, items: [text]) -> ModuleBuilder:
  ```

#### `src/app/ffi_gen/specs/archive_mod.spl`

- **Line 23**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr", "CString"])
  ```
- **Line 25**: `rt_items()`
  ```simple
  .add_import_items("std::fs", ["File"])
  ```
- **Line 26**: `rt_items()`
  ```simple
  .add_import_items("std::io", ["Read", "Write"])
  ```
- **Line 34**: `rt_tar_extract()`
  ```simple
  .add_fn(fn_rt_tar_extract())
  ```
- **Line 35**: `rt_tar_create()`
  ```simple
  .add_fn(fn_rt_tar_create())
  ```
- **Line 36**: `rt_gzip_compress()`
  ```simple
  .add_fn(fn_rt_gzip_compress())
  ```
- **Line 37**: `rt_gzip_decompress()`
  ```simple
  .add_fn(fn_rt_gzip_decompress())
  ```
- **Line 45**: `rt_tar_extract()`
  ```simple
  fn fn_rt_tar_extract() -> FFIFnSpec
  ```
- **Line 63**: `rt_tar_create()`
  ```simple
  fn fn_rt_tar_create() -> FFIFnSpec
  ```
- **Line 75**: `rt_gzip_compress()`
  ```simple
  fn fn_rt_gzip_compress() -> FFIFnSpec
  ```
- **Line 97**: `rt_gzip_decompress()`
  ```simple
  fn fn_rt_gzip_decompress() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/cli_mod.spl`

- **Line 23**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr", "CString"])
  ```
- **Line 29**: `rt_readline()`
  ```simple
  .add_fn(fn_rt_readline())
  ```
- **Line 30**: `rt_readline_with_prompt()`
  ```simple
  .add_fn(fn_rt_readline_with_prompt())
  ```
- **Line 38**: `rt_readline()`
  ```simple
  fn fn_rt_readline() -> FFIFnSpec
  ```
- **Line 55**: `rt_readline_with_prompt()`
  ```simple
  fn fn_rt_readline_with_prompt() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/codegen_mod.spl`

- **Line 23**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr"])
  ```
- **Line 31**: `rt_codegen_init()`
  ```simple
  .add_fn(fn_rt_codegen_init())
  ```
- **Line 32**: `rt_codegen_compile_module()`
  ```simple
  .add_fn(fn_rt_codegen_compile_module())
  ```
- **Line 33**: `rt_codegen_get_function_ptr()`
  ```simple
  .add_fn(fn_rt_codegen_get_function_ptr())
  ```
- **Line 41**: `rt_codegen_init()`
  ```simple
  fn fn_rt_codegen_init() -> FFIFnSpec
  ```
- **Line 52**: `rt_codegen_compile_module()`
  ```simple
  fn fn_rt_codegen_compile_module() -> FFIFnSpec
  ```
- **Line 64**: `rt_codegen_get_function_ptr()`
  ```simple
  fn fn_rt_codegen_get_function_ptr() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/concurrent_mod.spl`

- **Line 27**: `rt_parallel_map()`
  ```simple
  .add_fn(fn_rt_parallel_map())
  ```
- **Line 28**: `rt_thread_count()`
  ```simple
  .add_fn(fn_rt_thread_count())
  ```
- **Line 36**: `rt_parallel_map()`
  ```simple
  fn fn_rt_parallel_map() -> FFIFnSpec
  ```
- **Line 47**: `rt_thread_count()`
  ```simple
  fn fn_rt_thread_count() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/crypto_mod.spl`

- **Line 27**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr", "CString"])
  ```

#### `src/app/ffi_gen/specs/data_mod.spl`

- **Line 23**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr", "CString"])
  ```
- **Line 29**: `rt_regex_match()`
  ```simple
  .add_fn(fn_rt_regex_match())
  ```
- **Line 30**: `rt_regex_find_all()`
  ```simple
  .add_fn(fn_rt_regex_find_all())
  ```
- **Line 31**: `rt_regex_replace()`
  ```simple
  .add_fn(fn_rt_regex_replace())
  ```
- **Line 39**: `rt_regex_match()`
  ```simple
  fn fn_rt_regex_match() -> FFIFnSpec
  ```
- **Line 54**: `rt_regex_find_all()`
  ```simple
  fn fn_rt_regex_find_all() -> FFIFnSpec
  ```
- **Line 75**: `rt_regex_replace()`
  ```simple
  fn fn_rt_regex_replace() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/gc_full.spl`

- **Line 108**: `rt_gc_init()`
  ```simple
  "rt_gc_init();n" +
  ```
- **Line 110**: `rt_gc_malloc()`
  ```simple
  "    let ptr = rt_gc_malloc(1024);n" +
  ```
- **Line 122**: `rt_gc_malloc_atomic()`
  ```simple
  "    let ptr = rt_gc_malloc_atomic(512);n" +
  ```
- **Line 24**: `rt_items()`
  ```simple
  .add_import_items("std::alloc", ["GlobalAlloc", "Layout"])
  ```
- **Line 28**: `rt_gc_init()`
  ```simple
  .add_fn(fn_rt_gc_init())
  ```
- **Line 29**: `rt_gc_malloc()`
  ```simple
  .add_fn(fn_rt_gc_malloc())
  ```
- **Line 30**: `rt_gc_malloc_atomic()`
  ```simple
  .add_fn(fn_rt_gc_malloc_atomic())
  ```
- **Line 31**: `rt_gc_collect()`
  ```simple
  .add_fn(fn_rt_gc_collect())
  ```
- **Line 32**: `rt_gc_get_heap_size()`
  ```simple
  .add_fn(fn_rt_gc_get_heap_size())
  ```
- **Line 33**: `rt_gc_get_free_bytes()`
  ```simple
  .add_fn(fn_rt_gc_get_free_bytes())
  ```
- **Line 46**: `rt_gc_init()`
  ```simple
  fn fn_rt_gc_init() -> FFIFnSpec
  ```
- **Line 54**: `rt_gc_malloc()`
  ```simple
  fn fn_rt_gc_malloc() -> FFIFnSpec
  ```
- **Line 68**: `rt_gc_malloc_atomic()`
  ```simple
  fn fn_rt_gc_malloc_atomic() -> FFIFnSpec
  ```
- **Line 74**: `rt_gc_malloc()`
  ```simple
  "rt_gc_malloc(size)"
  ```
- **Line 79**: `rt_gc_collect()`
  ```simple
  fn fn_rt_gc_collect() -> FFIFnSpec
  ```
- **Line 87**: `rt_gc_get_heap_size()`
  ```simple
  fn fn_rt_gc_get_heap_size() -> FFIFnSpec
  ```
- **Line 94**: `rt_gc_get_free_bytes()`
  ```simple
  fn fn_rt_gc_get_free_bytes() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/io_full.spl`

- **Line 110**: `rt_file_delete()`
  ```simple
  fn fn_rt_file_delete() -> FFIFnSpec
  ```
- **Line 120**: `rt_file_atomic_write()`
  ```simple
  fn fn_rt_file_atomic_write() -> FFIFnSpec
  ```
- **Line 137**: `rt_dir_create()`
  ```simple
  fn fn_rt_dir_create() -> FFIFnSpec
  ```
- **Line 151**: `rt_dir_create_all()`
  ```simple
  fn fn_rt_dir_create_all() -> FFIFnSpec
  ```
- **Line 161**: `rt_dir_list()`
  ```simple
  fn fn_rt_dir_list() -> FFIFnSpec
  ```
- **Line 181**: `rt_dir_walk()`
  ```simple
  fn fn_rt_dir_walk() -> FFIFnSpec
  ```
- **Line 191**: `rt_dir_remove()`
  ```simple
  fn fn_rt_dir_remove() -> FFIFnSpec
  ```
- **Line 209**: `rt_env_cwd()`
  ```simple
  fn fn_rt_env_cwd() -> FFIFnSpec
  ```
- **Line 222**: `rt_env_home()`
  ```simple
  fn fn_rt_env_home() -> FFIFnSpec
  ```
- **Line 235**: `rt_env_get()`
  ```simple
  fn fn_rt_env_get() -> FFIFnSpec
  ```
- **Line 249**: `rt_env_set()`
  ```simple
  fn fn_rt_env_set() -> FFIFnSpec
  ```
- **Line 265**: `rt_glob()`
  ```simple
  fn fn_rt_glob() -> FFIFnSpec
  ```
- **Line 27**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr", "CString"])
  ```
- **Line 33**: `rt_file_exists()`
  ```simple
  .add_fn(fn_rt_file_exists())
  ```
- **Line 34**: `rt_file_read_text()`
  ```simple
  .add_fn(fn_rt_file_read_text())
  ```
- **Line 35**: `rt_file_write_text()`
  ```simple
  .add_fn(fn_rt_file_write_text())
  ```
- **Line 36**: `rt_file_copy()`
  ```simple
  .add_fn(fn_rt_file_copy())
  ```
- **Line 37**: `rt_file_delete()`
  ```simple
  .add_fn(fn_rt_file_delete())
  ```
- **Line 38**: `rt_file_atomic_write()`
  ```simple
  .add_fn(fn_rt_file_atomic_write())
  ```
- **Line 42**: `rt_dir_create()`
  ```simple
  .add_fn(fn_rt_dir_create())
  ```
- **Line 43**: `rt_dir_create_all()`
  ```simple
  .add_fn(fn_rt_dir_create_all())
  ```
- **Line 44**: `rt_dir_list()`
  ```simple
  .add_fn(fn_rt_dir_list())
  ```
- **Line 45**: `rt_dir_walk()`
  ```simple
  .add_fn(fn_rt_dir_walk())
  ```
- **Line 46**: `rt_dir_remove()`
  ```simple
  .add_fn(fn_rt_dir_remove())
  ```
- **Line 50**: `rt_env_cwd()`
  ```simple
  .add_fn(fn_rt_env_cwd())
  ```
- **Line 51**: `rt_env_home()`
  ```simple
  .add_fn(fn_rt_env_home())
  ```
- **Line 52**: `rt_env_get()`
  ```simple
  .add_fn(fn_rt_env_get())
  ```
- **Line 53**: `rt_env_set()`
  ```simple
  .add_fn(fn_rt_env_set())
  ```
- **Line 57**: `rt_glob()`
  ```simple
  .add_fn(fn_rt_glob())
  ```
- **Line 65**: `rt_file_exists()`
  ```simple
  fn fn_rt_file_exists() -> FFIFnSpec
  ```
- **Line 75**: `rt_file_read_text()`
  ```simple
  fn fn_rt_file_read_text() -> FFIFnSpec
  ```
- **Line 88**: `rt_file_write_text()`
  ```simple
  fn fn_rt_file_write_text() -> FFIFnSpec
  ```
- **Line 99**: `rt_file_copy()`
  ```simple
  fn fn_rt_file_copy() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/module_gen_spec.spl`

- **Line 124**: `rt_test()`
  ```simple
  expect(source.contains("pub extern "C" fn rt_test()")).to(be_true())
  ```

#### `src/app/ffi_gen/specs/net_mod.spl`

- **Line 22**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr", "CString"])
  ```
- **Line 27**: `rt_http_get()`
  ```simple
  .add_fn(fn_rt_http_get())
  ```
- **Line 28**: `rt_http_post()`
  ```simple
  .add_fn(fn_rt_http_post())
  ```
- **Line 36**: `rt_http_get()`
  ```simple
  fn fn_rt_http_get() -> FFIFnSpec
  ```
- **Line 54**: `rt_http_post()`
  ```simple
  fn fn_rt_http_post() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/process_mod.spl`

- **Line 118**: `rt_shell_exec()`
  ```simple
  fn fn_rt_shell_exec() -> FFIFnSpec
  ```
- **Line 133**: `rt_getpid()`
  ```simple
  fn fn_rt_getpid() -> FFIFnSpec
  ```
- **Line 23**: `rt_items()`
  ```simple
  .add_import_items("std::process", ["Command", "Stdio"])
  ```
- **Line 24**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr", "CString"])
  ```
- **Line 29**: `rt_process_run()`
  ```simple
  .add_fn(fn_rt_process_run())
  ```
- **Line 30**: `rt_process_run_timeout()`
  ```simple
  .add_fn(fn_rt_process_run_timeout())
  ```
- **Line 31**: `rt_process_output()`
  ```simple
  .add_fn(fn_rt_process_output())
  ```
- **Line 32**: `rt_shell()`
  ```simple
  .add_fn(fn_rt_shell())
  ```
- **Line 33**: `rt_shell_exec()`
  ```simple
  .add_fn(fn_rt_shell_exec())
  ```
- **Line 34**: `rt_getpid()`
  ```simple
  .add_fn(fn_rt_getpid())
  ```
- **Line 42**: `rt_process_run()`
  ```simple
  fn fn_rt_process_run() -> FFIFnSpec
  ```
- **Line 73**: `rt_process_run_timeout()`
  ```simple
  fn fn_rt_process_run_timeout() -> FFIFnSpec
  ```
- **Line 81**: `rt_process_run()`
  ```simple
  "rt_process_run(cmd, args)"
  ```
- **Line 86**: `rt_process_output()`
  ```simple
  fn fn_rt_process_output() -> FFIFnSpec
  ```
- **Line 91**: `rt_process_run()`
  ```simple
  "rt_process_run(cmd, args)"
  ```
- **Line 96**: `rt_shell()`
  ```simple
  fn fn_rt_shell() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/runtime_value_full.spl`

- **Line 167**: `rt_value_nil()`
  ```simple
  fn fn_rt_value_nil() -> FFIFnSpec
  ```
- **Line 172**: `rt_value_bool()`
  ```simple
  fn fn_rt_value_bool() -> FFIFnSpec
  ```
- **Line 179**: `rt_value_int()`
  ```simple
  fn fn_rt_value_int() -> FFIFnSpec
  ```
- **Line 186**: `rt_value_float()`
  ```simple
  fn fn_rt_value_float() -> FFIFnSpec
  ```
- **Line 193**: `rt_value_string()`
  ```simple
  fn fn_rt_value_string() -> FFIFnSpec
  ```
- **Line 201**: `rt_value_nil()`
  ```simple
  "    return rt_value_nil();n" +
  ```
- **Line 209**: `rt_value_array_new()`
  ```simple
  fn fn_rt_value_array_new() -> FFIFnSpec
  ```
- **Line 214**: `rt_value_dict_new()`
  ```simple
  fn fn_rt_value_dict_new() -> FFIFnSpec
  ```
- **Line 223**: `rt_value_type()`
  ```simple
  fn fn_rt_value_type() -> FFIFnSpec
  ```
- **Line 233**: `rt_value_is_nil()`
  ```simple
  fn fn_rt_value_is_nil() -> FFIFnSpec
  ```
- **Line 240**: `rt_value_is_bool()`
  ```simple
  fn fn_rt_value_is_bool() -> FFIFnSpec
  ```
- **Line 247**: `rt_value_is_int()`
  ```simple
  fn fn_rt_value_is_int() -> FFIFnSpec
  ```
- **Line 254**: `rt_value_is_float()`
  ```simple
  fn fn_rt_value_is_float() -> FFIFnSpec
  ```
- **Line 261**: `rt_value_is_string()`
  ```simple
  fn fn_rt_value_is_string() -> FFIFnSpec
  ```
- **Line 268**: `rt_value_is_array()`
  ```simple
  fn fn_rt_value_is_array() -> FFIFnSpec
  ```
- **Line 275**: `rt_value_is_dict()`
  ```simple
  fn fn_rt_value_is_dict() -> FFIFnSpec
  ```
- **Line 286**: `rt_value_as_bool()`
  ```simple
  fn fn_rt_value_as_bool() -> FFIFnSpec
  ```
- **Line 301**: `rt_value_as_int()`
  ```simple
  fn fn_rt_value_as_int() -> FFIFnSpec
  ```
- **Line 316**: `rt_value_as_float()`
  ```simple
  fn fn_rt_value_as_float() -> FFIFnSpec
  ```
- **Line 330**: `rt_value_as_string()`
  ```simple
  fn fn_rt_value_as_string() -> FFIFnSpec
  ```
- **Line 362**: `rt_value_add()`
  ```simple
  fn fn_rt_value_add() -> FFIFnSpec
  ```
- **Line 370**: `rt_value_nil()`
  ```simple
  "    return rt_value_nil();n" +
  ```
- **Line 374**: `rt_value_int()`
  ```simple
  "    (RuntimeValue::Int(a), RuntimeValue::Int(b)) => rt_value_int(a + b),n" +
  ```
- **Line 375**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Float(a), RuntimeValue::Float(b)) => rt_value_float(a + b),n" +
  ```
- **Line 376**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Int(a), RuntimeValue::Float(b)) => rt_value_float(*a as f64 + b),n" +
  ```
- **Line 377**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Float(a), RuntimeValue::Int(b)) => rt_value_float(a + *b as f64),n" +
  ```
- **Line 381**: `rt_value_string()`
  ```simple
  "        rt_value_string(c_str.as_ptr(), c_str.as_bytes().len())n" +
  ```
- **Line 383**: `rt_value_nil()`
  ```simple
  "    _ => rt_value_nil(),n" +
  ```
- **Line 387**: `rt_value_sub()`
  ```simple
  fn fn_rt_value_sub() -> FFIFnSpec
  ```
- **Line 395**: `rt_value_nil()`
  ```simple
  "    return rt_value_nil();n" +
  ```
- **Line 399**: `rt_value_int()`
  ```simple
  "    (RuntimeValue::Int(a), RuntimeValue::Int(b)) => rt_value_int(a - b),n" +
  ```
- **Line 400**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Float(a), RuntimeValue::Float(b)) => rt_value_float(a - b),n" +
  ```
- **Line 401**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Int(a), RuntimeValue::Float(b)) => rt_value_float(*a as f64 - b),n" +
  ```
- **Line 402**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Float(a), RuntimeValue::Int(b)) => rt_value_float(a - *b as f64),n" +
  ```
- **Line 403**: `rt_value_nil()`
  ```simple
  "    _ => rt_value_nil(),n" +
  ```
- **Line 407**: `rt_value_mul()`
  ```simple
  fn fn_rt_value_mul() -> FFIFnSpec
  ```
- **Line 40**: `rt_value_nil()`
  ```simple
  .add_fn(fn_rt_value_nil())
  ```
- **Line 415**: `rt_value_nil()`
  ```simple
  "    return rt_value_nil();n" +
  ```
- **Line 419**: `rt_value_int()`
  ```simple
  "    (RuntimeValue::Int(a), RuntimeValue::Int(b)) => rt_value_int(a * b),n" +
  ```
- **Line 41**: `rt_value_bool()`
  ```simple
  .add_fn(fn_rt_value_bool())
  ```
- **Line 420**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Float(a), RuntimeValue::Float(b)) => rt_value_float(a * b),n" +
  ```
- **Line 421**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Int(a), RuntimeValue::Float(b)) => rt_value_float(*a as f64 * b),n" +
  ```
- **Line 422**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Float(a), RuntimeValue::Int(b)) => rt_value_float(a * (*b as f64)),n" +
  ```
- **Line 423**: `rt_value_nil()`
  ```simple
  "    _ => rt_value_nil(),n" +
  ```
- **Line 427**: `rt_value_div()`
  ```simple
  fn fn_rt_value_div() -> FFIFnSpec
  ```
- **Line 42**: `rt_value_int()`
  ```simple
  .add_fn(fn_rt_value_int())
  ```
- **Line 435**: `rt_value_nil()`
  ```simple
  "    return rt_value_nil();n" +
  ```
- **Line 43**: `rt_value_float()`
  ```simple
  .add_fn(fn_rt_value_float())
  ```
- **Line 441**: `rt_value_nil()`
  ```simple
  "            return rt_value_nil(); // Division by zeron" +
  ```
- **Line 443**: `rt_value_int()`
  ```simple
  "        rt_value_int(a / b)n" +
  ```
- **Line 445**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Float(a), RuntimeValue::Float(b)) => rt_value_float(a / b),n" +
  ```
- **Line 446**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Int(a), RuntimeValue::Float(b)) => rt_value_float(*a as f64 / b),n" +
  ```
- **Line 447**: `rt_value_float()`
  ```simple
  "    (RuntimeValue::Float(a), RuntimeValue::Int(b)) => rt_value_float(a / (*b as f64)),n" +
  ```
- **Line 448**: `rt_value_nil()`
  ```simple
  "    _ => rt_value_nil(),n" +
  ```
- **Line 44**: `rt_value_string()`
  ```simple
  .add_fn(fn_rt_value_string())
  ```
- **Line 456**: `rt_value_eq()`
  ```simple
  fn fn_rt_value_eq() -> FFIFnSpec
  ```
- **Line 45**: `rt_value_array_new()`
  ```simple
  .add_fn(fn_rt_value_array_new())
  ```
- **Line 46**: `rt_value_dict_new()`
  ```simple
  .add_fn(fn_rt_value_dict_new())
  ```
- **Line 480**: `rt_value_lt()`
  ```simple
  fn fn_rt_value_lt() -> FFIFnSpec
  ```
- **Line 505**: `rt_value_print()`
  ```simple
  fn fn_rt_value_print() -> FFIFnSpec
  ```
- **Line 50**: `rt_value_type()`
  ```simple
  .add_fn(fn_rt_value_type())
  ```
- **Line 51**: `rt_value_is_nil()`
  ```simple
  .add_fn(fn_rt_value_is_nil())
  ```
- **Line 527**: `rt_value_println()`
  ```simple
  fn fn_rt_value_println() -> FFIFnSpec
  ```
- **Line 52**: `rt_value_is_bool()`
  ```simple
  .add_fn(fn_rt_value_is_bool())
  ```
- **Line 531**: `rt_value_print()`
  ```simple
  "rt_value_print(value);nprintln!();"
  ```
- **Line 538**: `rt_value_free()`
  ```simple
  fn fn_rt_value_free() -> FFIFnSpec
  ```
- **Line 53**: `rt_value_is_int()`
  ```simple
  .add_fn(fn_rt_value_is_int())
  ```
- **Line 547**: `rt_value_clone()`
  ```simple
  fn fn_rt_value_clone() -> FFIFnSpec
  ```
- **Line 54**: `rt_value_is_float()`
  ```simple
  .add_fn(fn_rt_value_is_float())
  ```
- **Line 552**: `rt_value_nil()`
  ```simple
  "    return rt_value_nil();n" +
  ```
- **Line 55**: `rt_value_is_string()`
  ```simple
  .add_fn(fn_rt_value_is_string())
  ```
- **Line 56**: `rt_value_is_array()`
  ```simple
  .add_fn(fn_rt_value_is_array())
  ```
- **Line 577**: `rt_value_nil()`
  ```simple
  "    let val = rt_value_nil();n" +
  ```
- **Line 579**: `rt_value_is_nil()`
  ```simple
  "    assert!(rt_value_is_nil(val));n" +
  ```
- **Line 57**: `rt_value_is_dict()`
  ```simple
  .add_fn(fn_rt_value_is_dict())
  ```
- **Line 580**: `rt_value_type()`
  ```simple
  "    assert_eq!(rt_value_type(val), ValueType::Nil);n" +
  ```
- **Line 581**: `rt_value_free()`
  ```simple
  "    rt_value_free(val);n" +
  ```
- **Line 588**: `rt_value_int()`
  ```simple
  "    let val = rt_value_int(42);n" +
  ```
- **Line 590**: `rt_value_is_int()`
  ```simple
  "    assert!(rt_value_is_int(val));n" +
  ```
- **Line 591**: `rt_value_as_int()`
  ```simple
  "    assert_eq!(rt_value_as_int(val), 42);n" +
  ```
- **Line 592**: `rt_value_free()`
  ```simple
  "    rt_value_free(val);n" +
  ```
- **Line 600**: `rt_value_string()`
  ```simple
  "    let val = rt_value_string(s.as_ptr(), s.as_bytes().len());n" +
  ```
- **Line 602**: `rt_value_is_string()`
  ```simple
  "    assert!(rt_value_is_string(val));n" +
  ```
- **Line 605**: `rt_value_as_string()`
  ```simple
  "    let ptr = rt_value_as_string(val, &mut len);n" +
  ```
- **Line 609**: `rt_value_free()`
  ```simple
  "    rt_value_free(val);n" +
  ```
- **Line 616**: `rt_value_int()`
  ```simple
  "    let a = rt_value_int(10);n" +
  ```
- **Line 617**: `rt_value_int()`
  ```simple
  "    let b = rt_value_int(5);n" +
  ```
- **Line 619**: `rt_value_add()`
  ```simple
  "    let sum = rt_value_add(a, b);n" +
  ```
- **Line 61**: `rt_value_as_bool()`
  ```simple
  .add_fn(fn_rt_value_as_bool())
  ```
- **Line 620**: `rt_value_as_int()`
  ```simple
  "    assert_eq!(rt_value_as_int(sum), 15);n" +
  ```
- **Line 622**: `rt_value_sub()`
  ```simple
  "    let diff = rt_value_sub(a, b);n" +
  ```
- **Line 623**: `rt_value_as_int()`
  ```simple
  "    assert_eq!(rt_value_as_int(diff), 5);n" +
  ```
- **Line 625**: `rt_value_mul()`
  ```simple
  "    let prod = rt_value_mul(a, b);n" +
  ```
- **Line 626**: `rt_value_as_int()`
  ```simple
  "    assert_eq!(rt_value_as_int(prod), 50);n" +
  ```
- **Line 628**: `rt_value_div()`
  ```simple
  "    let quot = rt_value_div(a, b);n" +
  ```
- **Line 629**: `rt_value_as_int()`
  ```simple
  "    assert_eq!(rt_value_as_int(quot), 2);n" +
  ```
- **Line 62**: `rt_value_as_int()`
  ```simple
  .add_fn(fn_rt_value_as_int())
  ```
- **Line 631**: `rt_value_free()`
  ```simple
  "    rt_value_free(a);n" +
  ```
- **Line 632**: `rt_value_free()`
  ```simple
  "    rt_value_free(b);n" +
  ```
- **Line 633**: `rt_value_free()`
  ```simple
  "    rt_value_free(sum);n" +
  ```
- **Line 634**: `rt_value_free()`
  ```simple
  "    rt_value_free(diff);n" +
  ```
- **Line 635**: `rt_value_free()`
  ```simple
  "    rt_value_free(prod);n" +
  ```
- **Line 636**: `rt_value_free()`
  ```simple
  "    rt_value_free(quot);n" +
  ```
- **Line 63**: `rt_value_as_float()`
  ```simple
  .add_fn(fn_rt_value_as_float())
  ```
- **Line 643**: `rt_value_int()`
  ```simple
  "    let a = rt_value_int(10);n" +
  ```
- **Line 644**: `rt_value_int()`
  ```simple
  "    let b = rt_value_int(5);n" +
  ```
- **Line 645**: `rt_value_int()`
  ```simple
  "    let c = rt_value_int(10);n" +
  ```
- **Line 647**: `rt_value_eq()`
  ```simple
  "    assert!(!rt_value_eq(a, b));n" +
  ```
- **Line 648**: `rt_value_eq()`
  ```simple
  "    assert!(rt_value_eq(a, c));n" +
  ```
- **Line 649**: `rt_value_lt()`
  ```simple
  "    assert!(rt_value_lt(b, a));n" +
  ```
- **Line 64**: `rt_value_as_string()`
  ```simple
  .add_fn(fn_rt_value_as_string())
  ```
- **Line 650**: `rt_value_lt()`
  ```simple
  "    assert!(!rt_value_lt(a, b));n" +
  ```
- **Line 652**: `rt_value_free()`
  ```simple
  "    rt_value_free(a);n" +
  ```
- **Line 653**: `rt_value_free()`
  ```simple
  "    rt_value_free(b);n" +
  ```
- **Line 654**: `rt_value_free()`
  ```simple
  "    rt_value_free(c);n" +
  ```
- **Line 68**: `rt_value_add()`
  ```simple
  .add_fn(fn_rt_value_add())
  ```
- **Line 69**: `rt_value_sub()`
  ```simple
  .add_fn(fn_rt_value_sub())
  ```
- **Line 70**: `rt_value_mul()`
  ```simple
  .add_fn(fn_rt_value_mul())
  ```
- **Line 71**: `rt_value_div()`
  ```simple
  .add_fn(fn_rt_value_div())
  ```
- **Line 75**: `rt_value_eq()`
  ```simple
  .add_fn(fn_rt_value_eq())
  ```
- **Line 76**: `rt_value_lt()`
  ```simple
  .add_fn(fn_rt_value_lt())
  ```
- **Line 80**: `rt_value_print()`
  ```simple
  .add_fn(fn_rt_value_print())
  ```
- **Line 81**: `rt_value_println()`
  ```simple
  .add_fn(fn_rt_value_println())
  ```
- **Line 85**: `rt_value_free()`
  ```simple
  .add_fn(fn_rt_value_free())
  ```
- **Line 86**: `rt_value_clone()`
  ```simple
  .add_fn(fn_rt_value_clone())
  ```

#### `src/app/ffi_gen/specs/serde_mod.spl`

- **Line 23**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CStr", "CString"])
  ```
- **Line 29**: `rt_json_parse()`
  ```simple
  .add_fn(fn_rt_json_parse())
  ```
- **Line 30**: `rt_json_stringify()`
  ```simple
  .add_fn(fn_rt_json_stringify())
  ```
- **Line 31**: `rt_json_get()`
  ```simple
  .add_fn(fn_rt_json_get())
  ```
- **Line 32**: `rt_toml_parse()`
  ```simple
  .add_fn(fn_rt_toml_parse())
  ```
- **Line 40**: `rt_json_parse()`
  ```simple
  fn fn_rt_json_parse() -> FFIFnSpec
  ```
- **Line 50**: `rt_json_stringify()`
  ```simple
  fn fn_rt_json_stringify() -> FFIFnSpec
  ```
- **Line 60**: `rt_json_get()`
  ```simple
  fn fn_rt_json_get() -> FFIFnSpec
  ```
- **Line 82**: `rt_toml_parse()`
  ```simple
  fn fn_rt_toml_parse() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/system_mod.spl`

- **Line 23**: `rt_items()`
  ```simple
  .add_import_items("std::ffi", ["CString"])
  ```
- **Line 29**: `rt_hostname()`
  ```simple
  .add_fn(fn_rt_hostname())
  ```
- **Line 30**: `rt_system_cpu_count()`
  ```simple
  .add_fn(fn_rt_system_cpu_count())
  ```
- **Line 38**: `rt_hostname()`
  ```simple
  fn fn_rt_hostname() -> FFIFnSpec
  ```
- **Line 53**: `rt_system_cpu_count()`
  ```simple
  fn fn_rt_system_cpu_count() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/specs/time_mod.spl`

- **Line 100**: `rt_timestamp_get_hour()`
  ```simple
  fn fn_rt_timestamp_get_hour() -> FFIFnSpec
  ```
- **Line 111**: `rt_timestamp_get_minute()`
  ```simple
  fn fn_rt_timestamp_get_minute() -> FFIFnSpec
  ```
- **Line 122**: `rt_timestamp_get_second()`
  ```simple
  fn fn_rt_timestamp_get_second() -> FFIFnSpec
  ```
- **Line 23**: `rt_items()`
  ```simple
  .add_import_items("std::time", ["SystemTime", "UNIX_EPOCH"])
  ```
- **Line 28**: `rt_time_now_unix_micros()`
  ```simple
  .add_fn(fn_rt_time_now_unix_micros())
  ```
- **Line 29**: `rt_current_time_ms()`
  ```simple
  .add_fn(fn_rt_current_time_ms())
  ```
- **Line 30**: `rt_timestamp_get_year()`
  ```simple
  .add_fn(fn_rt_timestamp_get_year())
  ```
- **Line 31**: `rt_timestamp_get_month()`
  ```simple
  .add_fn(fn_rt_timestamp_get_month())
  ```
- **Line 32**: `rt_timestamp_get_day()`
  ```simple
  .add_fn(fn_rt_timestamp_get_day())
  ```
- **Line 33**: `rt_timestamp_get_hour()`
  ```simple
  .add_fn(fn_rt_timestamp_get_hour())
  ```
- **Line 34**: `rt_timestamp_get_minute()`
  ```simple
  .add_fn(fn_rt_timestamp_get_minute())
  ```
- **Line 35**: `rt_timestamp_get_second()`
  ```simple
  .add_fn(fn_rt_timestamp_get_second())
  ```
- **Line 43**: `rt_time_now_unix_micros()`
  ```simple
  fn fn_rt_time_now_unix_micros() -> FFIFnSpec
  ```
- **Line 55**: `rt_current_time_ms()`
  ```simple
  fn fn_rt_current_time_ms() -> FFIFnSpec
  ```
- **Line 67**: `rt_timestamp_get_year()`
  ```simple
  fn fn_rt_timestamp_get_year() -> FFIFnSpec
  ```
- **Line 78**: `rt_timestamp_get_month()`
  ```simple
  fn fn_rt_timestamp_get_month() -> FFIFnSpec
  ```
- **Line 89**: `rt_timestamp_get_day()`
  ```simple
  fn fn_rt_timestamp_get_day() -> FFIFnSpec
  ```

#### `src/app/ffi_gen/templates/build.spl`

- **Line 100**: `rt_file_copy()`
  ```simple
  rt_file_copy(src_path, dst_path)
  ```
- **Line 22**: `rt_env_cwd()`
  ```simple
  val script_dir = rt_env_cwd()
  ```
- **Line 29**: `rt_dir_create()`
  ```simple
  rt_dir_create(build_dir, true)
  ```
- **Line 46**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(build_dir + "/Cargo.toml", cargo_toml)
  ```
- **Line 49**: `rt_dir_create()`
  ```simple
  rt_dir_create(build_dir + "/src", true)
  ```
- **Line 66**: `rt_process_run()`
  ```simple
  val result = rt_process_run("cargo", cargo_args)
  ```
- **Line 75**: `rt_dir_create()`
  ```simple
  rt_dir_create(script_dir + "/lib", true)
  ```
- **Line 78**: `rt_file_exists()`
  ```simple
  if rt_file_exists(so_file)
  ```
- **Line 79**: `rt_file_copy()`
  ```simple
  rt_file_copy(so_file, script_dir + "/lib/libsimple_ffi_wrapper.so")
  ```
- **Line 83**: `rt_file_exists()`
  ```simple
  if rt_file_exists(dylib_file)
  ```
- **Line 84**: `rt_file_copy()`
  ```simple
  rt_file_copy(dylib_file, script_dir + "/lib/libsimple_ffi_wrapper.dylib")
  ```
- **Line 88**: `rt_file_exists()`
  ```simple
  if rt_file_exists(a_file)
  ```
- **Line 89**: `rt_file_copy()`
  ```simple
  rt_file_copy(a_file, script_dir + "/lib/libsimple_ffi_wrapper.a")
  ```
- **Line 99**: `rt_file_exists()`
  ```simple
  if rt_file_exists(src_path)
  ```

#### `src/app/ffi_gen/test_gen.spl`

- **Line 109**: `rt_value_free()`
  ```simple
  out = out + "rt_value_free({var_name});"
  ```
- **Line 84**: `rt_not_null()`
  ```simple
  fn assert_not_null(var_name: text) -> text:
  ```
- **Line 88**: `rt_eq()`
  ```simple
  fn assert_eq(actual: text, expected: text) -> text:
  ```
- **Line 92**: `rt_true()`
  ```simple
  fn assert_true(condition: text) -> text:
  ```
- **Line 96**: `rt_false()`
  ```simple
  fn assert_false(condition: text) -> text:
  ```

#### `src/app/fix/main.spl`

- **Line 36**: `rt_by()`
  ```simple
  replacements = replacements.sort_by(a, b: b.start - a.start)
  ```

#### `src/app/fix/rules.spl`

- **Line 82**: `rt_offset()`
  ```simple
  fn line_start_offset(source: String, target_line: Int) -> Int:
  ```

#### `src/app/interpreter/ast_convert_expr.spl`

- **Line 106**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 117**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 126**: `rt_binary_expression()`
  ```simple
  fn convert_binary_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 14**: `rt_expression()`
  ```simple
  fn convert_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 155**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 174**: `rt_unary_expression()`
  ```simple
  fn convert_unary_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 188**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 202**: `rt_call_expression()`
  ```simple
  fn convert_call_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 211**: `rt_arguments()`
  ```simple
  args = convert_arguments(tree, child)
  ```
- **Line 214**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 228**: `rt_arguments()`
  ```simple
  fn convert_arguments(tree: &Tree, node: Node) -> Array<Expr>:
  ```
- **Line 234**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 241**: `rt_method_call()`
  ```simple
  fn convert_method_call(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 254**: `rt_arguments()`
  ```simple
  args = convert_arguments(tree, child)
  ```
- **Line 257**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 272**: `rt_index_expression()`
  ```simple
  fn convert_index_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 279**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 297**: `rt_field_expression()`
  ```simple
  fn convert_field_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 310**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 324**: `rt_array_literal()`
  ```simple
  fn convert_array_literal(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 330**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 337**: `rt_dict_literal()`
  ```simple
  fn convert_dict_literal(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 344**: `rt_dict_entry()`
  ```simple
  match convert_dict_entry(tree, child)
  ```
- **Line 351**: `rt_dict_entry()`
  ```simple
  fn convert_dict_entry(tree: &Tree, node: Node) -> Result<(Expr, Expr), String>:
  ```
- **Line 358**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 371**: `rt_tuple_literal()`
  ```simple
  fn convert_tuple_literal(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 377**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 384**: `rt_lambda()`
  ```simple
  fn convert_lambda(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 393**: `rt_lambda_params()`
  ```simple
  params = convert_lambda_params(tree, child)
  ```
- **Line 398**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 40**: `rt_binary_expression()`
  ```simple
  return convert_binary_expression(tree, node)
  ```
- **Line 412**: `rt_lambda_params()`
  ```simple
  fn convert_lambda_params(tree: &Tree, node: Node) -> Array<String>:
  ```
- **Line 424**: `rt_if_expression()`
  ```simple
  fn convert_if_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 432**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 44**: `rt_unary_expression()`
  ```simple
  return convert_unary_expression(tree, node)
  ```
- **Line 453**: `rt_match_expression()`
  ```simple
  fn convert_match_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 462**: `rt_match_arm()`
  ```simple
  match convert_match_arm(tree, child)
  ```
- **Line 467**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 481**: `rt_match_arm()`
  ```simple
  fn convert_match_arm(tree: &Tree, node: Node) -> Result<(Pattern, Expr), String>:
  ```
- **Line 48**: `rt_call_expression()`
  ```simple
  return convert_call_expression(tree, node)
  ```
- **Line 490**: `rt_pattern()`
  ```simple
  match convert_pattern(tree, child)
  ```
- **Line 495**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 499**: `rt_pattern()`
  ```simple
  match convert_pattern(tree, child)
  ```
- **Line 508**: `rt_range_expression()`
  ```simple
  fn convert_range_expression(tree: &Tree, node: Node) -> Result<Expr, String>:
  ```
- **Line 522**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 52**: `rt_method_call()`
  ```simple
  return convert_method_call(tree, node)
  ```
- **Line 56**: `rt_index_expression()`
  ```simple
  return convert_index_expression(tree, node)
  ```
- **Line 60**: `rt_field_expression()`
  ```simple
  return convert_field_expression(tree, node)
  ```
- **Line 64**: `rt_array_literal()`
  ```simple
  return convert_array_literal(tree, node)
  ```
- **Line 68**: `rt_dict_literal()`
  ```simple
  return convert_dict_literal(tree, node)
  ```
- **Line 72**: `rt_tuple_literal()`
  ```simple
  return convert_tuple_literal(tree, node)
  ```
- **Line 76**: `rt_lambda()`
  ```simple
  return convert_lambda(tree, node)
  ```
- **Line 80**: `rt_if_expression()`
  ```simple
  return convert_if_expression(tree, node)
  ```
- **Line 84**: `rt_match_expression()`
  ```simple
  return convert_match_expression(tree, node)
  ```
- **Line 88**: `rt_range_expression()`
  ```simple
  return convert_range_expression(tree, node)
  ```
- **Line 95**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```

#### `src/app/interpreter/ast_convert_pattern.spl`

- **Line 105**: `rt_pattern()`
  ```simple
  match convert_pattern(tree, child)
  ```
- **Line 114**: `rt_enum_pattern()`
  ```simple
  fn convert_enum_pattern(tree: &Tree, node: Node) -> Result<Pattern, String>:
  ```
- **Line 125**: `rt_pattern()`
  ```simple
  match convert_pattern(tree, child)
  ```
- **Line 13**: `rt_literal()`
  ```simple
  fn convert_literal(tree: &Tree, node: Node) -> Result<Literal, String>:
  ```
- **Line 38**: `rt_pattern()`
  ```simple
  fn convert_pattern(tree: &Tree, node: Node) -> Result<Pattern, String>:
  ```
- **Line 45**: `rt_literal()`
  ```simple
  match convert_literal(tree, node)
  ```
- **Line 49**: `rt_literal()`
  ```simple
  match convert_literal(tree, node)
  ```
- **Line 57**: `rt_pattern()`
  ```simple
  match convert_pattern(tree, child)
  ```
- **Line 63**: `rt_struct_pattern()`
  ```simple
  return convert_struct_pattern(tree, node)
  ```
- **Line 65**: `rt_enum_pattern()`
  ```simple
  return convert_enum_pattern(tree, node)
  ```
- **Line 70**: `rt_struct_pattern()`
  ```simple
  fn convert_struct_pattern(tree: &Tree, node: Node) -> Result<Pattern, String>:
  ```
- **Line 81**: `rt_field_pattern()`
  ```simple
  match convert_field_pattern(tree, child)
  ```
- **Line 91**: `rt_field_pattern()`
  ```simple
  fn convert_field_pattern(tree: &Tree, node: Node) -> Result<(String, Pattern), String>:
  ```

#### `src/app/interpreter/ast_convert.spl`

- **Line 38**: `rt_import()`
  ```simple
  match convert_import(&tree, child)
  ```
- **Line 45**: `rt_statement()`
  ```simple
  match convert_statement(&tree, child)
  ```
- **Line 52**: `rt_statement()`
  ```simple
  match convert_statement(&tree, child)
  ```
- **Line 76**: `rt_expression()`
  ```simple
  match convert_expression(&tree, child)
  ```
- **Line 82**: `rt_expression()`
  ```simple
  return convert_expression(&tree, root)
  ```

#### `src/app/interpreter/ast_convert_stmt.spl`

- **Line 111**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 127**: `rt_var_statement()`
  ```simple
  fn convert_var_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 141**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 157**: `rt_return_statement()`
  ```simple
  fn convert_return_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 15**: `rt_import()`
  ```simple
  fn convert_import(tree: &Tree, node: Node) -> Result<Import, String>:
  ```
- **Line 161**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 168**: `rt_if_statement()`
  ```simple
  fn convert_if_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 178**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 183**: `rt_block()`
  ```simple
  match convert_block(tree, child)
  ```
- **Line 187**: `rt_block()`
  ```simple
  match convert_block(tree, child)
  ```
- **Line 192**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 207**: `rt_match_statement()`
  ```simple
  fn convert_match_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 216**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 220**: `rt_case_clause()`
  ```simple
  match convert_case_clause(tree, child)
  ```
- **Line 225**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 239**: `rt_case_clause()`
  ```simple
  fn convert_case_clause(tree: &Tree, node: Node) -> Result<MatchCase, String>:
  ```
- **Line 249**: `rt_pattern()`
  ```simple
  match convert_pattern(tree, child)
  ```
- **Line 253**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 257**: `rt_block()`
  ```simple
  match convert_block(tree, child)
  ```
- **Line 262**: `rt_pattern()`
  ```simple
  match convert_pattern(tree, child)
  ```
- **Line 277**: `rt_for_statement()`
  ```simple
  fn convert_for_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 27**: `rt_names()`
  ```simple
  names = parse_import_names(tree, child)
  ```
- **Line 287**: `rt_pattern()`
  ```simple
  match convert_pattern(tree, child)
  ```
- **Line 291**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 295**: `rt_block()`
  ```simple
  match convert_block(tree, child)
  ```
- **Line 300**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 315**: `rt_while_statement()`
  ```simple
  fn convert_while_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 324**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 328**: `rt_block()`
  ```simple
  match convert_block(tree, child)
  ```
- **Line 333**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 347**: `rt_loop_statement()`
  ```simple
  fn convert_loop_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 352**: `rt_block()`
  ```simple
  match convert_block(tree, child)
  ```
- **Line 359**: `rt_function_def()`
  ```simple
  fn convert_function_def(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 372**: `rt_parameters()`
  ```simple
  params = convert_parameters(tree, child)
  ```
- **Line 376**: `rt_block()`
  ```simple
  match convert_block(tree, child)
  ```
- **Line 392**: `rt_parameters()`
  ```simple
  fn convert_parameters(tree: &Tree, node: Node) -> Array<Param>:
  ```
- **Line 399**: `rt_parameter()`
  ```simple
  match convert_parameter(tree, child)
  ```
- **Line 39**: `rt_names()`
  ```simple
  fn parse_import_names(tree: &Tree, node: Node) -> Array<String>:
  ```
- **Line 406**: `rt_parameter()`
  ```simple
  fn convert_parameter(tree: &Tree, node: Node) -> Result<Param, String>:
  ```
- **Line 420**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 431**: `rt_struct_def()`
  ```simple
  fn convert_struct_def(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 442**: `rt_struct_field()`
  ```simple
  match convert_struct_field(tree, child)
  ```
- **Line 452**: `rt_struct_field()`
  ```simple
  fn convert_struct_field(tree: &Tree, node: Node) -> Result<StructField, String>:
  ```
- **Line 472**: `rt_enum_def()`
  ```simple
  fn convert_enum_def(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 483**: `rt_enum_variant()`
  ```simple
  match convert_enum_variant(tree, child)
  ```
- **Line 493**: `rt_enum_variant()`
  ```simple
  fn convert_enum_variant(tree: &Tree, node: Node) -> Result<EnumVariant, String>:
  ```
- **Line 49**: `rt_statement()`
  ```simple
  fn convert_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 504**: `rt_variant_fields()`
  ```simple
  fields = Some(convert_variant_fields(tree, child))
  ```
- **Line 512**: `rt_variant_fields()`
  ```simple
  fn convert_variant_fields(tree: &Tree, node: Node) -> Array<StructField>:
  ```
- **Line 519**: `rt_struct_field()`
  ```simple
  match convert_struct_field(tree, child)
  ```
- **Line 526**: `rt_impl_def()`
  ```simple
  fn convert_impl_def(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```
- **Line 52**: `rt_let_statement()`
  ```simple
  return convert_let_statement(tree, node)
  ```
- **Line 540**: `rt_function_def()`
  ```simple
  match convert_function_def(tree, child)
  ```
- **Line 54**: `rt_var_statement()`
  ```simple
  return convert_var_statement(tree, node)
  ```
- **Line 551**: `rt_block()`
  ```simple
  fn convert_block(tree: &Tree, node: Node) -> Result<Block, String>:
  ```
- **Line 557**: `rt_statement()`
  ```simple
  match convert_statement(tree, child)
  ```
- **Line 56**: `rt_return_statement()`
  ```simple
  return convert_return_statement(tree, node)
  ```
- **Line 58**: `rt_if_statement()`
  ```simple
  return convert_if_statement(tree, node)
  ```
- **Line 60**: `rt_match_statement()`
  ```simple
  return convert_match_statement(tree, node)
  ```
- **Line 62**: `rt_for_statement()`
  ```simple
  return convert_for_statement(tree, node)
  ```
- **Line 64**: `rt_while_statement()`
  ```simple
  return convert_while_statement(tree, node)
  ```
- **Line 66**: `rt_loop_statement()`
  ```simple
  return convert_loop_statement(tree, node)
  ```
- **Line 74**: `rt_function_def()`
  ```simple
  return convert_function_def(tree, node)
  ```
- **Line 76**: `rt_struct_def()`
  ```simple
  return convert_struct_def(tree, node)
  ```
- **Line 78**: `rt_enum_def()`
  ```simple
  return convert_enum_def(tree, node)
  ```
- **Line 80**: `rt_impl_def()`
  ```simple
  return convert_impl_def(tree, node)
  ```
- **Line 86**: `rt_expression()`
  ```simple
  match convert_expression(tree, child)
  ```
- **Line 93**: `rt_expression()`
  ```simple
  match convert_expression(tree, node)
  ```
- **Line 97**: `rt_let_statement()`
  ```simple
  fn convert_let_statement(tree: &Tree, node: Node) -> Result<Statement, String>:
  ```

#### `src/app/interpreter/call/builtins.spl`

- **Line 160**: `rt_value()`
  ```simple
  args[0].sqrt_value()
  ```

#### `src/app/interpreter/extern/collections.spl`

- **Line 108**: `rt_hashmap_remove()`
  ```simple
  Ok(Value.bool(__rt_hashmap_remove(h, k)))
  ```
- **Line 115**: `rt_hashmap_contains()`
  ```simple
  Ok(Value.bool(__rt_hashmap_contains(h, k)))
  ```
- **Line 119**: `rt_hashmap_len()`
  ```simple
  Ok(Value.int(__rt_hashmap_len(h)))
  ```
- **Line 123**: `rt_hashmap_keys()`
  ```simple
  Ok(Value.array(__rt_hashmap_keys(h).map(k: Value.string(k))))
  ```
- **Line 127**: `rt_hashmap_values()`
  ```simple
  Ok(Value.array(__rt_hashmap_values(h).map(v: Value.from_handle(v))))
  ```
- **Line 131**: `rt_hashmap_keys()`
  ```simple
  val keys = __rt_hashmap_keys(h)
  ```
- **Line 132**: `rt_hashmap_values()`
  ```simple
  val values = __rt_hashmap_values(h)
  ```
- **Line 138**: `rt_hashmap_clear()`
  ```simple
  __rt_hashmap_clear(h)
  ```
- **Line 143**: `rt_hashmap_free()`
  ```simple
  __rt_hashmap_free(h)
  ```
- **Line 151**: `rt_hashset_new()`
  ```simple
  Ok(Value.int(__rt_hashset_new()))
  ```
- **Line 158**: `rt_hashset_insert()`
  ```simple
  Ok(Value.bool(__rt_hashset_insert(h, k)))
  ```
- **Line 165**: `rt_hashset_contains()`
  ```simple
  Ok(Value.bool(__rt_hashset_contains(h, k)))
  ```
- **Line 172**: `rt_hashset_remove()`
  ```simple
  Ok(Value.bool(__rt_hashset_remove(h, k)))
  ```
- **Line 176**: `rt_hashset_len()`
  ```simple
  Ok(Value.int(__rt_hashset_len(h)))
  ```
- **Line 180**: `rt_hashset_to_array()`
  ```simple
  Ok(Value.array(__rt_hashset_to_array(h).map(k: Value.string(k))))
  ```
- **Line 184**: `rt_hashset_clear()`
  ```simple
  __rt_hashset_clear(h)
  ```
- **Line 189**: `rt_hashset_free()`
  ```simple
  __rt_hashset_free(h)
  ```
- **Line 197**: `rt_btreemap_new()`
  ```simple
  Ok(Value.int(__rt_btreemap_new()))
  ```
- **Line 204**: `rt_btreemap_insert()`
  ```simple
  Ok(Value.bool(__rt_btreemap_insert(h, k, args[2].to_handle())))
  ```
- **Line 211**: `rt_btreemap_get()`
  ```simple
  val result = __rt_btreemap_get(h, k)
  ```
- **Line 222**: `rt_btreemap_remove()`
  ```simple
  Ok(Value.bool(__rt_btreemap_remove(h, k)))
  ```
- **Line 229**: `rt_btreemap_contains()`
  ```simple
  Ok(Value.bool(__rt_btreemap_contains(h, k)))
  ```
- **Line 233**: `rt_btreemap_len()`
  ```simple
  Ok(Value.int(__rt_btreemap_len(h)))
  ```
- **Line 237**: `rt_btreemap_keys()`
  ```simple
  Ok(Value.array(__rt_btreemap_keys(h).map(k: Value.string(k))))
  ```
- **Line 241**: `rt_btreemap_free()`
  ```simple
  __rt_btreemap_free(h)
  ```
- **Line 249**: `rt_vec_new()`
  ```simple
  Ok(Value.int(__rt_vec_new()))
  ```
- **Line 255**: `rt_vec_push()`
  ```simple
  __rt_vec_push(h, args[1].to_handle())
  ```
- **Line 25**: `rt_hashmap_new()`
  ```simple
  extern fn __rt_hashmap_new() -> i64
  ```
- **Line 260**: `rt_vec_pop()`
  ```simple
  val result = __rt_vec_pop(h)
  ```
- **Line 26**: `rt_hashmap_insert()`
  ```simple
  extern fn __rt_hashmap_insert(handle: i64, key: text, value: i64) -> bool
  ```
- **Line 271**: `rt_vec_get()`
  ```simple
  val result = __rt_vec_get(h, idx)
  ```
- **Line 27**: `rt_hashmap_get()`
  ```simple
  extern fn __rt_hashmap_get(handle: i64, key: text) -> i64?
  ```
- **Line 282**: `rt_vec_set()`
  ```simple
  __rt_vec_set(h, idx, args[2].to_handle())
  ```
- **Line 287**: `rt_vec_len()`
  ```simple
  Ok(Value.int(__rt_vec_len(h)))
  ```
- **Line 28**: `rt_hashmap_remove()`
  ```simple
  extern fn __rt_hashmap_remove(handle: i64, key: text) -> bool
  ```
- **Line 291**: `rt_vec_clear()`
  ```simple
  __rt_vec_clear(h)
  ```
- **Line 296**: `rt_vec_to_array()`
  ```simple
  Ok(Value.array(__rt_vec_to_array(h).map(v: Value.from_handle(v))))
  ```
- **Line 29**: `rt_hashmap_contains()`
  ```simple
  extern fn __rt_hashmap_contains(handle: i64, key: text) -> bool
  ```
- **Line 300**: `rt_vec_free()`
  ```simple
  __rt_vec_free(h)
  ```
- **Line 30**: `rt_hashmap_len()`
  ```simple
  extern fn __rt_hashmap_len(handle: i64) -> i64
  ```
- **Line 31**: `rt_hashmap_keys()`
  ```simple
  extern fn __rt_hashmap_keys(handle: i64) -> [text]
  ```
- **Line 32**: `rt_hashmap_values()`
  ```simple
  extern fn __rt_hashmap_values(handle: i64) -> [i64]
  ```
- **Line 33**: `rt_hashmap_clear()`
  ```simple
  extern fn __rt_hashmap_clear(handle: i64)
  ```
- **Line 34**: `rt_hashmap_free()`
  ```simple
  extern fn __rt_hashmap_free(handle: i64)
  ```
- **Line 36**: `rt_hashset_new()`
  ```simple
  extern fn __rt_hashset_new() -> i64
  ```
- **Line 37**: `rt_hashset_insert()`
  ```simple
  extern fn __rt_hashset_insert(handle: i64, key: text) -> bool
  ```
- **Line 38**: `rt_hashset_contains()`
  ```simple
  extern fn __rt_hashset_contains(handle: i64, key: text) -> bool
  ```
- **Line 39**: `rt_hashset_remove()`
  ```simple
  extern fn __rt_hashset_remove(handle: i64, key: text) -> bool
  ```
- **Line 40**: `rt_hashset_len()`
  ```simple
  extern fn __rt_hashset_len(handle: i64) -> i64
  ```
- **Line 41**: `rt_hashset_to_array()`
  ```simple
  extern fn __rt_hashset_to_array(handle: i64) -> [text]
  ```
- **Line 42**: `rt_hashset_clear()`
  ```simple
  extern fn __rt_hashset_clear(handle: i64)
  ```
- **Line 43**: `rt_hashset_free()`
  ```simple
  extern fn __rt_hashset_free(handle: i64)
  ```
- **Line 45**: `rt_btreemap_new()`
  ```simple
  extern fn __rt_btreemap_new() -> i64
  ```
- **Line 46**: `rt_btreemap_insert()`
  ```simple
  extern fn __rt_btreemap_insert(handle: i64, key: text, value: i64) -> bool
  ```
- **Line 47**: `rt_btreemap_get()`
  ```simple
  extern fn __rt_btreemap_get(handle: i64, key: text) -> i64?
  ```
- **Line 48**: `rt_btreemap_remove()`
  ```simple
  extern fn __rt_btreemap_remove(handle: i64, key: text) -> bool
  ```
- **Line 49**: `rt_btreemap_contains()`
  ```simple
  extern fn __rt_btreemap_contains(handle: i64, key: text) -> bool
  ```
- **Line 50**: `rt_btreemap_len()`
  ```simple
  extern fn __rt_btreemap_len(handle: i64) -> i64
  ```
- **Line 51**: `rt_btreemap_keys()`
  ```simple
  extern fn __rt_btreemap_keys(handle: i64) -> [text]
  ```
- **Line 52**: `rt_btreemap_free()`
  ```simple
  extern fn __rt_btreemap_free(handle: i64)
  ```
- **Line 54**: `rt_vec_new()`
  ```simple
  extern fn __rt_vec_new() -> i64
  ```
- **Line 55**: `rt_vec_push()`
  ```simple
  extern fn __rt_vec_push(handle: i64, value: i64)
  ```
- **Line 56**: `rt_vec_pop()`
  ```simple
  extern fn __rt_vec_pop(handle: i64) -> i64?
  ```
- **Line 57**: `rt_vec_get()`
  ```simple
  extern fn __rt_vec_get(handle: i64, idx: i64) -> i64?
  ```
- **Line 58**: `rt_vec_set()`
  ```simple
  extern fn __rt_vec_set(handle: i64, idx: i64, value: i64)
  ```
- **Line 59**: `rt_vec_len()`
  ```simple
  extern fn __rt_vec_len(handle: i64) -> i64
  ```
- **Line 60**: `rt_vec_clear()`
  ```simple
  extern fn __rt_vec_clear(handle: i64)
  ```
- **Line 61**: `rt_vec_to_array()`
  ```simple
  extern fn __rt_vec_to_array(handle: i64) -> [i64]
  ```
- **Line 62**: `rt_vec_free()`
  ```simple
  extern fn __rt_vec_free(handle: i64)
  ```
- **Line 83**: `rt_hashmap_new()`
  ```simple
  Ok(Value.int(__rt_hashmap_new()))
  ```
- **Line 90**: `rt_hashmap_insert()`
  ```simple
  Ok(Value.bool(__rt_hashmap_insert(h, k, args[2].to_handle())))
  ```
- **Line 97**: `rt_hashmap_get()`
  ```simple
  val result = __rt_hashmap_get(h, k)
  ```

#### `src/app/interpreter/extern/coverage.spl`

- **Line 36**: `rt_coverage_enabled()`
  ```simple
  fn _rt_coverage_enabled() -> bool
  ```
- **Line 39**: `rt_coverage_clear()`
  ```simple
  fn _rt_coverage_clear()
  ```
- **Line 42**: `rt_coverage_dump_sdn()`
  ```simple
  fn _rt_coverage_dump_sdn() -> text
  ```
- **Line 81**: `rt_coverage_enabled()`
  ```simple
  fn rt_coverage_enabled(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 82**: `rt_coverage_enabled()`
  ```simple
  Ok(Value.bool(_rt_coverage_enabled()))
  ```
- **Line 84**: `rt_coverage_clear()`
  ```simple
  fn rt_coverage_clear(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 85**: `rt_coverage_clear()`
  ```simple
  _rt_coverage_clear()
  ```
- **Line 88**: `rt_coverage_dump_sdn()`
  ```simple
  fn rt_coverage_dump_sdn(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 89**: `rt_coverage_dump_sdn()`
  ```simple
  Ok(Value.string(_rt_coverage_dump_sdn()))
  ```
- **Line 91**: `rt_coverage_free_sdn()`
  ```simple
  fn rt_coverage_free_sdn(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 95**: `rt_cstring_to_text()`
  ```simple
  fn rt_cstring_to_text(args: [Value]) -> Result<Value, InterpreterError>:
  ```

#### `src/app/interpreter/extern/math.spl`

- **Line 100**: `rt_math_sin()`
  ```simple
  fn rt_math_sin(x: f64) -> f64
  ```
- **Line 103**: `rt_math_cos()`
  ```simple
  fn rt_math_cos(x: f64) -> f64
  ```
- **Line 106**: `rt_math_tan()`
  ```simple
  fn rt_math_tan(x: f64) -> f64
  ```
- **Line 109**: `rt_math_asin()`
  ```simple
  fn rt_math_asin(x: f64) -> f64
  ```
- **Line 112**: `rt_math_acos()`
  ```simple
  fn rt_math_acos(x: f64) -> f64
  ```
- **Line 115**: `rt_math_atan()`
  ```simple
  fn rt_math_atan(x: f64) -> f64
  ```
- **Line 121**: `rt_math_sinh()`
  ```simple
  fn rt_math_sinh(x: f64) -> f64
  ```
- **Line 124**: `rt_math_cosh()`
  ```simple
  fn rt_math_cosh(x: f64) -> f64
  ```
- **Line 127**: `rt_math_tanh()`
  ```simple
  fn rt_math_tanh(x: f64) -> f64
  ```
- **Line 130**: `rt_math_floor_f()`
  ```simple
  fn rt_math_floor_f(x: f64) -> f64
  ```
- **Line 133**: `rt_math_ceil_f()`
  ```simple
  fn rt_math_ceil_f(x: f64) -> f64
  ```
- **Line 136**: `rt_math_nan()`
  ```simple
  fn rt_math_nan() -> f64
  ```
- **Line 139**: `rt_math_inf()`
  ```simple
  fn rt_math_inf() -> f64
  ```
- **Line 142**: `rt_math_is_nan()`
  ```simple
  fn rt_math_is_nan(x: f64) -> bool
  ```
- **Line 145**: `rt_math_is_inf()`
  ```simple
  fn rt_math_is_inf(x: f64) -> bool
  ```
- **Line 148**: `rt_math_is_finite()`
  ```simple
  fn rt_math_is_finite(x: f64) -> bool
  ```
- **Line 151**: `rt_math_round()`
  ```simple
  fn rt_math_round(x: f64) -> f64
  ```
- **Line 154**: `rt_math_trunc()`
  ```simple
  fn rt_math_trunc(x: f64) -> f64
  ```
- **Line 157**: `rt_math_abs()`
  ```simple
  fn rt_math_abs(x: f64) -> f64
  ```
- **Line 160**: `rt_math_hypot()`
  ```simple
  fn rt_math_hypot(x: f64, y: f64) -> f64
  ```
- **Line 163**: `rt_math_gcd()`
  ```simple
  fn rt_math_gcd(a: i64, b: i64) -> i64
  ```
- **Line 166**: `rt_math_lcm()`
  ```simple
  fn rt_math_lcm(a: i64, b: i64) -> i64
  ```
- **Line 169**: `rt_math_min_f()`
  ```simple
  fn rt_math_min_f(x: f64, y: f64) -> f64
  ```
- **Line 172**: `rt_math_max_f()`
  ```simple
  fn rt_math_max_f(x: f64, y: f64) -> f64
  ```
- **Line 175**: `rt_math_clamp()`
  ```simple
  fn rt_math_clamp(x: f64, min_val: f64, max_val: f64) -> f64
  ```
- **Line 178**: `rt_math_sign()`
  ```simple
  fn rt_math_sign(x: f64) -> f64
  ```
- **Line 181**: `rt_math_fract()`
  ```simple
  fn rt_math_fract(x: f64) -> f64
  ```
- **Line 184**: `rt_math_rem()`
  ```simple
  fn rt_math_rem(x: f64, y: f64) -> f64
  ```
- **Line 193**: `rt_math_pow_extern()`
  ```simple
  fn rt_math_pow_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 194**: `rt_math_pow()`
  ```simple
  Ok(Value.float(rt_math_pow(_get_float_arg(args, 0)?, _get_float_arg(args, 1)?)))
  ```
- **Line 196**: `rt_math_log_extern()`
  ```simple
  fn rt_math_log_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 197**: `rt_math_log()`
  ```simple
  Ok(Value.float(rt_math_log(_get_float_arg(args, 0)?)))
  ```
- **Line 205**: `rt_math_exp_extern()`
  ```simple
  fn rt_math_exp_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 206**: `rt_math_exp()`
  ```simple
  Ok(Value.float(rt_math_exp(_get_float_arg(args, 0)?)))
  ```
- **Line 208**: `rt_math_sqrt_extern()`
  ```simple
  fn rt_math_sqrt_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 209**: `rt_math_sqrt()`
  ```simple
  Ok(Value.float(rt_math_sqrt(_get_float_arg(args, 0)?)))
  ```
- **Line 211**: `rt_math_cbrt_extern()`
  ```simple
  fn rt_math_cbrt_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 212**: `rt_math_cbrt()`
  ```simple
  Ok(Value.float(rt_math_cbrt(_get_float_arg(args, 0)?)))
  ```
- **Line 214**: `rt_math_sin_extern()`
  ```simple
  fn rt_math_sin_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 215**: `rt_math_sin()`
  ```simple
  Ok(Value.float(rt_math_sin(_get_float_arg(args, 0)?)))
  ```
- **Line 217**: `rt_math_cos_extern()`
  ```simple
  fn rt_math_cos_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 218**: `rt_math_cos()`
  ```simple
  Ok(Value.float(rt_math_cos(_get_float_arg(args, 0)?)))
  ```
- **Line 220**: `rt_math_tan_extern()`
  ```simple
  fn rt_math_tan_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 221**: `rt_math_tan()`
  ```simple
  Ok(Value.float(rt_math_tan(_get_float_arg(args, 0)?)))
  ```
- **Line 223**: `rt_math_asin_extern()`
  ```simple
  fn rt_math_asin_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 224**: `rt_math_asin()`
  ```simple
  Ok(Value.float(rt_math_asin(_get_float_arg(args, 0)?)))
  ```
- **Line 226**: `rt_math_acos_extern()`
  ```simple
  fn rt_math_acos_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 227**: `rt_math_acos()`
  ```simple
  Ok(Value.float(rt_math_acos(_get_float_arg(args, 0)?)))
  ```
- **Line 229**: `rt_math_atan_extern()`
  ```simple
  fn rt_math_atan_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 230**: `rt_math_atan()`
  ```simple
  Ok(Value.float(rt_math_atan(_get_float_arg(args, 0)?)))
  ```
- **Line 235**: `rt_math_sinh_extern()`
  ```simple
  fn rt_math_sinh_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 236**: `rt_math_sinh()`
  ```simple
  Ok(Value.float(rt_math_sinh(_get_float_arg(args, 0)?)))
  ```
- **Line 238**: `rt_math_cosh_extern()`
  ```simple
  fn rt_math_cosh_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 239**: `rt_math_cosh()`
  ```simple
  Ok(Value.float(rt_math_cosh(_get_float_arg(args, 0)?)))
  ```
- **Line 241**: `rt_math_tanh_extern()`
  ```simple
  fn rt_math_tanh_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 242**: `rt_math_tanh()`
  ```simple
  Ok(Value.float(rt_math_tanh(_get_float_arg(args, 0)?)))
  ```
- **Line 244**: `rt_math_floor_extern()`
  ```simple
  fn rt_math_floor_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 245**: `rt_math_floor_f()`
  ```simple
  Ok(Value.float(rt_math_floor_f(_get_float_arg(args, 0)?)))
  ```
- **Line 247**: `rt_math_ceil_extern()`
  ```simple
  fn rt_math_ceil_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 248**: `rt_math_ceil_f()`
  ```simple
  Ok(Value.float(rt_math_ceil_f(_get_float_arg(args, 0)?)))
  ```
- **Line 250**: `rt_math_nan_extern()`
  ```simple
  fn rt_math_nan_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 251**: `rt_math_nan()`
  ```simple
  Ok(Value.float(rt_math_nan()))
  ```
- **Line 253**: `rt_math_inf_extern()`
  ```simple
  fn rt_math_inf_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 254**: `rt_math_inf()`
  ```simple
  Ok(Value.float(rt_math_inf()))
  ```
- **Line 256**: `rt_math_is_nan_extern()`
  ```simple
  fn rt_math_is_nan_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 257**: `rt_math_is_nan()`
  ```simple
  Ok(Value.bool(rt_math_is_nan(_get_float_arg(args, 0)?)))
  ```
- **Line 259**: `rt_math_is_inf_extern()`
  ```simple
  fn rt_math_is_inf_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 260**: `rt_math_is_inf()`
  ```simple
  Ok(Value.bool(rt_math_is_inf(_get_float_arg(args, 0)?)))
  ```
- **Line 262**: `rt_math_is_finite_extern()`
  ```simple
  fn rt_math_is_finite_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 263**: `rt_math_is_finite()`
  ```simple
  Ok(Value.bool(rt_math_is_finite(_get_float_arg(args, 0)?)))
  ```
- **Line 265**: `rt_math_round_extern()`
  ```simple
  fn rt_math_round_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 266**: `rt_math_round()`
  ```simple
  Ok(Value.float(rt_math_round(_get_float_arg(args, 0)?)))
  ```
- **Line 268**: `rt_math_trunc_extern()`
  ```simple
  fn rt_math_trunc_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 269**: `rt_math_trunc()`
  ```simple
  Ok(Value.float(rt_math_trunc(_get_float_arg(args, 0)?)))
  ```
- **Line 271**: `rt_math_abs_extern()`
  ```simple
  fn rt_math_abs_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 272**: `rt_math_abs()`
  ```simple
  Ok(Value.float(rt_math_abs(_get_float_arg(args, 0)?)))
  ```
- **Line 274**: `rt_math_hypot_extern()`
  ```simple
  fn rt_math_hypot_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 275**: `rt_math_hypot()`
  ```simple
  Ok(Value.float(rt_math_hypot(_get_float_arg(args, 0)?, _get_float_arg(args, 1)?)))
  ```
- **Line 282**: `rt_math_gcd_extern()`
  ```simple
  fn rt_math_gcd_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 283**: `rt_math_gcd()`
  ```simple
  Ok(Value.int(rt_math_gcd(_get_int_arg(args, 0)?, _get_int_arg(args, 1)?)))
  ```
- **Line 285**: `rt_math_lcm_extern()`
  ```simple
  fn rt_math_lcm_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 286**: `rt_math_lcm()`
  ```simple
  Ok(Value.int(rt_math_lcm(_get_int_arg(args, 0)?, _get_int_arg(args, 1)?)))
  ```
- **Line 288**: `rt_math_min_f_extern()`
  ```simple
  fn rt_math_min_f_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 289**: `rt_math_min_f()`
  ```simple
  Ok(Value.float(rt_math_min_f(_get_float_arg(args, 0)?, _get_float_arg(args, 1)?)))
  ```
- **Line 291**: `rt_math_max_f_extern()`
  ```simple
  fn rt_math_max_f_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 292**: `rt_math_max_f()`
  ```simple
  Ok(Value.float(rt_math_max_f(_get_float_arg(args, 0)?, _get_float_arg(args, 1)?)))
  ```
- **Line 294**: `rt_math_clamp_extern()`
  ```simple
  fn rt_math_clamp_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 295**: `rt_math_clamp()`
  ```simple
  Ok(Value.float(rt_math_clamp(_get_float_arg(args, 0)?, _get_float_arg(args, 1)?, _get_float_arg(args, 2)?)))
  ```
- **Line 297**: `rt_math_sign_extern()`
  ```simple
  fn rt_math_sign_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 298**: `rt_math_sign()`
  ```simple
  Ok(Value.float(rt_math_sign(_get_float_arg(args, 0)?)))
  ```
- **Line 300**: `rt_math_fract_extern()`
  ```simple
  fn rt_math_fract_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 301**: `rt_math_fract()`
  ```simple
  Ok(Value.float(rt_math_fract(_get_float_arg(args, 0)?)))
  ```
- **Line 303**: `rt_math_rem_extern()`
  ```simple
  fn rt_math_rem_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 304**: `rt_math_rem()`
  ```simple
  Ok(Value.float(rt_math_rem(_get_float_arg(args, 0)?, _get_float_arg(args, 1)?)))
  ```
- **Line 47**: `rt_extern()`
  ```simple
  fn sqrt_extern(args: [Value]) -> Result<Value, InterpreterError>:
  ```
- **Line 52**: `rt_math_sqrt()`
  ```simple
  Ok(Value.int(rt_math_sqrt(n.to_float()).to_int()))
  ```
- **Line 79**: `rt_math_pow()`
  ```simple
  fn rt_math_pow(base: f64, exp: f64) -> f64
  ```
- **Line 82**: `rt_math_log()`
  ```simple
  fn rt_math_log(x: f64) -> f64
  ```
- **Line 91**: `rt_math_exp()`
  ```simple
  fn rt_math_exp(x: f64) -> f64
  ```
- **Line 94**: `rt_math_sqrt()`
  ```simple
  fn rt_math_sqrt(x: f64) -> f64
  ```
- **Line 97**: `rt_math_cbrt()`
  ```simple
  fn rt_math_cbrt(x: f64) -> f64
  ```

#### `src/app/interpreter/extern/random.spl`

- **Line 13**: `rt_random_seed()`
  ```simple
  fn _rt_random_seed(seed: i64)
  ```
- **Line 16**: `rt_random_getstate()`
  ```simple
  fn _rt_random_getstate() -> i64
  ```
- **Line 19**: `rt_random_setstate()`
  ```simple
  fn _rt_random_setstate(state: i64)
  ```
- **Line 22**: `rt_random_next()`
  ```simple
  fn _rt_random_next() -> i64
  ```
- **Line 25**: `rt_random_randint()`
  ```simple
  fn _rt_random_randint(min: i64, max: i64) -> i64
  ```
- **Line 28**: `rt_random_random()`
  ```simple
  fn _rt_random_random() -> f64
  ```
- **Line 31**: `rt_random_uniform()`
  ```simple
  fn _rt_random_uniform(min: f64, max: f64) -> f64
  ```
- **Line 37**: `rt_random_seed()`
  ```simple
  _rt_random_seed(seed)
  ```
- **Line 41**: `rt_random_getstate()`
  ```simple
  Ok(Value.int(_rt_random_getstate()))
  ```
- **Line 47**: `rt_random_setstate()`
  ```simple
  _rt_random_setstate(state)
  ```
- **Line 51**: `rt_random_next()`
  ```simple
  Ok(Value.int(_rt_random_next()))
  ```
- **Line 58**: `rt_random_randint()`
  ```simple
  Ok(Value.int(_rt_random_randint(min, max)))
  ```
- **Line 61**: `rt_random_random()`
  ```simple
  Ok(Value.float(_rt_random_random()))
  ```
- **Line 68**: `rt_random_uniform()`
  ```simple
  Ok(Value.float(_rt_random_uniform(min, max)))
  ```

#### `src/app/interpreter/extern/sdn.spl`

- **Line 15**: `rt_sdn_check()`
  ```simple
  fn _rt_sdn_check(path: text) -> i64
  ```
- **Line 18**: `rt_sdn_to_json()`
  ```simple
  fn _rt_sdn_to_json(path: text) -> text
  ```
- **Line 21**: `rt_sdn_from_json()`
  ```simple
  fn _rt_sdn_from_json(path: text) -> text
  ```
- **Line 24**: `rt_sdn_get()`
  ```simple
  fn _rt_sdn_get(path: text, key: text) -> text
  ```
- **Line 27**: `rt_sdn_set()`
  ```simple
  fn _rt_sdn_set(path: text, key: text, value: text) -> i64
  ```
- **Line 30**: `rt_sdn_fmt()`
  ```simple
  fn _rt_sdn_fmt(path: text) -> i64
  ```
- **Line 37**: `rt_sdn_check()`
  ```simple
  Ok(Value.int(_rt_sdn_check(path)))
  ```
- **Line 41**: `rt_sdn_to_json()`
  ```simple
  Ok(Value.string(_rt_sdn_to_json(path)))
  ```
- **Line 45**: `rt_sdn_from_json()`
  ```simple
  Ok(Value.string(_rt_sdn_from_json(path)))
  ```
- **Line 50**: `rt_sdn_get()`
  ```simple
  Ok(Value.string(_rt_sdn_get(path, key)))
  ```
- **Line 56**: `rt_sdn_set()`
  ```simple
  Ok(Value.int(_rt_sdn_set(path, key, value)))
  ```
- **Line 60**: `rt_sdn_fmt()`
  ```simple
  Ok(Value.int(_rt_sdn_fmt(path)))
  ```

#### `src/app/interpreter/extern/time.spl`

- **Line 102**: `rt_timestamp_get_hour()`
  ```simple
  Ok(Value.int(_rt_timestamp_get_hour(_get_micros_arg(args)?).to_i64()))
  ```
- **Line 105**: `rt_timestamp_get_minute()`
  ```simple
  Ok(Value.int(_rt_timestamp_get_minute(_get_micros_arg(args)?).to_i64()))
  ```
- **Line 108**: `rt_timestamp_get_second()`
  ```simple
  Ok(Value.int(_rt_timestamp_get_second(_get_micros_arg(args)?).to_i64()))
  ```
- **Line 111**: `rt_timestamp_get_microsecond()`
  ```simple
  Ok(Value.int(_rt_timestamp_get_microsecond(_get_micros_arg(args)?).to_i64()))
  ```
- **Line 124**: `rt_timestamp_from_components()`
  ```simple
  Ok(Value.int(_rt_timestamp_from_components(
  ```
- **Line 133**: `rt_timestamp_add_days()`
  ```simple
  Ok(Value.int(_rt_timestamp_add_days(micros, days)))
  ```
- **Line 140**: `rt_timestamp_diff_days()`
  ```simple
  Ok(Value.int(_rt_timestamp_diff_days(micros1, micros2)))
  ```
- **Line 18**: `rt_time_now_seconds()`
  ```simple
  fn _rt_time_now_seconds() -> f64
  ```
- **Line 21**: `rt_progress_init()`
  ```simple
  fn _rt_progress_init()
  ```
- **Line 24**: `rt_progress_reset()`
  ```simple
  fn _rt_progress_reset()
  ```
- **Line 27**: `rt_progress_get_elapsed_seconds()`
  ```simple
  fn _rt_progress_get_elapsed_seconds() -> f64
  ```
- **Line 30**: `rt_time_now_unix_micros()`
  ```simple
  fn _rt_time_now_unix_micros() -> i64
  ```
- **Line 33**: `rt_timestamp_get_year()`
  ```simple
  fn _rt_timestamp_get_year(micros: i64) -> i32
  ```
- **Line 36**: `rt_timestamp_get_month()`
  ```simple
  fn _rt_timestamp_get_month(micros: i64) -> i32
  ```
- **Line 39**: `rt_timestamp_get_day()`
  ```simple
  fn _rt_timestamp_get_day(micros: i64) -> i32
  ```
- **Line 42**: `rt_timestamp_get_hour()`
  ```simple
  fn _rt_timestamp_get_hour(micros: i64) -> i32
  ```
- **Line 45**: `rt_timestamp_get_minute()`
  ```simple
  fn _rt_timestamp_get_minute(micros: i64) -> i32
  ```
- **Line 48**: `rt_timestamp_get_second()`
  ```simple
  fn _rt_timestamp_get_second(micros: i64) -> i32
  ```
- **Line 51**: `rt_timestamp_get_microsecond()`
  ```simple
  fn _rt_timestamp_get_microsecond(micros: i64) -> i32
  ```
- **Line 54**: `rt_timestamp_from_components()`
  ```simple
  fn _rt_timestamp_from_components(year: i32, month: i32, day: i32,
  ```
- **Line 59**: `rt_timestamp_add_days()`
  ```simple
  fn _rt_timestamp_add_days(micros: i64, days: i64) -> i64
  ```
- **Line 62**: `rt_timestamp_diff_days()`
  ```simple
  fn _rt_timestamp_diff_days(micros1: i64, micros2: i64) -> i64
  ```
- **Line 65**: `rt_time_now_seconds()`
  ```simple
  Ok(Value.float(_rt_time_now_seconds()))
  ```
- **Line 68**: `rt_time_now_seconds()`
  ```simple
  Ok(Value.int(_rt_time_now_seconds().to_int()))
  ```
- **Line 71**: `rt_time_now_seconds()`
  ```simple
  Ok(Value.int((_rt_time_now_seconds() * 1000.0).to_int()))
  ```
- **Line 74**: `rt_progress_init()`
  ```simple
  _rt_progress_init()
  ```
- **Line 78**: `rt_progress_reset()`
  ```simple
  _rt_progress_reset()
  ```
- **Line 82**: `rt_progress_get_elapsed_seconds()`
  ```simple
  Ok(Value.float(_rt_progress_get_elapsed_seconds()))
  ```
- **Line 85**: `rt_time_now_unix_micros()`
  ```simple
  Ok(Value.int(_rt_time_now_unix_micros()))
  ```
- **Line 93**: `rt_timestamp_get_year()`
  ```simple
  Ok(Value.int(_rt_timestamp_get_year(_get_micros_arg(args)?).to_i64()))
  ```
- **Line 96**: `rt_timestamp_get_month()`
  ```simple
  Ok(Value.int(_rt_timestamp_get_month(_get_micros_arg(args)?).to_i64()))
  ```
- **Line 99**: `rt_timestamp_get_day()`
  ```simple
  Ok(Value.int(_rt_timestamp_get_day(_get_micros_arg(args)?).to_i64()))
  ```

#### `src/app/interpreter/ffi/eval_slice.spl`

- **Line 109**: `rt_error_division_by_zero()`
  ```simple
  val err = rt_error_division_by_zero()
  ```
- **Line 110**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```
- **Line 116**: `rt_error_division_by_zero()`
  ```simple
  val err = rt_error_division_by_zero()
  ```
- **Line 117**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```
- **Line 129**: `rt_error_semantic()`
  ```simple
  val err = rt_error_semantic("unsupported binary op for integers: {op}")
  ```
- **Line 130**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```
- **Line 144**: `rt_error_semantic()`
  ```simple
  val err = rt_error_semantic("unsupported binary op for floats: {op}")
  ```
- **Line 145**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```
- **Line 154**: `rt_error_semantic()`
  ```simple
  val err = rt_error_semantic("unsupported binary op for strings: {op}")
  ```
- **Line 155**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```
- **Line 165**: `rt_error_semantic()`
  ```simple
  val err = rt_error_semantic("unsupported binary op for bools: {op}")
  ```
- **Line 166**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```
- **Line 170**: `rt_error_type_mismatch()`
  ```simple
  val err = rt_error_type_mismatch("binary op type mismatch for op: {op}")
  ```
- **Line 171**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```
- **Line 184**: `rt_error_type_mismatch()`
  ```simple
  val err = rt_error_type_mismatch("unsupported unary op: {op}")
  ```
- **Line 185**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```
- **Line 35**: `rt_ast_expr_tag()`
  ```simple
  val tag = rt_ast_expr_tag(expr_handle)
  ```
- **Line 39**: `rt_ast_expr_int_value()`
  ```simple
  val v = rt_ast_expr_int_value(expr_handle)
  ```
- **Line 43**: `rt_ast_expr_float_value()`
  ```simple
  val v = rt_ast_expr_float_value(expr_handle)
  ```
- **Line 47**: `rt_ast_expr_string_value()`
  ```simple
  val v = rt_ast_expr_string_value(expr_handle)
  ```
- **Line 51**: `rt_ast_expr_bool_value()`
  ```simple
  val v = rt_ast_expr_bool_value(expr_handle)
  ```
- **Line 58**: `rt_ast_expr_ident_name()`
  ```simple
  val name = rt_ast_expr_ident_name(expr_handle)
  ```
- **Line 59**: `rt_env_get_var()`
  ```simple
  val v = rt_env_get_var(env_handle, name)
  ```
- **Line 74**: `rt_ast_expr_binary_op()`
  ```simple
  val op = rt_ast_expr_binary_op(expr_handle)
  ```
- **Line 75**: `rt_ast_expr_binary_left()`
  ```simple
  val left_handle = rt_ast_expr_binary_left(expr_handle)
  ```
- **Line 76**: `rt_ast_expr_binary_right()`
  ```simple
  val right_handle = rt_ast_expr_binary_right(expr_handle)
  ```
- **Line 82**: `rt_ast_expr_free()`
  ```simple
  rt_ast_expr_free(left_handle)
  ```
- **Line 83**: `rt_ast_expr_free()`
  ```simple
  rt_ast_expr_free(right_handle)
  ```
- **Line 88**: `rt_ast_expr_unary_op()`
  ```simple
  val op = rt_ast_expr_unary_op(expr_handle)
  ```
- **Line 89**: `rt_ast_expr_unary_operand()`
  ```simple
  val operand_handle = rt_ast_expr_unary_operand(expr_handle)
  ```
- **Line 91**: `rt_ast_expr_free()`
  ```simple
  rt_ast_expr_free(operand_handle)
  ```
- **Line 95**: `rt_error_semantic()`
  ```simple
  val err = rt_error_semantic("eval_expr_simple: unsupported expression tag: {tag}")
  ```
- **Line 96**: `rt_error_throw()`
  ```simple
  rt_error_throw(err)
  ```

#### `src/app/interpreter/memory/refc_binary.spl`

- **Line 596**: `rt_by()`
  ```simple
  self.free_blocks = self.free_blocks.sort_by(a, b: a.0 - b.0)
  ```

#### `src/app/lint/main.spl`

- **Line 559**: `rt_by()`
  ```simple
  all_replacements = all_replacements.sort_by(a, b: b.start - a.start)
  ```

#### `src/app/lsp/handlers/completion.spl`

- **Line 71**: `rt_text()`
  ```simple
  fn with_insert_text(text: String) -> CompletionItem:
  ```

#### `src/app/lsp/handlers/semantic_tokens.spl`

- **Line 151**: `rt_by()`
  ```simple
  tokens.sort_by(|a, b| {
  ```

#### `src/app/mcp/main.spl`

- **Line 110**: `rt_server()`
  ```simple
  fn start_server(debug_mode: Bool):
  ```
- **Line 61**: `rt_server()`
  ```simple
  start_server(debug_mode)
  ```

#### `src/app/package/all_ffi_test.spl`

- **Line 101**: `rt_package_create_tarball()`
  ```simple
  val create_tar_result = rt_package_create_tarball("/tmp/ffi-all-test", tarball_path)
  ```
- **Line 103**: `rt_package_file_size()`
  ```simple
  val tar_size = rt_package_file_size(tarball_path)
  ```
- **Line 113**: `rt_package_mkdir_all()`
  ```simple
  rt_package_mkdir_all(extract_dir)
  ```
- **Line 114**: `rt_package_extract_tarball()`
  ```simple
  val extract_result = rt_package_extract_tarball(tarball_path, extract_dir)
  ```
- **Line 124**: `rt_package_remove_dir_all()`
  ```simple
  val remove_result = rt_package_remove_dir_all("/tmp/ffi-all-test")
  ```
- **Line 126**: `rt_package_exists()`
  ```simple
  if rt_package_exists("/tmp/ffi-all-test") == 0
  ```
- **Line 137**: `rt_package_remove_dir_all()`
  ```simple
  rt_package_remove_dir_all(extract_dir)
  ```
- **Line 14**: `rt_package_exists()`
  ```simple
  val exists_result = rt_package_exists("/tmp")
  ```
- **Line 24**: `rt_package_is_dir()`
  ```simple
  val isdir_result = rt_package_is_dir("/tmp")
  ```
- **Line 36**: `rt_package_exists()`
  ```simple
  if rt_package_exists("/tmp/ffi-all-test") == 1
  ```
- **Line 37**: `rt_package_remove_dir_all()`
  ```simple
  rt_package_remove_dir_all("/tmp/ffi-all-test")
  ```
- **Line 38**: `rt_package_mkdir_all()`
  ```simple
  val mkdir_result = rt_package_mkdir_all(test_dir)
  ```
- **Line 48**: `rt_package_file_size()`
  ```simple
  val size = rt_package_file_size("/etc/passwd")
  ```
- **Line 59**: `rt_package_copy_file()`
  ```simple
  val copy_result = rt_package_copy_file("/etc/passwd", copy_dest)
  ```
- **Line 69**: `rt_package_chmod()`
  ```simple
  val chmod_result = rt_package_chmod(copy_dest, 0o644)
  ```
- **Line 90**: `rt_package_create_symlink()`
  ```simple
  val symlink_result = rt_package_create_symlink(copy_dest, link_path)
  ```

#### `src/app/package/direct_ffi_test.spl`

- **Line 7**: `rt_package_exists()`
  ```simple
  val result = rt_package_exists("/tmp")
  ```
- **Line 8**: `rt_package_exists()`
  ```simple
  print "rt_package_exists("/tmp") = " + result.to_string()
  ```

#### `src/app/package/lockfile.spl`

- **Line 15**: `rt_package_exists()`
  ```simple
  if rt_package_exists(path) == 0
  ```
- **Line 162**: `rt_file_write_text()`
  ```simple
  match rt_file_write_text(path, content)
  ```
- **Line 18**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text(path)
  ```
- **Line 221**: `rt_package_exists()`
  ```simple
  rt_package_exists(lockfile_path()) == 1
  ```
- **Line 227**: `rt_time_now_unix_micros()`
  ```simple
  val now_micros = rt_time_now_unix_micros()
  ```
- **Line 238**: `rt_timestamp_get_year()`
  ```simple
  val year = rt_timestamp_get_year(micros)
  ```
- **Line 239**: `rt_timestamp_get_month()`
  ```simple
  val month = rt_timestamp_get_month(micros)
  ```
- **Line 240**: `rt_timestamp_get_day()`
  ```simple
  val day = rt_timestamp_get_day(micros)
  ```
- **Line 241**: `rt_timestamp_get_hour()`
  ```simple
  val hour = rt_timestamp_get_hour(micros)
  ```
- **Line 242**: `rt_timestamp_get_minute()`
  ```simple
  val minute = rt_timestamp_get_minute(micros)
  ```
- **Line 243**: `rt_timestamp_get_second()`
  ```simple
  val second = rt_timestamp_get_second(micros)
  ```

#### `src/app/parser/core.spl`

- **Line 208**: `rt_stmt()`
  ```simple
  self.parse_import_stmt()
  ```
- **Line 214**: `rt_stmt()`
  ```simple
  self.parse_export_stmt()
  ```
- **Line 240**: `rt_stmt()`
  ```simple
  self.parse_assert_stmt()
  ```
- **Line 397**: `rt_stmt()`
  ```simple
  me parse_import_stmt() -> Result<Node, ParseError>
  ```
- **Line 403**: `rt_stmt()`
  ```simple
  me parse_export_stmt() -> Result<Node, ParseError>
  ```
- **Line 471**: `rt_stmt()`
  ```simple
  me parse_assert_stmt() -> Result<Node, ParseError>
  ```

#### `src/app/parser/definitions.spl`

- **Line 1405**: `rt_class()`
  ```simple
  elif self.is_method_start_class()
  ```
- **Line 1434**: `rt_class()`
  ```simple
  fn is_method_start_class(self) -> Bool
  ```

#### `src/app/parser/expressions.spl`

- **Line 1669**: `rt_argument()`
  ```simple
  elif self.is_callable_expr(expr) and self.can_start_argument()
  ```
- **Line 1714**: `rt_argument()`
  ```simple
  fn can_start_argument() -> bool
  ```
- **Line 1745**: `rt_argument()`
  ```simple
  if not self.can_start_argument() or match self.current.kind
  ```

#### `src/app/parser/modules.spl`

- **Line 125**: `rt_target()`
  ```simple
  val target = self.parse_import_target(None)
  ```
- **Line 139**: `rt_target()`
  ```simple
  val target = self.parse_import_target(None)
  ```
- **Line 149**: `rt_target()`
  ```simple
  val target = self.parse_import_target(Some(last))
  ```
- **Line 168**: `rt_body()`
  ```simple
  self.parse_use_or_import_body(start_span, is_type_only)
  ```
- **Line 190**: `rt_body()`
  ```simple
  self.parse_use_or_import_body(start_span, is_type_only)
  ```
- **Line 244**: `rt_body()`
  ```simple
  fn parse_use_or_import_body(self, start_span: Span, is_type_only: Bool) -> Result<Node, ParseError>:
  ```
- **Line 323**: `rt_use()`
  ```simple
  fn parse_export_use(self) -> Result<Node, ParseError>
  ```
- **Line 86**: `rt_target()`
  ```simple
  fn parse_import_target(self, last_segment: Option<String>) -> Result<ImportTarget, ParseError>:
  ```

#### `src/app/parser/statements.spl`

- **Line 1008**: `rt_statement()`
  ```simple
  fn parse_export_statement(self) -> Result<Node, ParseError>
  ```
- **Line 1019**: `rt_target()`
  ```simple
  target = Some(self.parse_import_target())
  ```
- **Line 1487**: `rt_block()`
  ```simple
  fn parse_lean_import_block(self) -> Result<Node, ParseError>
  ```
- **Line 679**: `rt_statement()`
  ```simple
  fn parse_assert_statement(self) -> Result<Node, ParseError>
  ```
- **Line 871**: `rt_target()`
  ```simple
  fn parse_import_target(self) -> ImportTarget
  ```
- **Line 913**: `rt_target()`
  ```simple
  target = Some(self.parse_import_target())
  ```
- **Line 925**: `rt_statement()`
  ```simple
  fn parse_import_statement(self) -> Result<Node, ParseError>
  ```
- **Line 934**: `rt_target()`
  ```simple
  target = Some(self.parse_import_target())
  ```
- **Line 952**: `rt_target()`
  ```simple
  val target = self.parse_import_target()
  ```
- **Line 996**: `rt_target()`
  ```simple
  target = Some(self.parse_import_target())
  ```

#### `src/app/release/install.spl`

- **Line 104**: `rt_dir_create()`
  ```simple
  rt_dir_create(parent, true)
  ```
- **Line 105**: `rt_file_copy()`
  ```simple
  rt_file_copy(file, dst_file)
  ```
- **Line 21**: `rt_env_cwd()`
  ```simple
  val script_dir = rt_env_cwd()
  ```
- **Line 31**: `rt_dir_create()`
  ```simple
  rt_dir_create(prefix + "/bin", true)
  ```
- **Line 32**: `rt_dir_create()`
  ```simple
  rt_dir_create(prefix + "/lib", true)
  ```
- **Line 33**: `rt_dir_create()`
  ```simple
  rt_dir_create(prefix + "/include", true)
  ```
- **Line 34**: `rt_dir_create()`
  ```simple
  rt_dir_create(prefix + "/share/simple/src", true)
  ```
- **Line 40**: `rt_file_exists()`
  ```simple
  if rt_file_exists(runtime_src)
  ```
- **Line 41**: `rt_file_copy()`
  ```simple
  rt_file_copy(runtime_src, runtime_dst)
  ```
- **Line 54**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(prefix + "/bin/simple", wrapper)
  ```
- **Line 60**: `rt_file_exists()`
  ```simple
  if rt_file_exists(lib_src)
  ```
- **Line 61**: `rt_file_copy()`
  ```simple
  rt_file_copy(lib_src, prefix + "/lib/libsimple_ffi_wrapper.so")
  ```
- **Line 67**: `rt_file_exists()`
  ```simple
  if rt_file_exists(header_src)
  ```
- **Line 68**: `rt_file_copy()`
  ```simple
  rt_file_copy(header_src, prefix + "/include/simple_ffi.h")
  ```
- **Line 95**: `rt_dir_create()`
  ```simple
  rt_dir_create(dst, true)
  ```
- **Line 96**: `rt_dir_walk()`
  ```simple
  val files = rt_dir_walk(src)
  ```

#### `src/app/release/package.spl`

- **Line 18**: `rt_env_cwd()`
  ```simple
  val root = rt_env_cwd()
  ```
- **Line 31**: `rt_dir_create()`
  ```simple
  rt_dir_create(release_dir, true)
  ```
- **Line 32**: `rt_dir_create()`
  ```simple
  rt_dir_create(pkg_dir, true)
  ```
- **Line 33**: `rt_dir_create()`
  ```simple
  rt_dir_create(pkg_dir + "/bin", true)
  ```
- **Line 34**: `rt_dir_create()`
  ```simple
  rt_dir_create(pkg_dir + "/lib", true)
  ```
- **Line 35**: `rt_dir_create()`
  ```simple
  rt_dir_create(pkg_dir + "/src", true)
  ```
- **Line 36**: `rt_dir_create()`
  ```simple
  rt_dir_create(pkg_dir + "/src/lib", true)
  ```
- **Line 37**: `rt_dir_create()`
  ```simple
  rt_dir_create(pkg_dir + "/src/app", true)
  ```
- **Line 43**: `rt_file_exists()`
  ```simple
  if rt_file_exists(runtime_src)
  ```
- **Line 44**: `rt_file_copy()`
  ```simple
  rt_file_copy(runtime_src, runtime_dst)
  ```
- **Line 49**: `rt_file_exists()`
  ```simple
  if rt_file_exists(main_runtime)
  ```
- **Line 50**: `rt_file_copy()`
  ```simple
  rt_file_copy(main_runtime, runtime_dst)
  ```
- **Line 59**: `rt_file_exists()`
  ```simple
  if rt_file_exists(ffi_lib)
  ```
- **Line 60**: `rt_file_copy()`
  ```simple
  rt_file_copy(ffi_lib, pkg_dir + "/lib/libsimple_ffi_wrapper.so")
  ```
- **Line 65**: `rt_file_exists()`
  ```simple
  if rt_file_exists(ffi_header)
  ```
- **Line 66**: `rt_dir_create()`
  ```simple
  rt_dir_create(pkg_dir + "/include", true)
  ```
- **Line 67**: `rt_file_copy()`
  ```simple
  rt_file_copy(ffi_header, pkg_dir + "/include/simple_ffi.h")
  ```

#### `src/app/test_runner_new/feature_db.spl`

- **Line 179**: `rt_features()`
  ```simple
  me sort_features()
  ```

#### `src/app/test_runner_new/test_db_core.spl`

- **Line 383**: `rt_run()`
  ```simple
  me start_run() -> text
  ```

#### `src/app/test_runner_new/test_db_validation.spl`

- **Line 222**: `rt_process_exists()`
  ```simple
  if not rt_process_exists(run.pid)
  ```

#### `src/app/test_runner_new/test_runner_main.spl`

- **Line 315**: `rt_run()`
  ```simple
  val run_id = db.start_run()
  ```

#### `src/compiler/aop.spl`

- **Line 350**: `rt_by()`
  ```simple
  matching.sort_by(a, b: a.order - b.order)
  ```
- **Line 432**: `rt_by()`
  ```simple
  matched = matched.sort_by(a, b
  ```

#### `src/compiler/backend/lean_backend.spl`

- **Line 310**: `rt_module()`
  ```simple
  fn export_module(module: MirModule) -> Result<LeanExportResult, CompileError>:
  ```
- **Line 322**: `rt_types()`
  ```simple
  self.export_types(builder, module)
  ```
- **Line 326**: `rt_function()`
  ```simple
  self.export_function(builder, name, body)
  ```
- **Line 343**: `rt_types()`
  ```simple
  fn export_types(builder: LeanBuilder, module: MirModule):
  ```
- **Line 350**: `rt_function()`
  ```simple
  fn export_function(builder: LeanBuilder, name: text, body: MirBody):
  ```

#### `src/compiler/backend/llvm_backend.spl`

- **Line 176**: `rt_function()`
  ```simple
  me start_function(name: text, params: [text], return_type: text):
  ```
- **Line 304**: `rt_function()`
  ```simple
  self.builder.start_function(name, params, ret_ty)
  ```

#### `src/compiler/backend/native_bridge.spl`

- **Line 19**: `rt_compile_to_native()`
  ```simple
  rt_compile_to_native(source_path, output_path)
  ```
- **Line 22**: `rt_execute_native()`
  ```simple
  rt_execute_native(binary_path, args, timeout_ms)
  ```
- **Line 25**: `rt_file_delete()`
  ```simple
  rt_file_delete(path)
  ```
- **Line 28**: `rt_time_now_unix_micros()`
  ```simple
  rt_time_now_unix_micros()
  ```

#### `src/compiler/borrow_check/mod.spl`

- **Line 106**: `rt_terminator()`
  ```simple
  block.set_terminator(self.convert_terminator(mir_block.terminator, block_id))
  ```
- **Line 118**: `rt_terminator()`
  ```simple
  fn convert_terminator(mir_term: MirTerminator, block_id: i64) -> Terminator:
  ```
- **Line 157**: `rt_place()`
  ```simple
  val mir_place = self.convert_place(place)
  ```
- **Line 179**: `rt_place()`
  ```simple
  fn convert_place(mir_place: MirPlace) -> Place:
  ```

#### `src/compiler/build_log.spl`

- **Line 104**: `rt_time_millis()`
  ```simple
  rt_time_millis()
  ```
- **Line 108**: `rt_time_millis()`
  ```simple
  val duration = rt_time_millis() - start_millis
  ```
- **Line 124**: `rt_env_var()`
  ```simple
  val working_dir = rt_env_var("PWD") ?? "."
  ```
- **Line 90**: `rt_time_now_iso()`
  ```simple
  BuildLogger(session_id: rt_uuid_v4(), start_time: rt_time_now_iso(),
  ```
- **Line 97**: `rt_phase()`
  ```simple
  me start_phase(name: text) -> i64:
  ```

#### `src/compiler/build_mode.spl`

- **Line 67**: `rt_time_now_iso()`
  ```simple
  rt_time_now_iso()
  ```

#### `src/compiler/codegen.spl`

- **Line 119**: `rt_cranelift_new_module()`
  ```simple
  rt_cranelift_new_module(name_ptr, name_len, target)
  ```
- **Line 122**: `rt_cranelift_new_aot_module()`
  ```simple
  rt_cranelift_new_aot_module(name_ptr, name_len, target)
  ```
- **Line 125**: `rt_cranelift_finalize_module()`
  ```simple
  rt_cranelift_finalize_module(module)
  ```
- **Line 128**: `rt_cranelift_free_module()`
  ```simple
  rt_cranelift_free_module(module)
  ```
- **Line 132**: `rt_cranelift_begin_function()`
  ```simple
  rt_cranelift_begin_function(module, name_ptr, name_len, sig)
  ```
- **Line 135**: `rt_cranelift_end_function()`
  ```simple
  rt_cranelift_end_function(ctx)
  ```
- **Line 138**: `rt_cranelift_define_function()`
  ```simple
  rt_cranelift_define_function(module, func_id, ctx)
  ```
- **Line 142**: `rt_cranelift_new_signature()`
  ```simple
  rt_cranelift_new_signature(call_conv)
  ```
- **Line 145**: `rt_cranelift_sig_add_param()`
  ```simple
  rt_cranelift_sig_add_param(sig, type_)
  ```
- **Line 148**: `rt_cranelift_sig_set_return()`
  ```simple
  rt_cranelift_sig_set_return(sig, type_)
  ```
- **Line 152**: `rt_cranelift_create_block()`
  ```simple
  rt_cranelift_create_block(ctx)
  ```
- **Line 155**: `rt_cranelift_switch_to_block()`
  ```simple
  rt_cranelift_switch_to_block(ctx, block)
  ```
- **Line 158**: `rt_cranelift_seal_block()`
  ```simple
  rt_cranelift_seal_block(ctx, block)
  ```
- **Line 161**: `rt_cranelift_seal_all_blocks()`
  ```simple
  rt_cranelift_seal_all_blocks(ctx)
  ```
- **Line 165**: `rt_cranelift_iconst()`
  ```simple
  rt_cranelift_iconst(ctx, type_, value)
  ```
- **Line 168**: `rt_cranelift_fconst()`
  ```simple
  rt_cranelift_fconst(ctx, type_, value)
  ```
- **Line 171**: `rt_cranelift_bconst()`
  ```simple
  rt_cranelift_bconst(ctx, value)
  ```
- **Line 174**: `rt_cranelift_null()`
  ```simple
  rt_cranelift_null(ctx, type_)
  ```
- **Line 178**: `rt_cranelift_iadd()`
  ```simple
  rt_cranelift_iadd(ctx, a, b)
  ```
- **Line 181**: `rt_cranelift_isub()`
  ```simple
  rt_cranelift_isub(ctx, a, b)
  ```
- **Line 184**: `rt_cranelift_imul()`
  ```simple
  rt_cranelift_imul(ctx, a, b)
  ```
- **Line 187**: `rt_cranelift_sdiv()`
  ```simple
  rt_cranelift_sdiv(ctx, a, b)
  ```
- **Line 190**: `rt_cranelift_udiv()`
  ```simple
  rt_cranelift_udiv(ctx, a, b)
  ```
- **Line 193**: `rt_cranelift_srem()`
  ```simple
  rt_cranelift_srem(ctx, a, b)
  ```
- **Line 196**: `rt_cranelift_urem()`
  ```simple
  rt_cranelift_urem(ctx, a, b)
  ```
- **Line 199**: `rt_cranelift_fadd()`
  ```simple
  rt_cranelift_fadd(ctx, a, b)
  ```
- **Line 202**: `rt_cranelift_fsub()`
  ```simple
  rt_cranelift_fsub(ctx, a, b)
  ```
- **Line 205**: `rt_cranelift_fmul()`
  ```simple
  rt_cranelift_fmul(ctx, a, b)
  ```
- **Line 208**: `rt_cranelift_fdiv()`
  ```simple
  rt_cranelift_fdiv(ctx, a, b)
  ```
- **Line 212**: `rt_cranelift_band()`
  ```simple
  rt_cranelift_band(ctx, a, b)
  ```
- **Line 215**: `rt_cranelift_bor()`
  ```simple
  rt_cranelift_bor(ctx, a, b)
  ```
- **Line 218**: `rt_cranelift_bxor()`
  ```simple
  rt_cranelift_bxor(ctx, a, b)
  ```
- **Line 221**: `rt_cranelift_bnot()`
  ```simple
  rt_cranelift_bnot(ctx, a)
  ```
- **Line 224**: `rt_cranelift_ishl()`
  ```simple
  rt_cranelift_ishl(ctx, a, b)
  ```
- **Line 227**: `rt_cranelift_sshr()`
  ```simple
  rt_cranelift_sshr(ctx, a, b)
  ```
- **Line 230**: `rt_cranelift_ushr()`
  ```simple
  rt_cranelift_ushr(ctx, a, b)
  ```
- **Line 234**: `rt_cranelift_icmp()`
  ```simple
  rt_cranelift_icmp(ctx, cond, a, b)
  ```
- **Line 237**: `rt_cranelift_fcmp()`
  ```simple
  rt_cranelift_fcmp(ctx, cond, a, b)
  ```
- **Line 241**: `rt_cranelift_load()`
  ```simple
  rt_cranelift_load(ctx, type_, addr, offset)
  ```
- **Line 244**: `rt_cranelift_store()`
  ```simple
  rt_cranelift_store(ctx, value, addr, offset)
  ```
- **Line 247**: `rt_cranelift_stack_slot()`
  ```simple
  rt_cranelift_stack_slot(ctx, size, align)
  ```
- **Line 250**: `rt_cranelift_stack_addr()`
  ```simple
  rt_cranelift_stack_addr(ctx, slot, offset)
  ```
- **Line 254**: `rt_cranelift_jump()`
  ```simple
  rt_cranelift_jump(ctx, block)
  ```
- **Line 257**: `rt_cranelift_brif()`
  ```simple
  rt_cranelift_brif(ctx, cond, then_block, else_block)
  ```
- **Line 260**: `rt_cranelift_return()`
  ```simple
  rt_cranelift_return(ctx, value)
  ```
- **Line 263**: `rt_cranelift_return_void()`
  ```simple
  rt_cranelift_return_void(ctx)
  ```
- **Line 266**: `rt_cranelift_trap()`
  ```simple
  rt_cranelift_trap(ctx, code)
  ```
- **Line 270**: `rt_cranelift_call()`
  ```simple
  rt_cranelift_call(ctx, func, args_ptr, args_len)
  ```
- **Line 273**: `rt_cranelift_call_indirect()`
  ```simple
  rt_cranelift_call_indirect(ctx, sig, addr, args_ptr, args_len)
  ```
- **Line 277**: `rt_cranelift_sextend()`
  ```simple
  rt_cranelift_sextend(ctx, to_type, value)
  ```
- **Line 280**: `rt_cranelift_uextend()`
  ```simple
  rt_cranelift_uextend(ctx, to_type, value)
  ```
- **Line 283**: `rt_cranelift_ireduce()`
  ```simple
  rt_cranelift_ireduce(ctx, to_type, value)
  ```
- **Line 286**: `rt_cranelift_fcvt_to_sint()`
  ```simple
  rt_cranelift_fcvt_to_sint(ctx, to_type, value)
  ```
- **Line 289**: `rt_cranelift_fcvt_to_uint()`
  ```simple
  rt_cranelift_fcvt_to_uint(ctx, to_type, value)
  ```
- **Line 292**: `rt_cranelift_fcvt_from_sint()`
  ```simple
  rt_cranelift_fcvt_from_sint(ctx, to_type, value)
  ```
- **Line 295**: `rt_cranelift_fcvt_from_uint()`
  ```simple
  rt_cranelift_fcvt_from_uint(ctx, to_type, value)
  ```
- **Line 298**: `rt_cranelift_bitcast()`
  ```simple
  rt_cranelift_bitcast(ctx, to_type, value)
  ```
- **Line 302**: `rt_cranelift_append_block_param()`
  ```simple
  rt_cranelift_append_block_param(ctx, block, type_)
  ```
- **Line 305**: `rt_cranelift_block_param()`
  ```simple
  rt_cranelift_block_param(ctx, block, index)
  ```
- **Line 309**: `rt_cranelift_get_function_ptr()`
  ```simple
  rt_cranelift_get_function_ptr(module, name_ptr, name_len)
  ```
- **Line 312**: `rt_cranelift_call_function_ptr()`
  ```simple
  rt_cranelift_call_function_ptr(ptr, args_ptr, args_len)
  ```
- **Line 316**: `rt_cranelift_emit_object()`
  ```simple
  rt_cranelift_emit_object(module, path)
  ```

#### `src/compiler/config.spl`

- **Line 104**: `rt_env_get()`
  ```simple
  val det_env = rt_env_get("SIMPLE_DETERMINISTIC")
  ```
- **Line 108**: `rt_env_get()`
  ```simple
  val cov_env = rt_env_get("SIMPLE_COVERAGE")
  ```
- **Line 180**: `rt_env_get()`
  ```simple
  val env_val = rt_env_get("SIMPLE_LOG")
  ```
- **Line 90**: `rt_env_get()`
  ```simple
  val profile_env = rt_env_get("SIMPLE_PROFILE")
  ```
- **Line 94**: `rt_env_get()`
  ```simple
  val log_env = rt_env_get("SIMPLE_LOG")
  ```

#### `src/compiler/dependency/graph.spl`

- **Line 153**: `rt_use()`
  ```simple
  me add_export_use(from: text, to: text):
  ```

#### `src/compiler/driver/incremental.spl`

- **Line 136**: `rt_file_exists()`
  ```simple
  if not rt_file_exists(cache_path)
  ```
- **Line 30**: `rt_file_exists()`
  ```simple
  if not rt_file_exists(path)
  ```
- **Line 33**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text(path)
  ```
- **Line 35**: `rt_file_size()`
  ```simple
  val size = rt_file_size(path)
  ```
- **Line 36**: `rt_file_modified()`
  ```simple
  val mtime = rt_file_modified(path)
  ```

#### `src/compiler/driver.spl`

- **Line 351**: `rt_shell()`
  ```simple
  val result = rt_shell("{simple_old} {source_file}")
  ```
- **Line 510**: `rt_file_read_bytes()`
  ```simple
  val bytes = rt_file_read_bytes(tmp_path)
  ```
- **Line 513**: `rt_file_delete()`
  ```simple
  rt_file_delete(tmp_path)
  ```
- **Line 524**: `rt_file_write_bytes()`
  ```simple
  if rt_file_write_bytes(output, smf_bytes)
  ```
- **Line 550**: `rt_shell()`
  ```simple
  val result = rt_shell(cmd)
  ```
- **Line 673**: `rt_env_get()`
  ```simple
  val env_path = rt_env_get("SIMPLE_RUNTIME_PATH")
  ```
- **Line 677**: `rt_file_exists()`
  ```simple
  if rt_file_exists("rust/target/debug/libsimple_compiler.so")
  ```
- **Line 679**: `rt_file_exists()`
  ```simple
  if rt_file_exists("rust/target/release/libsimple_compiler.so")
  ```
- **Line 689**: `rt_env_get()`
  ```simple
  val runtime_path = rt_env_get("SIMPLE_RUNTIME_PATH")
  ```
- **Line 692**: `rt_env_get()`
  ```simple
  val env_path = rt_env_get("SIMPLE_OLD_PATH")
  ```
- **Line 696**: `rt_file_exists()`
  ```simple
  if rt_file_exists("./rust/target/debug/simple_runtime")
  ```
- **Line 698**: `rt_file_exists()`
  ```simple
  if rt_file_exists("./rust/target/release/simple_runtime")
  ```
- **Line 700**: `rt_file_exists()`
  ```simple
  if rt_file_exists("./rust/target/debug/simple_old")
  ```
- **Line 702**: `rt_file_exists()`
  ```simple
  if rt_file_exists("./rust/target/release/simple_old")
  ```

#### `src/compiler/driver_types.spl`

- **Line 193**: `rt_file_read_text()`
  ```simple
  val content_opt = rt_file_read_text(path)
  ```

#### `src/compiler/ffi_minimal.spl`

- **Line 129**: `rt_gc_init()`
  ```simple
  rt_gc_init()
  ```
- **Line 132**: `rt_gc_malloc()`
  ```simple
  rt_gc_malloc(size)
  ```
- **Line 135**: `rt_gc_collect()`
  ```simple
  rt_gc_collect()
  ```
- **Line 139**: `rt_value_nil()`
  ```simple
  rt_value_nil()
  ```
- **Line 142**: `rt_value_bool()`
  ```simple
  rt_value_bool(value)
  ```
- **Line 145**: `rt_value_int()`
  ```simple
  rt_value_int(value)
  ```
- **Line 148**: `rt_value_float()`
  ```simple
  rt_value_float(value)
  ```
- **Line 151**: `rt_value_string()`
  ```simple
  rt_value_string(ptr, len)
  ```
- **Line 154**: `rt_value_array_new()`
  ```simple
  rt_value_array_new()
  ```
- **Line 157**: `rt_value_dict_new()`
  ```simple
  rt_value_dict_new()
  ```
- **Line 161**: `rt_value_type()`
  ```simple
  rt_value_type(value)
  ```
- **Line 164**: `rt_value_is_nil()`
  ```simple
  rt_value_is_nil(value)
  ```
- **Line 167**: `rt_value_is_bool()`
  ```simple
  rt_value_is_bool(value)
  ```
- **Line 170**: `rt_value_is_int()`
  ```simple
  rt_value_is_int(value)
  ```
- **Line 173**: `rt_value_is_float()`
  ```simple
  rt_value_is_float(value)
  ```
- **Line 176**: `rt_value_is_string()`
  ```simple
  rt_value_is_string(value)
  ```
- **Line 179**: `rt_value_is_array()`
  ```simple
  rt_value_is_array(value)
  ```
- **Line 182**: `rt_value_is_dict()`
  ```simple
  rt_value_is_dict(value)
  ```
- **Line 186**: `rt_value_as_bool()`
  ```simple
  rt_value_as_bool(value)
  ```
- **Line 189**: `rt_value_as_int()`
  ```simple
  rt_value_as_int(value)
  ```
- **Line 192**: `rt_value_as_float()`
  ```simple
  rt_value_as_float(value)
  ```
- **Line 195**: `rt_value_as_string()`
  ```simple
  rt_value_as_string(value, out_len)
  ```
- **Line 199**: `rt_value_add()`
  ```simple
  rt_value_add(left, right)
  ```
- **Line 202**: `rt_value_sub()`
  ```simple
  rt_value_sub(left, right)
  ```
- **Line 205**: `rt_value_mul()`
  ```simple
  rt_value_mul(left, right)
  ```
- **Line 208**: `rt_value_div()`
  ```simple
  rt_value_div(left, right)
  ```
- **Line 212**: `rt_value_eq()`
  ```simple
  rt_value_eq(left, right)
  ```
- **Line 215**: `rt_value_lt()`
  ```simple
  rt_value_lt(left, right)
  ```
- **Line 219**: `rt_value_print()`
  ```simple
  rt_value_print(value)
  ```
- **Line 222**: `rt_value_println()`
  ```simple
  rt_value_println(value)
  ```
- **Line 226**: `rt_value_free()`
  ```simple
  rt_value_free(value)
  ```
- **Line 229**: `rt_value_clone()`
  ```simple
  rt_value_clone(value)
  ```
- **Line 233**: `rt_file_exists()`
  ```simple
  rt_file_exists(path_ptr, path_len)
  ```
- **Line 236**: `rt_file_read_text()`
  ```simple
  rt_file_read_text(path_ptr, path_len)
  ```
- **Line 239**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(path_ptr, path_len, content_ptr, content_len)
  ```
- **Line 242**: `rt_file_delete()`
  ```simple
  rt_file_delete(path_ptr, path_len)
  ```
- **Line 245**: `rt_string_free()`
  ```simple
  rt_string_free(ptr)
  ```
- **Line 249**: `rt_env_get()`
  ```simple
  rt_env_get(name_ptr, name_len)
  ```
- **Line 252**: `rt_env_set()`
  ```simple
  rt_env_set(name_ptr, name_len, value_ptr, value_len)
  ```

#### `src/compiler/incremental_builder.spl`

- **Line 92**: `rt_hash_text()`
  ```simple
  SourceInfo(path: self.path, content_hash: rt_hash_text(content),
  ```

#### `src/compiler/incremental.spl`

- **Line 52**: `rt_hash_text()`
  ```simple
  val hash = FileHash(path: path, content_hash: rt_hash_text(content),
  ```
- **Line 53**: `rt_time_millis()`
  ```simple
  mtime_ms: rt_time_millis())
  ```

#### `src/compiler/layout_recorder.spl`

- **Line 139**: `rt_time_millis()`
  ```simple
  (rt_time_millis() - self.start_millis) * 1000
  ```
- **Line 152**: `rt_sdn()`
  ```simple
  fn export_sdn() -> text
  ```
- **Line 181**: `rt_recording()`
  ```simple
  fn start_recording()
  ```
- **Line 187**: `rt_layout_sdn()`
  ```simple
  fn export_layout_sdn() -> text
  ```
- **Line 189**: `rt_sdn()`
  ```simple
  _global_session.unwrap().export_sdn()
  ```
- **Line 71**: `rt_time_millis()`
  ```simple
  start_millis: rt_time_millis(),
  ```

#### `src/compiler/lexer.spl`

- **Line 110**: `rt_implicit_mul()`
  ```simple
  me maybe_insert_implicit_mul(token: Token) -> Token:
  ```
- **Line 166**: `rt_implicit_mul()`
  ```simple
  return self.maybe_insert_implicit_mul(token)
  ```

#### `src/compiler/macro_check/hygiene.spl`

- **Line 320**: `rt_expansion()`
  ```simple
  me start_expansion() -> SyntaxMark
  ```

#### `src/compiler/macro_check/mod.spl`

- **Line 212**: `rt_expansion()`
  ```simple
  val mark = self.hygiene.start_expansion()
  ```

#### `src/compiler/main.spl`

- **Line 103**: `rt_option()`
  ```simple
  match self.parse_short_option(arg, result)
  ```
- **Line 194**: `rt_option()`
  ```simple
  me parse_short_option(arg: text, result: CliArgs) -> Result<CliArgs, text>:
  ```
- **Line 342**: `rt_exec()`
  ```simple
  val exit_code = rt_exec("./target/debug/simple_old {last_arg}")
  ```
- **Line 429**: `rt_exec()`
  ```simple
  val step2_result = rt_exec("./simple-compiler-v1 -c -o simple-compiler-v2 simple/compiler/main.spl")
  ```
- **Line 437**: `rt_exec()`
  ```simple
  val step3_result = rt_exec("./simple-compiler-v2 -c -o simple-compiler-v3 simple/compiler/main.spl")
  ```
- **Line 445**: `rt_file_hash()`
  ```simple
  val v2_hash = rt_file_hash("simple-compiler-v2")
  ```
- **Line 446**: `rt_file_hash()`
  ```simple
  val v3_hash = rt_file_hash("simple-compiler-v3")
  ```

#### `src/compiler/mir_lowering.spl`

- **Line 886**: `rt_range()`
  ```simple
  Generates call to rt_range(start, end) or rt_range_inclusive(start, end).
  ```

#### `src/compiler/monomorphize/cache.spl`

- **Line 107**: `rt_time_millis()`
  ```simple
  last_access: rt_time_millis(), content_hash: content_hash)
  ```

#### `src/compiler/parallel.spl`

- **Line 22**: `rt_cpu_count()`
  ```simple
  ParallelConfig(max_threads: rt_cpu_count(), batch_size: 16)
  ```

#### `src/compiler/parser.spl`

- **Line 101**: `rt_struct()`
  ```simple
  val struct_ = self.convert_struct(struct_outline)
  ```
- **Line 106**: `rt_enum()`
  ```simple
  val enum_ = self.convert_enum(enum_outline)
  ```
- **Line 121**: `rt_type_alias()`
  ```simple
  val alias = self.convert_type_alias(alias_outline)
  ```
- **Line 1421**: `rt_type()`
  ```simple
  self.convert_type(outline)
  ```
- **Line 199**: `rt_type_list()`
  ```simple
  me convert_type_list(outlines: [TypeOutline]) -> [Type]:
  ```
- **Line 202**: `rt_type()`
  ```simple
  result = result.push(self.convert_type(outline))
  ```
- **Line 206**: `rt_field_list()`
  ```simple
  me convert_field_list(outlines: [FieldOutline]) -> [Field]:
  ```
- **Line 209**: `rt_field()`
  ```simple
  result = result.push(self.convert_field(outline))
  ```
- **Line 212**: `rt_import()`
  ```simple
  me convert_import(outline: ImportOutline) -> Import:
  ```
- **Line 223**: `rt_type()`
  ```simple
  me convert_type(outline: TypeOutline) -> Type:
  ```
- **Line 226**: `rt_type_list()`
  ```simple
  TypeKind.Named(name, self.convert_type_list(args))
  ```
- **Line 228**: `rt_type_list()`
  ```simple
  TypeKind.Tuple(self.convert_type_list(elements))
  ```
- **Line 230**: `rt_type()`
  ```simple
  TypeKind.Array(self.convert_type(element), nil)
  ```
- **Line 232**: `rt_type_list()`
  ```simple
  TypeKind.Function(self.convert_type_list(params), self.convert_type(ret))
  ```
- **Line 234**: `rt_type()`
  ```simple
  TypeKind.Optional(self.convert_type(inner))
  ```
- **Line 236**: `rt_type()`
  ```simple
  TypeKind.Reference(self.convert_type(inner), mutable)
  ```
- **Line 238**: `rt_type()`
  ```simple
  TypeKind.Atomic(self.convert_type(inner))
  ```
- **Line 240**: `rt_type()`
  ```simple
  TypeKind.Isolated(self.convert_type(inner))
  ```
- **Line 246**: `rt_type_param()`
  ```simple
  me convert_type_param(outline: TypeParamOutline) -> TypeParam:
  ```
- **Line 249**: `rt_type()`
  ```simple
  bounds = bounds.push(self.convert_type(b))
  ```
- **Line 254**: `rt_type()`
  ```simple
  default: outline.default.map(t: self.convert_type(t)),
  ```
- **Line 258**: `rt_param()`
  ```simple
  me convert_param(outline: ParamOutline) -> Param:
  ```
- **Line 263**: `rt_type()`
  ```simple
  val type_result = outline.type_.map(t: self.convert_type(t))
  ```
- **Line 271**: `rt_field()`
  ```simple
  me convert_field(outline: FieldOutline) -> Field:
  ```
- **Line 278**: `rt_type()`
  ```simple
  type_: self.convert_type(outline.type_),
  ```
- **Line 284**: `rt_struct()`
  ```simple
  me convert_struct(outline: StructOutline) -> Struct:
  ```
- **Line 287**: `rt_type_param()`
  ```simple
  type_params = type_params.push(self.convert_type_param(tp))
  ```
- **Line 291**: `rt_field()`
  ```simple
  fields = fields.push(self.convert_field(f))
  ```
- **Line 302**: `rt_enum()`
  ```simple
  me convert_enum(outline: EnumOutline) -> Enum:
  ```
- **Line 305**: `rt_type_param()`
  ```simple
  type_params = type_params.push(self.convert_type_param(tp))
  ```
- **Line 313**: `rt_type_list()`
  ```simple
  VariantKind.Tuple(self.convert_type_list(types))
  ```
- **Line 315**: `rt_field_list()`
  ```simple
  VariantKind.Struct(self.convert_field_list(fields))
  ```
- **Line 332**: `rt_type_alias()`
  ```simple
  me convert_type_alias(outline: TypeAliasOutline) -> TypeAlias:
  ```
- **Line 335**: `rt_type_param()`
  ```simple
  type_params = type_params.push(self.convert_type_param(tp))
  ```
- **Line 340**: `rt_type()`
  ```simple
  type_: self.convert_type(outline.type_),
  ```
- **Line 357**: `rt_param()`
  ```simple
  params = params.push(self.convert_param(p))
  ```
- **Line 368**: `rt_type()`
  ```simple
  return_type: outline.return_type.map(t: self.convert_type(t)),
  ```
- **Line 382**: `rt_type_param()`
  ```simple
  type_params = type_params.push(self.convert_type_param(tp))
  ```
- **Line 386**: `rt_field()`
  ```simple
  fields = fields.push(self.convert_field(f))
  ```
- **Line 406**: `rt_type_param()`
  ```simple
  type_params = type_params.push(self.convert_type_param(tp))
  ```
- **Line 429**: `rt_type()`
  ```simple
  type_: self.convert_type(outline.type_),
  ```
- **Line 430**: `rt_type()`
  ```simple
  trait_: outline.trait_.map(t: self.convert_type(t)),
  ```
- **Line 440**: `rt_type()`
  ```simple
  type_: outline.type_.map(t: self.convert_type(t)),
  ```
- **Line 75**: `rt_import()`
  ```simple
  module.imports = module.imports.push(self.convert_import(imp))
  ```

#### `src/compiler/project.spl`

- **Line 109**: `rt_file_exists()`
  ```simple
  if rt_file_exists(spl_path)
  ```
- **Line 114**: `rt_file_exists()`
  ```simple
  if rt_file_exists(init_path)
  ```
- **Line 122**: `rt_list_dir_recursive()`
  ```simple
  rt_list_dir_recursive(self.source_root, ".spl")
  ```
- **Line 64**: `rt_file_exists()`
  ```simple
  if rt_file_exists(sdn_path)
  ```
- **Line 66**: `rt_file_exists()`
  ```simple
  elif rt_file_exists(toml_path)
  ```
- **Line 73**: `rt_file_exists()`
  ```simple
  val source_root = if rt_file_exists("{root}/src"): "{root}/src" else: root
  ```

#### `src/compiler/simd_phase9c.spl`

- **Line 222**: `rt_ps()`
  ```simple
  static fn sse_sqrt_ps(a: Vec4f) -> Vec4f:
  ```

#### `src/compiler/test_bootstrap.spl`

- **Line 20**: `rt_cranelift_finalize_module()`
  ```simple
  rt_cranelift_finalize_module(module)
  ```
- **Line 66**: `rt_exec()`
  ```simple
  val result = rt_exec("echo 'Hello from rt_exec'")
  ```
- **Line 72**: `rt_file_hash()`
  ```simple
  val hash = rt_file_hash("/bin/sh")
  ```

#### `src/compiler/treesitter.spl`

- **Line 362**: `rt_items()`
  ```simple
  items = self.parse_import_items()
  ```
- **Line 384**: `rt_items()`
  ```simple
  me parse_import_items() -> [text]
  ```

#### `src/compiler/type_infer.spl`

- **Line 151**: `rt_hir_trait_to_def()`
  ```simple
  val trait_def = self.convert_hir_trait_to_def(hir_trait)
  ```
- **Line 160**: `rt_hir_impl_to_block()`
  ```simple
  val impl_block = self.convert_hir_impl_to_block(hir_impl)
  ```
- **Line 193**: `rt_hir_trait_to_def()`
  ```simple
  fn convert_hir_trait_to_def(hir_trait: HirTrait) -> TraitDef:
  ```
- **Line 232**: `rt_hir_impl_to_block()`
  ```simple
  fn convert_hir_impl_to_block(hir_impl: HirImpl) -> ImplBlock:
  ```

#### `src/compiler/type_system/builtin_registry.spl`

- **Line 20**: `rt_type_registry_lookup()`
  ```simple
  rt_type_registry_lookup(name)
  ```
- **Line 23**: `rt_type_registry_has()`
  ```simple
  rt_type_registry_has(name)
  ```

#### `src/lib/common/config_env.spl`

- **Line 53**: `rt_env_vars()`
  ```simple
  val vars = rt_env_vars()
  ```
- **Line 62**: `rt_env_vars()`
  ```simple
  val vars = rt_env_vars()
  ```

#### `src/lib/common/file_reader.spl`

- **Line 108**: `rt_file_size()`
  ```simple
  val size = rt_file_size(path)
  ```
- **Line 112**: `rt_file_mmap_read_bytes()`
  ```simple
  Ok(rt_file_mmap_read_bytes(path))
  ```
- **Line 114**: `rt_file_read_bytes()`
  ```simple
  Ok(rt_file_read_bytes(path))
  ```
- **Line 53**: `rt_file_mmap_read_text()`
  ```simple
  val content = rt_file_mmap_read_text(path)
  ```
- **Line 62**: `rt_file_mmap_read_bytes()`
  ```simple
  rt_file_mmap_read_bytes(self.path)
  ```
- **Line 88**: `rt_file_size()`
  ```simple
  val size = rt_file_size(path)
  ```
- **Line 92**: `rt_file_mmap_read_text()`
  ```simple
  val content = rt_file_mmap_read_text(path)
  ```
- **Line 97**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text(path)
  ```

#### `src/lib/common/fix_applicator.spl`

- **Line 107**: `rt_file_write_text()`
  ```simple
  val ok = rt_file_write_text(file, content)
  ```
- **Line 69**: `rt_by()`
  ```simple
  var sorted = replacements.sort_by(a, b: b.1.span.start - a.1.span.start)
  ```

#### `src/lib/common/target.spl`

- **Line 107**: `rt_host_os()`
  ```simple
  val os = rt_host_os()
  ```
- **Line 23**: `rt_host_arch()`
  ```simple
  val arch = rt_host_arch()
  ```

#### `src/lib/dependency_tracker/resolution.spl`

- **Line 116**: `rt_file_exists()`
  ```simple
  if rt_file_exists(file_path) and rt_file_exists(dir_path)
  ```
- **Line 97**: `rt_file_exists()`
  ```simple
  val file_exists = rt_file_exists(file_path)
  ```
- **Line 98**: `rt_file_exists()`
  ```simple
  val dir_exists = rt_file_exists(dir_path)
  ```

#### `src/lib/examples/testing/benchmark_example.spl`

- **Line 30**: `rt_impl()`
  ```simple
  fn quicksort_impl()
  ```
- **Line 34**: `rt_impl()`
  ```simple
  fn bubblesort_impl()
  ```

#### `src/lib/failsafe/mod.spl`

- **Line 66**: `rt_timeout()`
  ```simple
  val token = self.timeout_manager.start_timeout(operation_name)
  ```

#### `src/lib/failsafe/timeout.spl`

- **Line 110**: `rt_operation()`
  ```simple
  pub me start_operation()
  ```
- **Line 62**: `rt_timeout()`
  ```simple
  pub me start_timeout(operation_name: text) -> TimeoutToken:
  ```
- **Line 63**: `rt_timeout_ms()`
  ```simple
  return self.start_timeout_ms(operation_name, self.config.default_timeout_ms)
  ```
- **Line 65**: `rt_timeout_ms()`
  ```simple
  pub me start_timeout_ms(operation_name: text, timeout_ms: i64) -> TimeoutToken:
  ```

#### `src/lib/package_ffi.spl`

- **Line 103**: `rt_package_create_symlink()`
  ```simple
  rt_package_create_symlink(target, link_path) == 0
  ```
- **Line 115**: `rt_package_chmod()`
  ```simple
  rt_package_chmod(file_path, mode) == 0
  ```
- **Line 126**: `rt_package_exists()`
  ```simple
  rt_package_exists(path) == 1
  ```
- **Line 137**: `rt_package_is_dir()`
  ```simple
  rt_package_is_dir(path) == 1
  ```
- **Line 37**: `rt_package_create_tarball()`
  ```simple
  rt_package_create_tarball(source_dir, output_path) == 0
  ```
- **Line 49**: `rt_package_extract_tarball()`
  ```simple
  rt_package_extract_tarball(tarball_path, dest_dir) == 0
  ```
- **Line 57**: `rt_package_file_size()`
  ```simple
  rt_package_file_size(file_path)
  ```
- **Line 69**: `rt_package_copy_file()`
  ```simple
  rt_package_copy_file(src_path, dst_path) == 0
  ```
- **Line 80**: `rt_package_mkdir_all()`
  ```simple
  rt_package_mkdir_all(dir_path) == 0
  ```
- **Line 91**: `rt_package_remove_dir_all()`
  ```simple
  rt_package_remove_dir_all(dir_path) == 0
  ```

#### `src/lib/sdn/document.spl`

- **Line 123**: `rt_file_write_text()`
  ```simple
  val ok = rt_file_write_text(path, content)
  ```
- **Line 41**: `rt_file_read_text()`
  ```simple
  val source = rt_file_read_text(path)
  ```

#### `src/lib/sdn/parser.spl`

- **Line 580**: `rt_file_read_text()`
  ```simple
  val source = rt_file_read_text(path)
  ```

#### `src/lib/src/db.spl`

- **Line 158**: `rt_file_write()`
  ```simple
  rt_file_write(self.path, content)
  ```
- **Line 62**: `rt_file_read()`
  ```simple
  val content = rt_file_read(path)
  ```

#### `src/lib/src/exp/artifact.spl`

- **Line 106**: `rt_time_now_unix_micros()`
  ```simple
  timestamp: "{rt_time_now_unix_micros()}"
  ```
- **Line 158**: `rt_file_exists()`
  ```simple
  rt_file_exists(path)
  ```
- **Line 161**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(path, content)
  ```
- **Line 58**: `rt_time_now_unix_micros()`
  ```simple
  timestamp: "{rt_time_now_unix_micros()}"
  ```
- **Line 83**: `rt_time_now_unix_micros()`
  ```simple
  timestamp: "{rt_time_now_unix_micros()}"
  ```

#### `src/lib/src/exp/config.spl`

- **Line 404**: `rt_file_exists()`
  ```simple
  rt_file_exists(path)
  ```
- **Line 407**: `rt_file_read_text()`
  ```simple
  rt_file_read_text(path)
  ```
- **Line 414**: `rt_env_get()`
  ```simple
  val result = rt_env_get(key)
  ```

#### `src/lib/src/exp/run.spl`

- **Line 123**: `rt_time_now_unix_micros()`
  ```simple
  val event = Event(timestamp: "{rt_time_now_unix_micros()}", kind: "tag", data: data)
  ```
- **Line 131**: `rt_time_now_unix_micros()`
  ```simple
  val event = Event(timestamp: "{rt_time_now_unix_micros()}", kind: "note", data: data)
  ```
- **Line 156**: `rt_time_now_unix_micros()`
  ```simple
  val event = Event(timestamp: "{rt_time_now_unix_micros()}", kind: "fail", data: data)
  ```
- **Line 162**: `rt_time_now_unix_micros()`
  ```simple
  rt_time_now_unix_micros() - self.system_info.start_time_micros
  ```
- **Line 168**: `rt_run()`
  ```simple
  pub fn start_run(config: ExpConfig, tags: [text]) -> Run:
  ```
- **Line 277**: `rt_time_now_unix_micros()`
  ```simple
  meta["end_time"] = "{rt_time_now_unix_micros()}"
  ```
- **Line 289**: `rt_time_now_unix_micros()`
  ```simple
  val event = Event(timestamp: "{rt_time_now_unix_micros()}", kind: "end", data: data)
  ```
- **Line 297**: `rt_time_now_unix_micros()`
  ```simple
  val ts = "{rt_time_now_unix_micros()}"
  ```
- **Line 300**: `rt_time_now_unix_micros()`
  ```simple
  val micros = rt_time_now_unix_micros()
  ```
- **Line 305**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(path, content)
  ```
- **Line 58**: `rt_env_get()`
  ```simple
  val hostname = rt_env_get("HOSTNAME")
  ```
- **Line 59**: `rt_time_now_unix_micros()`
  ```simple
  val micros = rt_time_now_unix_micros()
  ```
- **Line 99**: `rt_time_now_unix_micros()`
  ```simple
  timestamp: "{rt_time_now_unix_micros()}"
  ```

#### `src/lib/src/exp/storage.spl`

- **Line 257**: `rt_dir_create()`
  ```simple
  rt_dir_create(path)
  ```
- **Line 260**: `rt_file_exists()`
  ```simple
  rt_file_exists(path)
  ```
- **Line 263**: `rt_file_read_text()`
  ```simple
  val raw = rt_file_read_text(path)
  ```
- **Line 267**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(path, content)
  ```
- **Line 270**: `rt_file_append_text()`
  ```simple
  rt_file_append_text(path, content)
  ```
- **Line 273**: `rt_file_delete()`
  ```simple
  rt_file_delete(path)
  ```
- **Line 276**: `rt_dir_list()`
  ```simple
  val raw = rt_dir_list(path)
  ```
- **Line 287**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(tmp_path, data)
  ```
- **Line 289**: `rt_file_delete()`
  ```simple
  rt_file_delete(tmp_path)
  ```

#### `src/lib/src/exp/sweep.spl`

- **Line 221**: `rt_time_now_unix_micros()`
  ```simple
  start_time_micros: rt_time_now_unix_micros()
  ```
- **Line 230**: `rt_time_now_unix_micros()`
  ```simple
  start_time_micros: rt_time_now_unix_micros()
  ```
- **Line 240**: `rt_time_now_unix_micros()`
  ```simple
  val elapsed = (rt_time_now_unix_micros() - self.start_time_micros) / 1000000
  ```
- **Line 52**: `rt_random_uniform()`
  ```simple
  val value = rt_random_uniform(low, high)
  ```
- **Line 58**: `rt_random_randint()`
  ```simple
  val value = rt_random_randint(low, high)
  ```
- **Line 64**: `rt_random_randint()`
  ```simple
  val idx = rt_random_randint(0, choices.len() - 1)
  ```

#### `src/lib/src/log.spl`

- **Line 43**: `rt_log_set_global_level()`
  ```simple
  rt_log_set_global_level(level)
  ```
- **Line 47**: `rt_log_set_scope_level()`
  ```simple
  rt_log_set_scope_level(scope.ptr(), scope.len(), level)
  ```
- **Line 51**: `rt_log_get_scope_level()`
  ```simple
  rt_log_get_scope_level(scope.ptr(), scope.len())
  ```
- **Line 55**: `rt_log_get_global_level()`
  ```simple
  rt_log_get_global_level()
  ```
- **Line 59**: `rt_log_is_enabled()`
  ```simple
  rt_log_is_enabled(level, scope.ptr(), scope.len()) != 0
  ```
- **Line 63**: `rt_log_clear_scope_levels()`
  ```simple
  rt_log_clear_scope_levels()
  ```
- **Line 71**: `rt_log_emit()`
  ```simple
  rt_log_emit(level, scope.ptr(), scope.len(), msg.ptr(), msg.len())
  ```

#### `src/lib/src/map.spl`

- **Line 319**: `rt_if_absent()`
  ```simple
  me insert_if_absent(self, key: K, value: V) -> bool:
  ```
- **Line 330**: `rt_if_absent()`
  ```simple
  if map.insert_if_absent("key", "value")
  ```

#### `src/lib/src/set.spl`

- **Line 74**: `rt_if_absent()`
  ```simple
  self.map.insert_if_absent(value, true)
  ```

#### `src/lib/src/table.spl`

- **Line 392**: `rt_by()`
  ```simple
  fn sort_by(column: text, ascending: bool = true) -> Table:
  ```

#### `src/lib/src/testing/helpers.spl`

- **Line 107**: `rt_ok()`
  ```simple
  val data = assert_ok(load_data(), "Data load should succeed")
  ```
- **Line 124**: `rt_err()`
  ```simple
  val error = assert_err(invalid_operation(), "Should fail")
  ```
- **Line 164**: `rt_fast()`
  ```simple
  val result = assert_fast(: query_db(), 1000, "Query too slow")
  ```
- **Line 180**: `rt_called()`
  ```simple
  pub fn assert_called(spy, times: i32):
  ```
- **Line 188**: `rt_called()`
  ```simple
  assert_called(save_mock, 3)
  ```
- **Line 194**: `rt_called_with()`
  ```simple
  pub fn assert_called_with(spy, args: List<text>):
  ```
- **Line 202**: `rt_called_with()`
  ```simple
  assert_called_with(save_mock, ["user123", "Alice"])
  ```
- **Line 207**: `rt_not_called()`
  ```simple
  pub fn assert_not_called(spy)
  ```
- **Line 20**: `rt_eq()`
  ```simple
  assert_eq(result, 42, "Result should be 42")
  ```
- **Line 214**: `rt_not_called()`
  ```simple
  assert_not_called(delete_mock)
  ```
- **Line 233**: `rt_contains()`
  ```simple
  assert_contains(users, "Alice", "Should contain Alice")
  ```
- **Line 247**: `rt_not_contains()`
  ```simple
  assert_not_contains(blocked_users, "Alice", "Should not be blocked")
  ```
- **Line 260**: `rt_empty()`
  ```simple
  assert_empty(errors, "Should have no errors")
  ```
- **Line 274**: `rt_len()`
  ```simple
  assert_len(results, 5, "Should have 5 results")
  ```
- **Line 34**: `rt_ne()`
  ```simple
  assert_ne(result, 0, "Result should not be zero")
  ```
- **Line 39**: `rt_true()`
  ```simple
  pub fn assert_true(condition: bool, message: text):
  ```
- **Line 47**: `rt_true()`
  ```simple
  assert_true(user.is_active(), "User should be active")
  ```
- **Line 52**: `rt_false()`
  ```simple
  pub fn assert_false(condition: bool, message: text):
  ```
- **Line 60**: `rt_false()`
  ```simple
  assert_false(user.is_deleted(), "User should not be deleted")
  ```
- **Line 76**: `rt_some()`
  ```simple
  val user = assert_some(find_user("id123"), "User should exist")
  ```
- **Line 90**: `rt_none()`
  ```simple
  assert_none(find_user("invalid"), "User should not exist")
  ```

#### `src/lib/src/testing/mocking_advanced.spl`

- **Line 403**: `rt_order()`
  ```simple
  fn get_start_order() -> List<text>
  ```
- **Line 502**: `rt_waiting()`
  ```simple
  self.try_start_waiting()
  ```
- **Line 504**: `rt_waiting()`
  ```simple
  me try_start_waiting()
  ```

#### `src/lib/src/testing/mocking_core.spl`

- **Line 541**: `rt_chain()`
  ```simple
  me start_chain(parent_id: i32, call: CallRecord) -> i32:
  ```

#### `src/lib/src/time.spl`

- **Line 114**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(millis)
  ```
- **Line 117**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(1)
  ```
- **Line 24**: `rt_time_now_unix_micros()`
  ```simple
  rt_time_now_unix_micros() as i64
  ```
- **Line 41**: `rt_time_now_unix_micros()`
  ```simple
  rt_time_now_unix_micros() as i64 * 1000
  ```
- **Line 53**: `rt_time_now_unix_micros()`
  ```simple
  rt_time_now_unix_micros() as i64 / 1000
  ```
- **Line 67**: `rt_time_now_unix_micros()`
  ```simple
  rt_time_now_unix_micros() as f64 / 1_000_000.0
  ```
- **Line 85**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(millis)
  ```
- **Line 97**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(milliseconds)
  ```

#### `src/lib/src/tooling/easy_fix/rules.spl`

- **Line 81**: `rt_offset()`
  ```simple
  fn line_start_offset(source: String, target_line: Int) -> Int:
  ```

#### `test/app/devtools_cli_spec.spl`

- **Line 13**: `rt_package_remove_dir_all()`
  ```simple
  rt_package_remove_dir_all(test_dir)
  ```
- **Line 26**: `rt_dir_create()`
  ```simple
  rt_dir_create(test_dir, true)
  ```
- **Line 31**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/a.spl", "fn hello():n    passn")
  ```
- **Line 32**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/b.spl", "fn hello():n    passn")
  ```
- **Line 33**: `rt_file_read_text()`
  ```simple
  val a = rt_file_read_text("{test_dir}/a.spl")
  ```
- **Line 34**: `rt_file_read_text()`
  ```simple
  val b = rt_file_read_text("{test_dir}/b.spl")
  ```
- **Line 38**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/a.spl", "fn hello():n    passn")
  ```
- **Line 39**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/b.spl", "fn hello():n    print "hello"n")
  ```
- **Line 40**: `rt_file_read_text()`
  ```simple
  val a = rt_file_read_text("{test_dir}/a.spl")
  ```
- **Line 41**: `rt_file_read_text()`
  ```simple
  val b = rt_file_read_text("{test_dir}/b.spl")
  ```
- **Line 47**: `rt_dir_create()`
  ```simple
  rt_dir_create(test_dir, true)
  ```
- **Line 53**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/test.spl", code)
  ```
- **Line 54**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text("{test_dir}/test.spl")
  ```
- **Line 59**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/test.spl", code)
  ```
- **Line 60**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text("{test_dir}/test.spl")
  ```
- **Line 69**: `rt_dir_create()`
  ```simple
  rt_dir_create("{test_dir}/src", true)
  ```
- **Line 70**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/simple.sdn", "package:n  name: testn  version: 0.1.0n")
  ```
- **Line 71**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/src/main.spl", "fn main():n    print "hello"n")
  ```
- **Line 76**: `rt_file_read_text()`
  ```simple
  val manifest = rt_file_read_text("{test_dir}/simple.sdn")
  ```
- **Line 80**: `rt_file_exists()`
  ```simple
  assert rt_file_exists("{test_dir}/src/main.spl")
  ```

#### `test/app/interpreter/ast/ast_convert_expr_spec.spl`

- **Line 48**: `rt_expression()`
  ```simple
  Validates convert_expression() handles all node types.
  ```

#### `test/app/package_cli_spec.spl`

- **Line 103**: `rt_file_read_text()`
  ```simple
  val manifest = rt_file_read_text("{test_dir}/simple.sdn")
  ```
- **Line 14**: `rt_dir_create()`
  ```simple
  rt_dir_create(test_dir, true)
  ```
- **Line 16**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/simple.sdn", manifest)
  ```
- **Line 19**: `rt_package_remove_dir_all()`
  ```simple
  rt_package_remove_dir_all(test_dir)
  ```
- **Line 29**: `rt_file_read_text()`
  ```simple
  val manifest = rt_file_read_text("{test_dir}/simple.sdn")
  ```
- **Line 33**: `rt_file_read_text()`
  ```simple
  val manifest = rt_file_read_text("{test_dir}/simple.sdn")
  ```
- **Line 47**: `rt_file_read_text()`
  ```simple
  val manifest = rt_file_read_text("{test_dir}/simple.sdn")
  ```
- **Line 62**: `rt_file_read_text()`
  ```simple
  val manifest = rt_file_read_text("{test_dir}/simple.sdn")
  ```
- **Line 76**: `rt_file_exists()`
  ```simple
  assert not rt_file_exists("{test_dir}/simple.lock")
  ```
- **Line 80**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/simple.lock", lock_content)
  ```
- **Line 81**: `rt_file_exists()`
  ```simple
  assert rt_file_exists("{test_dir}/simple.lock")
  ```
- **Line 98**: `rt_file_read_text()`
  ```simple
  val manifest = rt_file_read_text("{test_dir}/simple.sdn")
  ```

#### `test/app/package/package_spec.spl`

- **Line 234**: `rt_package_create_tarball()`
  ```simple
  val result = rt_package_create_tarball(source_dir, tarball_path)
  ```
- **Line 240**: `rt_package_extract_tarball()`
  ```simple
  val extract_result = rt_package_extract_tarball(tarball_path, extract_dir)
  ```
- **Line 271**: `rt_package_free_string()`
  ```simple
  rt_package_free_string(checksum)
  ```
- **Line 277**: `rt_package_file_size()`
  ```simple
  val size = rt_package_file_size(test_file)
  ```
- **Line 287**: `rt_package_remove_dir_all()`
  ```simple
  rt_package_remove_dir_all("/tmp/mkdir-test")
  ```
- **Line 290**: `rt_package_mkdir_all()`
  ```simple
  val result = rt_package_mkdir_all(test_dir)
  ```
- **Line 295**: `rt_package_remove_dir_all()`
  ```simple
  val remove_result = rt_package_remove_dir_all("/tmp/mkdir-test")
  ```
- **Line 313**: `rt_package_create_symlink()`
  ```simple
  val result = rt_package_create_symlink(target, link)
  ```
- **Line 329**: `rt_package_exists()`
  ```simple
  expect(rt_package_exists(existing)).to_equal(1)
  ```
- **Line 330**: `rt_package_exists()`
  ```simple
  expect(rt_package_exists(nonexistent)).to_equal(0)
  ```
- **Line 337**: `rt_package_is_dir()`
  ```simple
  expect(rt_package_is_dir(dir)).to_equal(1)
  ```
- **Line 338**: `rt_package_is_dir()`
  ```simple
  expect(rt_package_is_dir(file)).to_equal(0)
  ```

#### `test/app/project_cli_spec.spl`

- **Line 14**: `rt_package_remove_dir_all()`
  ```simple
  rt_package_remove_dir_all(test_dir)
  ```
- **Line 19**: `rt_dir_create()`
  ```simple
  rt_dir_create(test_dir, true)
  ```
- **Line 26**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/simple.sdn", manifest)
  ```
- **Line 27**: `rt_file_exists()`
  ```simple
  assert rt_file_exists("{test_dir}/simple.sdn")
  ```
- **Line 30**: `rt_dir_create()`
  ```simple
  rt_dir_create("{test_dir}/src", true)
  ```
- **Line 31**: `rt_package_is_dir()`
  ```simple
  assert rt_package_is_dir("{test_dir}/src") == 1
  ```
- **Line 34**: `rt_dir_create()`
  ```simple
  rt_dir_create("{test_dir}/test", true)
  ```
- **Line 35**: `rt_package_is_dir()`
  ```simple
  assert rt_package_is_dir("{test_dir}/test") == 1
  ```
- **Line 38**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/simple.sdn", "existing")
  ```
- **Line 39**: `rt_file_exists()`
  ```simple
  assert rt_file_exists("{test_dir}/simple.sdn")
  ```
- **Line 44**: `rt_dir_create()`
  ```simple
  rt_dir_create(test_dir, true)
  ```
- **Line 50**: `rt_dir_create()`
  ```simple
  rt_dir_create("{env_dir}/lib", true)
  ```
- **Line 51**: `rt_dir_create()`
  ```simple
  rt_dir_create("{env_dir}/bin", true)
  ```
- **Line 52**: `rt_dir_create()`
  ```simple
  rt_dir_create("{env_dir}/simple_modules", true)
  ```
- **Line 53**: `rt_package_is_dir()`
  ```simple
  assert rt_package_is_dir("{env_dir}/lib") == 1
  ```
- **Line 54**: `rt_package_is_dir()`
  ```simple
  assert rt_package_is_dir("{env_dir}/bin") == 1
  ```
- **Line 58**: `rt_dir_create()`
  ```simple
  rt_dir_create(env_dir, true)
  ```
- **Line 59**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{env_dir}/activate.sh", "export SIMPLE_ENV=testn")
  ```
- **Line 60**: `rt_file_exists()`
  ```simple
  assert rt_file_exists("{env_dir}/activate.sh")
  ```
- **Line 65**: `rt_dir_create()`
  ```simple
  rt_dir_create("{test_dir}/src", true)
  ```
- **Line 66**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/src/example.spl", "fn hello():n    print "hello"nnfn world():n    # TODO: implementn    passn")
  ```
- **Line 71**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text("{test_dir}/src/example.spl")
  ```
- **Line 76**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text("{test_dir}/src/example.spl")
  ```
- **Line 84**: `rt_dir_create()`
  ```simple
  rt_dir_create("{test_dir}/test", true)
  ```
- **Line 85**: `rt_file_write_text()`
  ```simple
  rt_file_write_text("{test_dir}/test/example_spec.spl", "describe "example":n    #[ignore]n    it "should work":n        assert truenn    #[ignore = "WIP"]n    it "should also work":n        assert truen")
  ```
- **Line 90**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text("{test_dir}/test/example_spec.spl")
  ```
- **Line 94**: `rt_file_read_text()`
  ```simple
  val content = rt_file_read_text("{test_dir}/test/example_spec.spl")
  ```

#### `test/app/spl_coverage_spec.spl`

- **Line 13**: `rt_coverage_dump_sdn()`
  ```simple
  val data = rt_coverage_dump_sdn()
  ```
- **Line 18**: `rt_coverage_dump_sdn()`
  ```simple
  val sdn_data = rt_coverage_dump_sdn()
  ```
- **Line 23**: `rt_coverage_dump_sdn()`
  ```simple
  val sdn_data = rt_coverage_dump_sdn()
  ```
- **Line 31**: `rt_coverage_clear()`
  ```simple
  rt_coverage_clear()
  ```
- **Line 34**: `rt_coverage_dump_sdn()`
  ```simple
  val data_after_clear = rt_coverage_dump_sdn()
  ```
- **Line 8**: `rt_coverage_enabled()`
  ```simple
  val enabled = rt_coverage_enabled()
  ```

#### `test/compiler/backend/native_bridge_spec.spl`

- **Line 136**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(source, "fn main(): print "test"")
  ```
- **Line 145**: `rt_file_delete()`
  ```simple
  rt_file_delete(source)
  ```
- **Line 153**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(source, "fn main(): ()")
  ```
- **Line 160**: `rt_file_delete()`
  ```simple
  rt_file_delete(source)
  ```
- **Line 222**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(binary_path, "fake binary content")
  ```
- **Line 226**: `rt_file_exists()`
  ```simple
  expect rt_file_exists(binary_path) == false
  ```
- **Line 270**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(source, program)
  ```
- **Line 288**: `rt_file_delete()`
  ```simple
  rt_file_delete(source)
  ```
- **Line 299**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(source, "invalid syntax {{{")
  ```
- **Line 307**: `rt_file_delete()`
  ```simple
  rt_file_delete(source)
  ```
- **Line 318**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(source, "fn main(): ()")
  ```
- **Line 326**: `rt_file_delete()`
  ```simple
  rt_file_delete(source)
  ```

#### `test/compiler/backend/native_ffi_spec.spl`

- **Line 106**: `rt_file_delete()`
  ```simple
  val result = rt_file_delete("/tmp/nonexistent_file_xyz")
  ```
- **Line 110**: `rt_file_delete()`
  ```simple
  val result = rt_file_delete("/tmp/nonexistent_file_12345_xyz")
  ```
- **Line 116**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(temp_path, "test content")
  ```
- **Line 119**: `rt_file_exists()`
  ```simple
  expect rt_file_exists(temp_path) == true
  ```
- **Line 122**: `rt_file_delete()`
  ```simple
  val result = rt_file_delete(temp_path)
  ```
- **Line 126**: `rt_file_exists()`
  ```simple
  expect rt_file_exists(temp_path) == false
  ```
- **Line 130**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(temp_path, "test")
  ```
- **Line 131**: `rt_file_delete()`
  ```simple
  rt_file_delete(temp_path)
  ```
- **Line 134**: `rt_file_delete()`
  ```simple
  val result = rt_file_delete(temp_path)
  ```
- **Line 138**: `rt_file_delete()`
  ```simple
  val result = rt_file_delete("")
  ```
- **Line 143**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(temp_path, "test")
  ```
- **Line 145**: `rt_file_delete()`
  ```simple
  val result = rt_file_delete(temp_path)
  ```
- **Line 163**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(source, program)
  ```
- **Line 166**: `rt_compile_to_native()`
  ```simple
  val (success, error) = rt_compile_to_native(source, binary)
  ```
- **Line 170**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native(binary, [], 5000)
  ```
- **Line 175**: `rt_file_delete()`
  ```simple
  rt_file_delete(binary)
  ```
- **Line 181**: `rt_file_delete()`
  ```simple
  rt_file_delete(source)
  ```
- **Line 188**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(temp1, "content1")
  ```
- **Line 189**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(temp2, "content2")
  ```
- **Line 192**: `rt_file_exists()`
  ```simple
  expect rt_file_exists(temp1) == true
  ```
- **Line 193**: `rt_file_exists()`
  ```simple
  expect rt_file_exists(temp2) == true
  ```
- **Line 196**: `rt_file_delete()`
  ```simple
  expect rt_file_delete(temp1) == true
  ```
- **Line 197**: `rt_file_delete()`
  ```simple
  expect rt_file_delete(temp2) == true
  ```
- **Line 200**: `rt_file_exists()`
  ```simple
  expect rt_file_exists(temp1) == false
  ```
- **Line 201**: `rt_file_exists()`
  ```simple
  expect rt_file_exists(temp2) == false
  ```
- **Line 209**: `rt_compile_to_native()`
  ```simple
  val (success, error) = rt_compile_to_native("test?.spl", "out")
  ```
- **Line 214**: `rt_compile_to_native()`
  ```simple
  val (success, error) = rt_compile_to_native(long_path, "out")
  ```
- **Line 219**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/echo", ["test"], 5000)
  ```
- **Line 224**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/sleep", ["10"], 0)
  ```
- **Line 229**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/true", [], -1)
  ```
- **Line 238**: `rt_time_now_unix_micros()`
  ```simple
  val start = rt_time_now_unix_micros()
  ```
- **Line 239**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/true", [], 5000)
  ```
- **Line 240**: `rt_time_now_unix_micros()`
  ```simple
  val end = rt_time_now_unix_micros()
  ```
- **Line 251**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/echo", ["test"], 5000)
  ```
- **Line 34**: `rt_compile_to_native()`
  ```simple
  val (success, error) = rt_compile_to_native("test.spl", "test.out")
  ```
- **Line 39**: `rt_compile_to_native()`
  ```simple
  val (success, error) = rt_compile_to_native("/nonexistent/file.spl", "out")
  ```
- **Line 44**: `rt_compile_to_native()`
  ```simple
  val (success, error) = rt_compile_to_native("", "")
  ```
- **Line 49**: `rt_compile_to_native()`
  ```simple
  val (success, error) = rt_compile_to_native("", "")
  ```
- **Line 54**: `rt_compile_to_native()`
  ```simple
  val (success, error) = rt_compile_to_native("/invalid/path/file.spl", "output")
  ```
- **Line 64**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/echo", ["hello"], 5000)
  ```
- **Line 69**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/nonexistent/binary", [], 5000)
  ```
- **Line 75**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/sleep", ["0.001"], 10)
  ```
- **Line 80**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/echo", ["arg1", "arg2"], 5000)
  ```
- **Line 87**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/sh", ["-c", "echo error >&2"], 5000)
  ```
- **Line 92**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/true", [], 5000)
  ```
- **Line 96**: `rt_execute_native()`
  ```simple
  val (stdout, stderr, code) = rt_execute_native("/bin/echo", ["test"], 3600000)  # 1 hour
  ```

#### `test/compiler/dependency/graph_basic_spec.spl`

- **Line 144**: `rt_use()`
  ```simple
  graph.add_export_use("a", "b")
  ```

#### `test/ffi_gen/e2e_build_test.spl`

- **Line 22**: `rt_env_cwd()`
  ```simple
  val cwd = rt_env_cwd()
  ```
- **Line 26**: `rt_file_exists()`
  ```simple
  if rt_file_exists(test_dir)
  ```
- **Line 27**: `rt_dir_remove()`
  ```simple
  rt_dir_remove(test_dir, true)
  ```
- **Line 30**: `rt_dir_create()`
  ```simple
  rt_dir_create(test_dir, true)
  ```
- **Line 31**: `rt_dir_create()`
  ```simple
  rt_dir_create("{test_dir}/src", true)
  ```
- **Line 44**: `rt_file_write_text()`
  ```simple
  assert rt_file_write_text("{test_dir}/Cargo.toml", cargo_toml), "Should write Cargo.toml"
  ```
- **Line 45**: `rt_file_write_text()`
  ```simple
  assert rt_file_write_text("{test_dir}/src/lib.rs", rust_code), "Should write lib.rs"
  ```
- **Line 58**: `rt_process_run()`
  ```simple
  val result = rt_process_run("cargo", ["build", "--release", "--manifest-path", "{test_dir}/Cargo.toml"])
  ```
- **Line 75**: `rt_file_exists()`
  ```simple
  if rt_file_exists(so_path) or rt_file_exists(dylib_path)
  ```
- **Line 84**: `rt_dir_remove()`
  ```simple
  rt_dir_remove(test_dir, true)
  ```

#### `test/lib/std/features/bootstrap_spec.spl`

- **Line 107**: `rt_read_file()`
  ```simple
  val source = rt_read_file(path).unwrap()
  ```
- **Line 240**: `rt_read_file()`
  ```simple
  val source = rt_read_file(path)
  ```
- **Line 36**: `rt_read_file()`
  ```simple
  val source = rt_read_file("src/compiler/lexer.spl").unwrap()
  ```
- **Line 59**: `rt_read_file()`
  ```simple
  val sources = compiler_files.map(f: (f, rt_read_file(f).unwrap()))
  ```
- **Line 79**: `rt_read_file()`
  ```simple
  val source = rt_read_file("src/compiler/parser.spl").unwrap()
  ```

#### `test/lib/std/features/experiment_tracking_spec.spl`

- **Line 136**: `rt_run()`
  ```simple
  var run_a = start_run(config_a, ["baseline"])
  ```
- **Line 140**: `rt_run()`
  ```simple
  var run_b = start_run(config_b, ["experiment"])
  ```
- **Line 54**: `rt_run()`
  ```simple
  var run = start_run(config, ["test", "integration"])
  ```
- **Line 69**: `rt_run()`
  ```simple
  var run = start_run(config, [])
  ```

#### `test/lib/std/features/resource_cleanup_spec.spl`

- **Line 172**: `rt_tracking()`
  ```simple
  it "auto-registers on _start_tracking()"
  ```
- **Line 398**: `rt_tracking()`
  ```simple
  r._start_tracking("TrackedMockResource.open("{name}")")
  ```

#### `test/lib/std/features/table_spec.spl`

- **Line 163**: `rt_by()`
  ```simple
  val sorted = t.sort_by("age")
  ```
- **Line 172**: `rt_by()`
  ```simple
  val sorted = t.sort_by("age", ascending: false)
  ```

#### `test/lib/std/integration/failsafe/crash_prevention_spec.spl`

- **Line 244**: `rt_timeout()`
  ```simple
  val token = manager.start_timeout("slow_op")
  ```
- **Line 268**: `rt_timeout()`
  ```simple
  val token = manager.start_timeout("op")
  ```
- **Line 287**: `rt_timeout_ms()`
  ```simple
  manager.start_timeout_ms("op", 0)
  ```
- **Line 296**: `rt_operation()`
  ```simple
  deadline.start_operation()
  ```

#### `test/lib/std/unit/cli/cli_codegen_spec.spl`

- **Line 14**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/gen_lean/main.spl")
  ```
- **Line 18**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/feature_gen/main.spl")
  ```
- **Line 22**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/task_gen/main.spl")
  ```
- **Line 26**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/spec_gen/main.spl")
  ```
- **Line 30**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/todo_scan/main.spl")
  ```
- **Line 34**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/todo_gen/main.spl")
  ```

#### `test/lib/std/unit/cli/cli_info_spec.spl`

- **Line 14**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/targets/main.spl")
  ```
- **Line 18**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/linkers/main.spl")
  ```
- **Line 22**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/info/main.spl")
  ```
- **Line 26**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/env/main.spl")
  ```
- **Line 30**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/brief/main.spl")
  ```

#### `test/lib/std/unit/cli/cli_migration_spec.spl`

- **Line 14**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/src/i18n/main.spl")
  ```
- **Line 18**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/migrate/main.spl")
  ```
- **Line 22**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/lock/main.spl")
  ```
- **Line 26**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/qualify_ignore/main.spl")
  ```
- **Line 30**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/diagram/main.spl")
  ```

#### `test/lib/std/unit/cli/cli_misc_spec.spl`

- **Line 14**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/watch/main.spl")
  ```
- **Line 18**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/web/main.spl")
  ```
- **Line 22**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/run/main.spl")
  ```

#### `test/lib/std/unit/cli/cli_pkg_spec.spl`

- **Line 14**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/init/main.spl")
  ```
- **Line 18**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/add/main.spl")
  ```
- **Line 22**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/remove/main.spl")
  ```
- **Line 26**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/install/main.spl")
  ```
- **Line 30**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/update/main.spl")
  ```
- **Line 34**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/list/main.spl")
  ```
- **Line 38**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/tree/main.spl")
  ```
- **Line 42**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/cache/main.spl")
  ```

#### `test/lib/std/unit/cli/cli_validation_spec.spl`

- **Line 14**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/check/main.spl")
  ```
- **Line 18**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/compile/main.spl")
  ```
- **Line 22**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/diff/main.spl")
  ```
- **Line 26**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/constr/main.spl")
  ```
- **Line 30**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/query/main.spl")
  ```
- **Line 34**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/spec_coverage/main.spl")
  ```
- **Line 38**: `rt_file_exists_str()`
  ```simple
  expect rt_file_exists_str("src/app/replay/main.spl")
  ```

#### `test/lib/std/unit/concurrency/concurrency_spec.spl`

- **Line 31**: `rt_channel_send()`
  ```simple
  rt_channel_send(self._id, value)
  ```
- **Line 34**: `rt_channel_try_recv()`
  ```simple
  return rt_channel_try_recv(self._id)
  ```
- **Line 354**: `rt_channel_new()`
  ```simple
  val ch_id = rt_channel_new()
  ```
- **Line 357**: `rt_channel_send()`
  ```simple
  rt_channel_send(channel_id, data)
  ```
- **Line 359**: `rt_channel_recv()`
  ```simple
  val result = rt_channel_recv(ch_id)
  ```
- **Line 37**: `rt_channel_recv()`
  ```simple
  return rt_channel_recv(self._id)
  ```
- **Line 40**: `rt_channel_close()`
  ```simple
  rt_channel_close(self._id)
  ```
- **Line 43**: `rt_channel_is_closed()`
  ```simple
  return rt_channel_is_closed(self._id) == 1
  ```
- **Line 49**: `rt_thread_join()`
  ```simple
  return rt_thread_join(self._handle)
  ```
- **Line 52**: `rt_channel_new()`
  ```simple
  val id = rt_channel_new()
  ```
- **Line 56**: `rt_thread_available_parallelism()`
  ```simple
  return rt_thread_available_parallelism()
  ```
- **Line 59**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(millis)
  ```
- **Line 62**: `rt_thread_yield()`
  ```simple
  rt_thread_yield()
  ```
- **Line 69**: `rt_time_now_seconds()`
  ```simple
  return rt_time_now_seconds()
  ```

#### `test/lib/std/unit/concurrency/concurrent_providers_spec.spl`

- **Line 110**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 111**: `rt_hashmap_len()`
  ```simple
  expect __rt_hashmap_len(h) == 0
  ```
- **Line 114**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 115**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "key1", 42)
  ```
- **Line 116**: `rt_hashmap_get()`
  ```simple
  expect __rt_hashmap_get(h, "key1") == 42
  ```
- **Line 119**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 120**: `rt_hashmap_get()`
  ```simple
  expect __rt_hashmap_get(h, "nope") == nil
  ```
- **Line 123**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 124**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "x", 1)
  ```
- **Line 125**: `rt_hashmap_contains_key()`
  ```simple
  expect __rt_hashmap_contains_key(h, "x") == true
  ```
- **Line 126**: `rt_hashmap_contains_key()`
  ```simple
  expect __rt_hashmap_contains_key(h, "y") == false
  ```
- **Line 129**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 130**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "rm", 99)
  ```
- **Line 131**: `rt_hashmap_remove()`
  ```simple
  val removed = __rt_hashmap_remove(h, "rm")
  ```
- **Line 133**: `rt_hashmap_contains_key()`
  ```simple
  expect __rt_hashmap_contains_key(h, "rm") == false
  ```
- **Line 136**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 137**: `rt_hashmap_remove()`
  ```simple
  expect __rt_hashmap_remove(h, "missing") == nil
  ```
- **Line 140**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 141**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "a", 1)
  ```
- **Line 142**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "b", 2)
  ```
- **Line 143**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "c", 3)
  ```
- **Line 144**: `rt_hashmap_len()`
  ```simple
  expect __rt_hashmap_len(h) == 3
  ```
- **Line 147**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 148**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "a", 1)
  ```
- **Line 149**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "b", 2)
  ```
- **Line 150**: `rt_hashmap_clear()`
  ```simple
  __rt_hashmap_clear(h)
  ```
- **Line 151**: `rt_hashmap_len()`
  ```simple
  expect __rt_hashmap_len(h) == 0
  ```
- **Line 154**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 155**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "alpha", 1)
  ```
- **Line 156**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "beta", 2)
  ```
- **Line 157**: `rt_hashmap_keys()`
  ```simple
  val keys = __rt_hashmap_keys(h)
  ```
- **Line 15**: `rt_hashmap_new()`
  ```simple
  extern fn __rt_hashmap_new() -> i64
  ```
- **Line 161**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 162**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "x", 10)
  ```
- **Line 163**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "y", 20)
  ```
- **Line 164**: `rt_hashmap_values()`
  ```simple
  val vals = __rt_hashmap_values(h)
  ```
- **Line 168**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 169**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "k", 99)
  ```
- **Line 16**: `rt_hashmap_insert()`
  ```simple
  extern fn __rt_hashmap_insert(handle: i64, key: text, value: Any) -> bool
  ```
- **Line 170**: `rt_hashmap_entries()`
  ```simple
  val entries = __rt_hashmap_entries(h)
  ```
- **Line 174**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 175**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "dup", 1)
  ```
- **Line 176**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "dup", 2)
  ```
- **Line 177**: `rt_hashmap_get()`
  ```simple
  expect __rt_hashmap_get(h, "dup") == 2
  ```
- **Line 178**: `rt_hashmap_len()`
  ```simple
  expect __rt_hashmap_len(h) == 1
  ```
- **Line 17**: `rt_hashmap_get()`
  ```simple
  extern fn __rt_hashmap_get(handle: i64, key: text) -> Any
  ```
- **Line 181**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 182**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "greeting", "hello")
  ```
- **Line 183**: `rt_hashmap_get()`
  ```simple
  expect __rt_hashmap_get(h, "greeting") == "hello"
  ```
- **Line 186**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 189**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "key_{i}", i)
  ```
- **Line 18**: `rt_hashmap_contains_key()`
  ```simple
  extern fn __rt_hashmap_contains_key(handle: i64, key: text) -> bool
  ```
- **Line 191**: `rt_hashmap_len()`
  ```simple
  expect __rt_hashmap_len(h) == 100
  ```
- **Line 194**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 195**: `rt_hashmap_insert()`
  ```simple
  val result = __rt_hashmap_insert(h, "new", 1)
  ```
- **Line 199**: `rt_hashmap_new()`
  ```simple
  val h = __rt_hashmap_new()
  ```
- **Line 19**: `rt_hashmap_remove()`
  ```simple
  extern fn __rt_hashmap_remove(handle: i64, key: text) -> Any
  ```
- **Line 200**: `rt_hashmap_insert()`
  ```simple
  __rt_hashmap_insert(h, "dup", 1)
  ```
- **Line 201**: `rt_hashmap_insert()`
  ```simple
  val result = __rt_hashmap_insert(h, "dup", 2)
  ```
- **Line 209**: `rt_hashset_new()`
  ```simple
  val s = __rt_hashset_new()
  ```
- **Line 20**: `rt_hashmap_len()`
  ```simple
  extern fn __rt_hashmap_len(handle: i64) -> i64
  ```
- **Line 210**: `rt_hashset_len()`
  ```simple
  expect __rt_hashset_len(s) == 0
  ```
- **Line 213**: `rt_hashset_new()`
  ```simple
  val s = __rt_hashset_new()
  ```
- **Line 214**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "apple")
  ```
- **Line 215**: `rt_hashset_contains()`
  ```simple
  expect __rt_hashset_contains(s, "apple") == true
  ```
- **Line 216**: `rt_hashset_contains()`
  ```simple
  expect __rt_hashset_contains(s, "banana") == false
  ```
- **Line 219**: `rt_hashset_new()`
  ```simple
  val s = __rt_hashset_new()
  ```
- **Line 21**: `rt_hashmap_clear()`
  ```simple
  extern fn __rt_hashmap_clear(handle: i64) -> bool
  ```
- **Line 220**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "x")
  ```
- **Line 221**: `rt_hashset_remove()`
  ```simple
  expect __rt_hashset_remove(s, "x") == true
  ```
- **Line 222**: `rt_hashset_contains()`
  ```simple
  expect __rt_hashset_contains(s, "x") == false
  ```
- **Line 225**: `rt_hashset_new()`
  ```simple
  val s = __rt_hashset_new()
  ```
- **Line 226**: `rt_hashset_remove()`
  ```simple
  expect __rt_hashset_remove(s, "nope") == false
  ```
- **Line 229**: `rt_hashset_new()`
  ```simple
  val s = __rt_hashset_new()
  ```
- **Line 22**: `rt_hashmap_keys()`
  ```simple
  extern fn __rt_hashmap_keys(handle: i64) -> Any
  ```
- **Line 230**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "a")
  ```
- **Line 231**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "b")
  ```
- **Line 232**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "c")
  ```
- **Line 233**: `rt_hashset_len()`
  ```simple
  expect __rt_hashset_len(s) == 3
  ```
- **Line 236**: `rt_hashset_new()`
  ```simple
  val s = __rt_hashset_new()
  ```
- **Line 237**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "x")
  ```
- **Line 238**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "y")
  ```
- **Line 239**: `rt_hashset_clear()`
  ```simple
  __rt_hashset_clear(s)
  ```
- **Line 23**: `rt_hashmap_values()`
  ```simple
  extern fn __rt_hashmap_values(handle: i64) -> Any
  ```
- **Line 240**: `rt_hashset_len()`
  ```simple
  expect __rt_hashset_len(s) == 0
  ```
- **Line 243**: `rt_hashset_new()`
  ```simple
  val s = __rt_hashset_new()
  ```
- **Line 244**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "one")
  ```
- **Line 245**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(s, "two")
  ```
- **Line 246**: `rt_hashset_to_array()`
  ```simple
  val arr = __rt_hashset_to_array(s)
  ```
- **Line 24**: `rt_hashmap_entries()`
  ```simple
  extern fn __rt_hashmap_entries(handle: i64) -> Any
  ```
- **Line 250**: `rt_hashset_new()`
  ```simple
  val a = __rt_hashset_new()
  ```
- **Line 251**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "1")
  ```
- **Line 252**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "2")
  ```
- **Line 253**: `rt_hashset_new()`
  ```simple
  val b = __rt_hashset_new()
  ```
- **Line 254**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "2")
  ```
- **Line 255**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "3")
  ```
- **Line 256**: `rt_hashset_union()`
  ```simple
  val u = __rt_hashset_union(a, b)
  ```
- **Line 257**: `rt_hashset_len()`
  ```simple
  expect __rt_hashset_len(u) == 3
  ```
- **Line 260**: `rt_hashset_new()`
  ```simple
  val a = __rt_hashset_new()
  ```
- **Line 261**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "1")
  ```
- **Line 262**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "2")
  ```
- **Line 263**: `rt_hashset_new()`
  ```simple
  val b = __rt_hashset_new()
  ```
- **Line 264**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "2")
  ```
- **Line 265**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "3")
  ```
- **Line 266**: `rt_hashset_intersection()`
  ```simple
  val inter = __rt_hashset_intersection(a, b)
  ```
- **Line 267**: `rt_hashset_len()`
  ```simple
  expect __rt_hashset_len(inter) == 1
  ```
- **Line 270**: `rt_hashset_new()`
  ```simple
  val a = __rt_hashset_new()
  ```
- **Line 271**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "1")
  ```
- **Line 272**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "2")
  ```
- **Line 273**: `rt_hashset_new()`
  ```simple
  val b = __rt_hashset_new()
  ```
- **Line 274**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "2")
  ```
- **Line 275**: `rt_hashset_difference()`
  ```simple
  val d = __rt_hashset_difference(a, b)
  ```
- **Line 276**: `rt_hashset_len()`
  ```simple
  expect __rt_hashset_len(d) == 1
  ```
- **Line 277**: `rt_hashset_contains()`
  ```simple
  expect __rt_hashset_contains(d, "1") == true
  ```
- **Line 27**: `rt_hashset_new()`
  ```simple
  extern fn __rt_hashset_new() -> i64
  ```
- **Line 280**: `rt_hashset_new()`
  ```simple
  val a = __rt_hashset_new()
  ```
- **Line 281**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "1")
  ```
- **Line 282**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "2")
  ```
- **Line 283**: `rt_hashset_new()`
  ```simple
  val b = __rt_hashset_new()
  ```
- **Line 284**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "2")
  ```
- **Line 285**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "3")
  ```
- **Line 286**: `rt_hashset_symmetric_difference()`
  ```simple
  val sd = __rt_hashset_symmetric_difference(a, b)
  ```
- **Line 287**: `rt_hashset_len()`
  ```simple
  expect __rt_hashset_len(sd) == 2
  ```
- **Line 28**: `rt_hashset_insert()`
  ```simple
  extern fn __rt_hashset_insert(handle: i64, value: text) -> bool
  ```
- **Line 290**: `rt_hashset_new()`
  ```simple
  val a = __rt_hashset_new()
  ```
- **Line 291**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "1")
  ```
- **Line 292**: `rt_hashset_new()`
  ```simple
  val b = __rt_hashset_new()
  ```
- **Line 293**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "1")
  ```
- **Line 294**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "2")
  ```
- **Line 295**: `rt_hashset_is_subset()`
  ```simple
  expect __rt_hashset_is_subset(a, b) == true
  ```
- **Line 296**: `rt_hashset_is_subset()`
  ```simple
  expect __rt_hashset_is_subset(b, a) == false
  ```
- **Line 299**: `rt_hashset_new()`
  ```simple
  val a = __rt_hashset_new()
  ```
- **Line 29**: `rt_hashset_contains()`
  ```simple
  extern fn __rt_hashset_contains(handle: i64, value: text) -> bool
  ```
- **Line 300**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "1")
  ```
- **Line 301**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(a, "2")
  ```
- **Line 302**: `rt_hashset_new()`
  ```simple
  val b = __rt_hashset_new()
  ```
- **Line 303**: `rt_hashset_insert()`
  ```simple
  __rt_hashset_insert(b, "1")
  ```
- **Line 304**: `rt_hashset_is_superset()`
  ```simple
  expect __rt_hashset_is_superset(a, b) == true
  ```
- **Line 30**: `rt_hashset_remove()`
  ```simple
  extern fn __rt_hashset_remove(handle: i64, value: text) -> bool
  ```
- **Line 311**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 312**: `rt_btreemap_len()`
  ```simple
  expect __rt_btreemap_len(m) == 0
  ```
- **Line 315**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 316**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "key", 42)
  ```
- **Line 317**: `rt_btreemap_get()`
  ```simple
  expect __rt_btreemap_get(m, "key") == 42
  ```
- **Line 31**: `rt_hashset_len()`
  ```simple
  extern fn __rt_hashset_len(handle: i64) -> i64
  ```
- **Line 320**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 321**: `rt_btreemap_get()`
  ```simple
  expect __rt_btreemap_get(m, "nope") == nil
  ```
- **Line 324**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 325**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "x", 1)
  ```
- **Line 326**: `rt_btreemap_contains_key()`
  ```simple
  expect __rt_btreemap_contains_key(m, "x") == true
  ```
- **Line 327**: `rt_btreemap_contains_key()`
  ```simple
  expect __rt_btreemap_contains_key(m, "y") == false
  ```
- **Line 32**: `rt_hashset_clear()`
  ```simple
  extern fn __rt_hashset_clear(handle: i64) -> bool
  ```
- **Line 330**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 331**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "rm", 5)
  ```
- **Line 332**: `rt_btreemap_remove()`
  ```simple
  expect __rt_btreemap_remove(m, "rm") == 5
  ```
- **Line 333**: `rt_btreemap_len()`
  ```simple
  expect __rt_btreemap_len(m) == 0
  ```
- **Line 336**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 337**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "a", 1)
  ```
- **Line 338**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "b", 2)
  ```
- **Line 339**: `rt_btreemap_len()`
  ```simple
  expect __rt_btreemap_len(m) == 2
  ```
- **Line 33**: `rt_hashset_to_array()`
  ```simple
  extern fn __rt_hashset_to_array(handle: i64) -> Any
  ```
- **Line 342**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 343**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "a", 1)
  ```
- **Line 344**: `rt_btreemap_clear()`
  ```simple
  __rt_btreemap_clear(m)
  ```
- **Line 345**: `rt_btreemap_len()`
  ```simple
  expect __rt_btreemap_len(m) == 0
  ```
- **Line 348**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 349**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "c", 3)
  ```
- **Line 34**: `rt_hashset_union()`
  ```simple
  extern fn __rt_hashset_union(a: i64, b: i64) -> i64
  ```
- **Line 350**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "a", 1)
  ```
- **Line 351**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "b", 2)
  ```
- **Line 352**: `rt_btreemap_keys()`
  ```simple
  val keys = __rt_btreemap_keys(m)
  ```
- **Line 358**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 359**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "b", 20)
  ```
- **Line 35**: `rt_hashset_intersection()`
  ```simple
  extern fn __rt_hashset_intersection(a: i64, b: i64) -> i64
  ```
- **Line 360**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "a", 10)
  ```
- **Line 361**: `rt_btreemap_values()`
  ```simple
  val vals = __rt_btreemap_values(m)
  ```
- **Line 366**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 367**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "b", 2)
  ```
- **Line 368**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "a", 1)
  ```
- **Line 369**: `rt_btreemap_entries()`
  ```simple
  val entries = __rt_btreemap_entries(m)
  ```
- **Line 36**: `rt_hashset_difference()`
  ```simple
  extern fn __rt_hashset_difference(a: i64, b: i64) -> i64
  ```
- **Line 373**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 374**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "z", 26)
  ```
- **Line 375**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "a", 1)
  ```
- **Line 376**: `rt_btreemap_first_key()`
  ```simple
  expect __rt_btreemap_first_key(m) == "a"
  ```
- **Line 379**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 37**: `rt_hashset_symmetric_difference()`
  ```simple
  extern fn __rt_hashset_symmetric_difference(a: i64, b: i64) -> i64
  ```
- **Line 380**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "a", 1)
  ```
- **Line 381**: `rt_btreemap_insert()`
  ```simple
  __rt_btreemap_insert(m, "z", 26)
  ```
- **Line 382**: `rt_btreemap_last_key()`
  ```simple
  expect __rt_btreemap_last_key(m) == "z"
  ```
- **Line 385**: `rt_btreemap_new()`
  ```simple
  val m = __rt_btreemap_new()
  ```
- **Line 386**: `rt_btreemap_first_key()`
  ```simple
  expect __rt_btreemap_first_key(m) == nil
  ```
- **Line 38**: `rt_hashset_is_subset()`
  ```simple
  extern fn __rt_hashset_is_subset(a: i64, b: i64) -> bool
  ```
- **Line 393**: `rt_btreeset_new()`
  ```simple
  val s = __rt_btreeset_new()
  ```
- **Line 394**: `rt_btreeset_len()`
  ```simple
  expect __rt_btreeset_len(s) == 0
  ```
- **Line 397**: `rt_btreeset_new()`
  ```simple
  val s = __rt_btreeset_new()
  ```
- **Line 398**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "apple")
  ```
- **Line 399**: `rt_btreeset_contains()`
  ```simple
  expect __rt_btreeset_contains(s, "apple") == true
  ```
- **Line 39**: `rt_hashset_is_superset()`
  ```simple
  extern fn __rt_hashset_is_superset(a: i64, b: i64) -> bool
  ```
- **Line 402**: `rt_btreeset_new()`
  ```simple
  val s = __rt_btreeset_new()
  ```
- **Line 403**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "x")
  ```
- **Line 404**: `rt_btreeset_remove()`
  ```simple
  expect __rt_btreeset_remove(s, "x") == true
  ```
- **Line 405**: `rt_btreeset_contains()`
  ```simple
  expect __rt_btreeset_contains(s, "x") == false
  ```
- **Line 408**: `rt_btreeset_new()`
  ```simple
  val s = __rt_btreeset_new()
  ```
- **Line 409**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "a")
  ```
- **Line 410**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "b")
  ```
- **Line 411**: `rt_btreeset_len()`
  ```simple
  expect __rt_btreeset_len(s) == 2
  ```
- **Line 414**: `rt_btreeset_new()`
  ```simple
  val s = __rt_btreeset_new()
  ```
- **Line 415**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "x")
  ```
- **Line 416**: `rt_btreeset_clear()`
  ```simple
  __rt_btreeset_clear(s)
  ```
- **Line 417**: `rt_btreeset_len()`
  ```simple
  expect __rt_btreeset_len(s) == 0
  ```
- **Line 420**: `rt_btreeset_new()`
  ```simple
  val s = __rt_btreeset_new()
  ```
- **Line 421**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "c")
  ```
- **Line 422**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "a")
  ```
- **Line 423**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "b")
  ```
- **Line 424**: `rt_btreeset_to_array()`
  ```simple
  val arr = __rt_btreeset_to_array(s)
  ```
- **Line 42**: `rt_btreemap_new()`
  ```simple
  extern fn __rt_btreemap_new() -> i64
  ```
- **Line 430**: `rt_btreeset_new()`
  ```simple
  val s = __rt_btreeset_new()
  ```
- **Line 431**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "z")
  ```
- **Line 432**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "a")
  ```
- **Line 433**: `rt_btreeset_first()`
  ```simple
  expect __rt_btreeset_first(s) == "a"
  ```
- **Line 436**: `rt_btreeset_new()`
  ```simple
  val s = __rt_btreeset_new()
  ```
- **Line 437**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "a")
  ```
- **Line 438**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(s, "z")
  ```
- **Line 439**: `rt_btreeset_last()`
  ```simple
  expect __rt_btreeset_last(s) == "z"
  ```
- **Line 43**: `rt_btreemap_insert()`
  ```simple
  extern fn __rt_btreemap_insert(handle: i64, key: text, value: Any) -> bool
  ```
- **Line 442**: `rt_btreeset_new()`
  ```simple
  val a = __rt_btreeset_new()
  ```
- **Line 443**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "1")
  ```
- **Line 444**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "2")
  ```
- **Line 445**: `rt_btreeset_new()`
  ```simple
  val b = __rt_btreeset_new()
  ```
- **Line 446**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "2")
  ```
- **Line 447**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "3")
  ```
- **Line 448**: `rt_btreeset_union()`
  ```simple
  val u = __rt_btreeset_union(a, b)
  ```
- **Line 449**: `rt_btreeset_len()`
  ```simple
  expect __rt_btreeset_len(u) == 3
  ```
- **Line 44**: `rt_btreemap_get()`
  ```simple
  extern fn __rt_btreemap_get(handle: i64, key: text) -> Any
  ```
- **Line 452**: `rt_btreeset_new()`
  ```simple
  val a = __rt_btreeset_new()
  ```
- **Line 453**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "1")
  ```
- **Line 454**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "2")
  ```
- **Line 455**: `rt_btreeset_new()`
  ```simple
  val b = __rt_btreeset_new()
  ```
- **Line 456**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "2")
  ```
- **Line 457**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "3")
  ```
- **Line 458**: `rt_btreeset_intersection()`
  ```simple
  val inter = __rt_btreeset_intersection(a, b)
  ```
- **Line 459**: `rt_btreeset_len()`
  ```simple
  expect __rt_btreeset_len(inter) == 1
  ```
- **Line 45**: `rt_btreemap_contains_key()`
  ```simple
  extern fn __rt_btreemap_contains_key(handle: i64, key: text) -> bool
  ```
- **Line 462**: `rt_btreeset_new()`
  ```simple
  val a = __rt_btreeset_new()
  ```
- **Line 463**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "1")
  ```
- **Line 464**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "2")
  ```
- **Line 465**: `rt_btreeset_new()`
  ```simple
  val b = __rt_btreeset_new()
  ```
- **Line 466**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "2")
  ```
- **Line 467**: `rt_btreeset_difference()`
  ```simple
  val d = __rt_btreeset_difference(a, b)
  ```
- **Line 468**: `rt_btreeset_len()`
  ```simple
  expect __rt_btreeset_len(d) == 1
  ```
- **Line 46**: `rt_btreemap_remove()`
  ```simple
  extern fn __rt_btreemap_remove(handle: i64, key: text) -> Any
  ```
- **Line 471**: `rt_btreeset_new()`
  ```simple
  val a = __rt_btreeset_new()
  ```
- **Line 472**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "1")
  ```
- **Line 473**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "2")
  ```
- **Line 474**: `rt_btreeset_new()`
  ```simple
  val b = __rt_btreeset_new()
  ```
- **Line 475**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "2")
  ```
- **Line 476**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "3")
  ```
- **Line 477**: `rt_btreeset_symmetric_difference()`
  ```simple
  val sd = __rt_btreeset_symmetric_difference(a, b)
  ```
- **Line 478**: `rt_btreeset_len()`
  ```simple
  expect __rt_btreeset_len(sd) == 2
  ```
- **Line 47**: `rt_btreemap_len()`
  ```simple
  extern fn __rt_btreemap_len(handle: i64) -> i64
  ```
- **Line 481**: `rt_btreeset_new()`
  ```simple
  val a = __rt_btreeset_new()
  ```
- **Line 482**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "1")
  ```
- **Line 483**: `rt_btreeset_new()`
  ```simple
  val b = __rt_btreeset_new()
  ```
- **Line 484**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "1")
  ```
- **Line 485**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "2")
  ```
- **Line 486**: `rt_btreeset_is_subset()`
  ```simple
  expect __rt_btreeset_is_subset(a, b) == true
  ```
- **Line 489**: `rt_btreeset_new()`
  ```simple
  val a = __rt_btreeset_new()
  ```
- **Line 48**: `rt_btreemap_clear()`
  ```simple
  extern fn __rt_btreemap_clear(handle: i64) -> bool
  ```
- **Line 490**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "1")
  ```
- **Line 491**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(a, "2")
  ```
- **Line 492**: `rt_btreeset_new()`
  ```simple
  val b = __rt_btreeset_new()
  ```
- **Line 493**: `rt_btreeset_insert()`
  ```simple
  __rt_btreeset_insert(b, "1")
  ```
- **Line 494**: `rt_btreeset_is_superset()`
  ```simple
  expect __rt_btreeset_is_superset(a, b) == true
  ```
- **Line 49**: `rt_btreemap_keys()`
  ```simple
  extern fn __rt_btreemap_keys(handle: i64) -> Any
  ```
- **Line 501**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 505**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 506**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, 42)
  ```
- **Line 507**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == 42
  ```
- **Line 50**: `rt_btreemap_values()`
  ```simple
  extern fn __rt_btreemap_values(handle: i64) -> Any
  ```
- **Line 510**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 511**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == nil
  ```
- **Line 514**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 515**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, 1)
  ```
- **Line 516**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, 2)
  ```
- **Line 517**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, 3)
  ```
- **Line 518**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == 1
  ```
- **Line 519**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == 2
  ```
- **Line 51**: `rt_btreemap_entries()`
  ```simple
  extern fn __rt_btreemap_entries(handle: i64) -> Any
  ```
- **Line 520**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == 3
  ```
- **Line 523**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 524**: `rt_channel_close()`
  ```simple
  rt_channel_close(ch)
  ```
- **Line 525**: `rt_channel_is_closed()`
  ```simple
  expect rt_channel_is_closed(ch) == 1
  ```
- **Line 528**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 529**: `rt_channel_is_closed()`
  ```simple
  expect rt_channel_is_closed(ch) == 0
  ```
- **Line 52**: `rt_btreemap_first_key()`
  ```simple
  extern fn __rt_btreemap_first_key(handle: i64) -> Any
  ```
- **Line 532**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 533**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, "hello")
  ```
- **Line 534**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == "hello"
  ```
- **Line 537**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 538**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, true)
  ```
- **Line 539**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == true
  ```
- **Line 53**: `rt_btreemap_last_key()`
  ```simple
  extern fn __rt_btreemap_last_key(handle: i64) -> Any
  ```
- **Line 542**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 543**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, 42)
  ```
- **Line 544**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, "text")
  ```
- **Line 545**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, true)
  ```
- **Line 546**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == 42
  ```
- **Line 547**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == "text"
  ```
- **Line 548**: `rt_channel_try_recv()`
  ```simple
  expect rt_channel_try_recv(ch) == true
  ```
- **Line 551**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 552**: `rt_channel_send()`
  ```simple
  rt_channel_send(ch, 99)
  ```
- **Line 553**: `rt_channel_recv()`
  ```simple
  expect rt_channel_recv(ch) == 99
  ```
- **Line 560**: `rt_thread_available_parallelism()`
  ```simple
  expect rt_thread_available_parallelism() >= 1
  ```
- **Line 563**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(1)
  ```
- **Line 567**: `rt_thread_yield()`
  ```simple
  rt_thread_yield()
  ```
- **Line 56**: `rt_btreeset_new()`
  ```simple
  extern fn __rt_btreeset_new() -> i64
  ```
- **Line 576**: `rt_thread_join()`
  ```simple
  val result = rt_thread_join(handle)
  ```
- **Line 57**: `rt_btreeset_insert()`
  ```simple
  extern fn __rt_btreeset_insert(handle: i64, value: text) -> bool
  ```
- **Line 581**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 583**: `rt_channel_send()`
  ```simple
  rt_channel_send(channel_id, data)
  ```
- **Line 586**: `rt_channel_recv()`
  ```simple
  val result = rt_channel_recv(ch)
  ```
- **Line 587**: `rt_thread_join()`
  ```simple
  rt_thread_join(handle)
  ```
- **Line 58**: `rt_btreeset_contains()`
  ```simple
  extern fn __rt_btreeset_contains(handle: i64, value: text) -> bool
  ```
- **Line 591**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 593**: `rt_channel_send()`
  ```simple
  rt_channel_send(b, a * 2)
  ```
- **Line 596**: `rt_channel_recv()`
  ```simple
  val result = rt_channel_recv(ch)
  ```
- **Line 597**: `rt_thread_join()`
  ```simple
  rt_thread_join(handle)
  ```
- **Line 59**: `rt_btreeset_remove()`
  ```simple
  extern fn __rt_btreeset_remove(handle: i64, value: text) -> bool
  ```
- **Line 601**: `rt_channel_new()`
  ```simple
  val ch = rt_channel_new()
  ```
- **Line 603**: `rt_channel_send()`
  ```simple
  rt_channel_send(c, d)
  ```
- **Line 607**: `rt_channel_send()`
  ```simple
  rt_channel_send(c, d)
  ```
- **Line 60**: `rt_btreeset_len()`
  ```simple
  extern fn __rt_btreeset_len(handle: i64) -> i64
  ```
- **Line 610**: `rt_channel_recv()`
  ```simple
  val r1 = rt_channel_recv(ch)
  ```
- **Line 611**: `rt_channel_recv()`
  ```simple
  val r2 = rt_channel_recv(ch)
  ```
- **Line 612**: `rt_thread_join()`
  ```simple
  rt_thread_join(h1)
  ```
- **Line 613**: `rt_thread_join()`
  ```simple
  rt_thread_join(h2)
  ```
- **Line 61**: `rt_btreeset_clear()`
  ```simple
  extern fn __rt_btreeset_clear(handle: i64) -> bool
  ```
- **Line 621**: `rt_mutex_new()`
  ```simple
  val m = rt_mutex_new(42)
  ```
- **Line 625**: `rt_mutex_new()`
  ```simple
  val m = rt_mutex_new(42)
  ```
- **Line 626**: `rt_mutex_lock()`
  ```simple
  val v = rt_mutex_lock(m)
  ```
- **Line 62**: `rt_btreeset_to_array()`
  ```simple
  extern fn __rt_btreeset_to_array(handle: i64) -> Any
  ```
- **Line 630**: `rt_mutex_new()`
  ```simple
  val m = rt_mutex_new(10)
  ```
- **Line 631**: `rt_mutex_try_lock()`
  ```simple
  val v = rt_mutex_try_lock(m)
  ```
- **Line 635**: `rt_mutex_new()`
  ```simple
  val m = rt_mutex_new(1)
  ```
- **Line 636**: `rt_mutex_lock()`
  ```simple
  rt_mutex_lock(m)
  ```
- **Line 637**: `rt_mutex_unlock()`
  ```simple
  rt_mutex_unlock(m, 2)
  ```
- **Line 638**: `rt_mutex_lock()`
  ```simple
  val v = rt_mutex_lock(m)
  ```
- **Line 63**: `rt_btreeset_first()`
  ```simple
  extern fn __rt_btreeset_first(handle: i64) -> Any
  ```
- **Line 642**: `rt_mutex_new()`
  ```simple
  val m = rt_mutex_new(0)
  ```
- **Line 643**: `rt_mutex_lock()`
  ```simple
  rt_mutex_lock(m)
  ```
- **Line 644**: `rt_mutex_unlock()`
  ```simple
  rt_mutex_unlock(m, 1)
  ```
- **Line 645**: `rt_mutex_lock()`
  ```simple
  rt_mutex_lock(m)
  ```
- **Line 646**: `rt_mutex_unlock()`
  ```simple
  rt_mutex_unlock(m, 2)
  ```
- **Line 647**: `rt_mutex_lock()`
  ```simple
  rt_mutex_lock(m)
  ```
- **Line 648**: `rt_mutex_unlock()`
  ```simple
  rt_mutex_unlock(m, 3)
  ```
- **Line 64**: `rt_btreeset_last()`
  ```simple
  extern fn __rt_btreeset_last(handle: i64) -> Any
  ```
- **Line 652**: `rt_mutex_new()`
  ```simple
  val m = rt_mutex_new(100)
  ```
- **Line 656**: `rt_mutex_new()`
  ```simple
  val m1 = rt_mutex_new(1)
  ```
- **Line 657**: `rt_mutex_new()`
  ```simple
  val m2 = rt_mutex_new(2)
  ```
- **Line 658**: `rt_mutex_new()`
  ```simple
  val m3 = rt_mutex_new(3)
  ```
- **Line 65**: `rt_btreeset_union()`
  ```simple
  extern fn __rt_btreeset_union(a: i64, b: i64) -> i64
  ```
- **Line 664**: `rt_mutex_new()`
  ```simple
  val m = rt_mutex_new(99)
  ```
- **Line 665**: `rt_mutex_lock()`
  ```simple
  val locked = rt_mutex_lock(m)
  ```
- **Line 66**: `rt_btreeset_intersection()`
  ```simple
  extern fn __rt_btreeset_intersection(a: i64, b: i64) -> i64
  ```
- **Line 674**: `rt_rwlock_new()`
  ```simple
  val rw = rt_rwlock_new(42)
  ```
- **Line 678**: `rt_rwlock_new()`
  ```simple
  val rw = rt_rwlock_new(42)
  ```
- **Line 679**: `rt_rwlock_read()`
  ```simple
  val v = rt_rwlock_read(rw)
  ```
- **Line 67**: `rt_btreeset_difference()`
  ```simple
  extern fn __rt_btreeset_difference(a: i64, b: i64) -> i64
  ```
- **Line 683**: `rt_rwlock_new()`
  ```simple
  val rw = rt_rwlock_new(42)
  ```
- **Line 684**: `rt_rwlock_write()`
  ```simple
  val v = rt_rwlock_write(rw)
  ```
- **Line 688**: `rt_rwlock_new()`
  ```simple
  val rw = rt_rwlock_new(10)
  ```
- **Line 689**: `rt_rwlock_try_read()`
  ```simple
  val v = rt_rwlock_try_read(rw)
  ```
- **Line 68**: `rt_btreeset_symmetric_difference()`
  ```simple
  extern fn __rt_btreeset_symmetric_difference(a: i64, b: i64) -> i64
  ```
- **Line 693**: `rt_rwlock_new()`
  ```simple
  val rw = rt_rwlock_new(10)
  ```
- **Line 694**: `rt_rwlock_try_write()`
  ```simple
  val v = rt_rwlock_try_write(rw)
  ```
- **Line 698**: `rt_rwlock_new()`
  ```simple
  val rw = rt_rwlock_new(1)
  ```
- **Line 699**: `rt_rwlock_set()`
  ```simple
  rt_rwlock_set(rw, 2)
  ```
- **Line 69**: `rt_btreeset_is_subset()`
  ```simple
  extern fn __rt_btreeset_is_subset(a: i64, b: i64) -> bool
  ```
- **Line 703**: `rt_rwlock_new()`
  ```simple
  val r1 = rt_rwlock_new(1)
  ```
- **Line 704**: `rt_rwlock_new()`
  ```simple
  val r2 = rt_rwlock_new(2)
  ```
- **Line 709**: `rt_rwlock_new()`
  ```simple
  val rw = rt_rwlock_new(10)
  ```
- **Line 70**: `rt_btreeset_is_superset()`
  ```simple
  extern fn __rt_btreeset_is_superset(a: i64, b: i64) -> bool
  ```
- **Line 710**: `rt_rwlock_set()`
  ```simple
  rt_rwlock_set(rw, 20)
  ```
- **Line 711**: `rt_rwlock_read()`
  ```simple
  val v = rt_rwlock_read(rw)
  ```

#### `test/lib/std/unit/concurrency/perf_optimization_spec.spl`

- **Line 227**: `rt_channel_send()`
  ```simple
  rt_channel_send(channel_id, data * 7)
  ```
- **Line 239**: `rt_channel_send()`
  ```simple
  rt_channel_send(channel_id, i * 10)
  ```
- **Line 270**: `rt_get_concurrent_backend()`
  ```simple
  val backend = rt_get_concurrent_backend()
  ```
- **Line 275**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("native")
  ```
- **Line 276**: `rt_get_concurrent_backend()`
  ```simple
  expect rt_get_concurrent_backend() == "native"
  ```
- **Line 277**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 278**: `rt_get_concurrent_backend()`
  ```simple
  expect rt_get_concurrent_backend() == "pure_std"
  ```
- **Line 281**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("std")
  ```
- **Line 282**: `rt_get_concurrent_backend()`
  ```simple
  expect rt_get_concurrent_backend() == "pure_std"
  ```
- **Line 285**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 286**: `rt_get_concurrent_backend()`
  ```simple
  expect rt_get_concurrent_backend() == "pure_std"
  ```
- **Line 290**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("native")
  ```
- **Line 294**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 297**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("native")
  ```
- **Line 303**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 306**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("native")
  ```
- **Line 310**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 314**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("native")
  ```
- **Line 315**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 321**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 322**: `rt_thread_available_parallelism()`
  ```simple
  val cores = rt_thread_available_parallelism()
  ```
- **Line 326**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("native")
  ```
- **Line 327**: `rt_thread_available_parallelism()`
  ```simple
  val cores = rt_thread_available_parallelism()
  ```
- **Line 329**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 348**: `rt_channel_send()`
  ```simple
  rt_channel_send(channel_id, i * 10)
  ```
- **Line 369**: `rt_channel_send()`
  ```simple
  rt_channel_send(channel_id, data)
  ```
- **Line 412**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("native")
  ```
- **Line 416**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 483**: `rt_channel_send()`
  ```simple
  rt_channel_send(channel_id, thread_num * 100 + j)
  ```
- **Line 503**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 505**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("native")
  ```
- **Line 510**: `rt_set_concurrent_backend()`
  ```simple
  rt_set_concurrent_backend("pure_std")
  ```
- **Line 517**: `rt_thread_free()`
  ```simple
  rt_thread_free(h._handle)
  ```
- **Line 565**: `rt_thread_yield()`
  ```simple
  rt_thread_yield()
  ```
- **Line 569**: `rt_thread_sleep()`
  ```simple
  rt_thread_sleep(1)
  ```
- **Line 56**: `rt_channel_send()`
  ```simple
  rt_channel_send(self._id, value)
  ```
- **Line 59**: `rt_channel_try_recv()`
  ```simple
  return rt_channel_try_recv(self._id)
  ```
- **Line 62**: `rt_channel_recv()`
  ```simple
  return rt_channel_recv(self._id)
  ```
- **Line 65**: `rt_channel_close()`
  ```simple
  rt_channel_close(self._id)
  ```
- **Line 68**: `rt_channel_is_closed()`
  ```simple
  return rt_channel_is_closed(self._id) == 1
  ```
- **Line 71**: `rt_channel_new()`
  ```simple
  val id = rt_channel_new()
  ```
- **Line 78**: `rt_thread_join()`
  ```simple
  return rt_thread_join(self._handle)
  ```
- **Line 81**: `rt_thread_is_done()`
  ```simple
  return rt_thread_is_done(self._handle) == 1
  ```
- **Line 84**: `rt_thread_id()`
  ```simple
  return rt_thread_id(self._handle)
  ```
- **Line 87**: `rt_thread_spawn_isolated()`
  ```simple
  val handle = rt_thread_spawn_isolated(closure)
  ```

#### `test/lib/std/unit/exp/artifact_spec.spl`

- **Line 47**: `rt_run()`
  ```simple
  val run = start_run(config, [])
  ```
- **Line 55**: `rt_run()`
  ```simple
  val run = start_run(config, [])
  ```
- **Line 64**: `rt_run()`
  ```simple
  val run = start_run(config, [])
  ```
- **Line 71**: `rt_run()`
  ```simple
  val run = start_run(config, [])
  ```

#### `test/lib/std/unit/exp/run_spec.spl`

- **Line 104**: `rt_run()`
  ```simple
  var run = start_run(config, [])
  ```
- **Line 110**: `rt_run()`
  ```simple
  var run = start_run(config, [])
  ```
- **Line 57**: `rt_run()`
  ```simple
  val run = start_run(config, [])
  ```
- **Line 64**: `rt_run()`
  ```simple
  val run = start_run(config, ["baseline", "v2"])
  ```
- **Line 70**: `rt_run()`
  ```simple
  var run = start_run(config, [])
  ```
- **Line 78**: `rt_run()`
  ```simple
  var run = start_run(config, [])
  ```
- **Line 85**: `rt_run()`
  ```simple
  val run = start_run(config, [])
  ```
- **Line 91**: `rt_run()`
  ```simple
  var run = start_run(config, [])
  ```
- **Line 97**: `rt_run()`
  ```simple
  var run = start_run(config, [])
  ```

#### `test/lib/std/unit/failsafe/failsafe_module_spec.spl`

- **Line 110**: `rt_operation()`
  ```simple
  deadline.start_operation()
  ```
- **Line 56**: `rt_timeout()`
  ```simple
  val token = manager.start_timeout("operation")
  ```

#### `test/lib/std/unit/failsafe/panic_spec.spl`

- **Line 110**: `rt_some()`
  ```simple
  match assert_some(opt, "Should have value")
  ```
- **Line 118**: `rt_some()`
  ```simple
  expect(assert_some(opt, "Missing").is_err())
  ```

#### `test/lib/std/unit/failsafe/timeout_spec.spl`

- **Line 123**: `rt_operation()`
  ```simple
  deadline.start_operation()
  ```
- **Line 124**: `rt_operation()`
  ```simple
  deadline.start_operation()
  ```
- **Line 66**: `rt_timeout()`
  ```simple
  val token = manager.start_timeout("test_op")
  ```
- **Line 74**: `rt_timeout_ms()`
  ```simple
  val token = manager.start_timeout_ms("test_op", 5000)
  ```
- **Line 80**: `rt_timeout()`
  ```simple
  val token = manager.start_timeout("test_op")
  ```
- **Line 87**: `rt_timeout()`
  ```simple
  val token = manager.start_timeout("test_op")
  ```

#### `test/lib/std/unit/infra/atomic_spec.spl`

- **Line 102**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(42)
  ```
- **Line 103**: `rt_atomic_int_compare_exchange()`
  ```simple
  val success = rt_atomic_int_compare_exchange(atomic, 50, 100)
  ```
- **Line 105**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 42)
  ```
- **Line 106**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 109**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(0)
  ```
- **Line 110**: `rt_atomic_int_compare_exchange()`
  ```simple
  rt_atomic_int_compare_exchange(atomic, 0, 1)
  ```
- **Line 111**: `rt_atomic_int_compare_exchange()`
  ```simple
  rt_atomic_int_compare_exchange(atomic, 1, 2)
  ```
- **Line 112**: `rt_atomic_int_compare_exchange()`
  ```simple
  rt_atomic_int_compare_exchange(atomic, 2, 3)
  ```
- **Line 113**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 3)
  ```
- **Line 114**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 118**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(10)
  ```
- **Line 119**: `rt_atomic_int_fetch_add()`
  ```simple
  val old_val = rt_atomic_int_fetch_add(atomic, 5)
  ```
- **Line 121**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 15)
  ```
- **Line 122**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 125**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(20)
  ```
- **Line 126**: `rt_atomic_int_fetch_sub()`
  ```simple
  val old_val = rt_atomic_int_fetch_sub(atomic, 7)
  ```
- **Line 128**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 13)
  ```
- **Line 129**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 132**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(5)
  ```
- **Line 133**: `rt_atomic_int_fetch_sub()`
  ```simple
  rt_atomic_int_fetch_sub(atomic, 10)
  ```
- **Line 134**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == -5)
  ```
- **Line 135**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 139**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(0b1111)
  ```
- **Line 140**: `rt_atomic_int_fetch_and()`
  ```simple
  val old_val = rt_atomic_int_fetch_and(atomic, 0b1010)
  ```
- **Line 142**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 10)
  ```
- **Line 143**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 146**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(0b1010)
  ```
- **Line 147**: `rt_atomic_int_fetch_or()`
  ```simple
  val old_val = rt_atomic_int_fetch_or(atomic, 0b0101)
  ```
- **Line 149**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 15)
  ```
- **Line 150**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 153**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(0b1010)
  ```
- **Line 154**: `rt_atomic_int_fetch_xor()`
  ```simple
  val old_val = rt_atomic_int_fetch_xor(atomic, 0b1111)
  ```
- **Line 156**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 5)
  ```
- **Line 157**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 160**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(42)
  ```
- **Line 161**: `rt_atomic_int_fetch_xor()`
  ```simple
  rt_atomic_int_fetch_xor(atomic, 42)
  ```
- **Line 162**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 0)
  ```
- **Line 163**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 167**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(10)
  ```
- **Line 168**: `rt_atomic_int_fetch_add()`
  ```simple
  rt_atomic_int_fetch_add(atomic, 5)      # 10 + 5 = 15
  ```
- **Line 169**: `rt_atomic_int_fetch_sub()`
  ```simple
  rt_atomic_int_fetch_sub(atomic, 3)      # 15 - 3 = 12
  ```
- **Line 170**: `rt_atomic_int_fetch_and()`
  ```simple
  rt_atomic_int_fetch_and(atomic, 0b1110) # 12 & 14 = 12
  ```
- **Line 171**: `rt_atomic_int_fetch_or()`
  ```simple
  rt_atomic_int_fetch_or(atomic, 0b0001)  # 12 | 1 = 13
  ```
- **Line 172**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 13)
  ```
- **Line 173**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 177**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(0)
  ```
- **Line 178**: `rt_atomic_int_fetch_add()`
  ```simple
  rt_atomic_int_fetch_add(atomic, 1)  # 1
  ```
- **Line 179**: `rt_atomic_int_fetch_add()`
  ```simple
  rt_atomic_int_fetch_add(atomic, 1)  # 2
  ```
- **Line 180**: `rt_atomic_int_fetch_add()`
  ```simple
  rt_atomic_int_fetch_add(atomic, 1)  # 3
  ```
- **Line 181**: `rt_atomic_int_fetch_add()`
  ```simple
  rt_atomic_int_fetch_add(atomic, 1)  # 4
  ```
- **Line 182**: `rt_atomic_int_fetch_add()`
  ```simple
  rt_atomic_int_fetch_add(atomic, 1)  # 5
  ```
- **Line 183**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 5)
  ```
- **Line 184**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 188**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(5)
  ```
- **Line 189**: `rt_atomic_int_fetch_sub()`
  ```simple
  rt_atomic_int_fetch_sub(atomic, 1)  # 4
  ```
- **Line 190**: `rt_atomic_int_fetch_sub()`
  ```simple
  rt_atomic_int_fetch_sub(atomic, 1)  # 3
  ```
- **Line 191**: `rt_atomic_int_fetch_sub()`
  ```simple
  rt_atomic_int_fetch_sub(atomic, 1)  # 2
  ```
- **Line 192**: `rt_atomic_int_fetch_sub()`
  ```simple
  rt_atomic_int_fetch_sub(atomic, 1)  # 1
  ```
- **Line 193**: `rt_atomic_int_fetch_sub()`
  ```simple
  rt_atomic_int_fetch_sub(atomic, 1)  # 0
  ```
- **Line 194**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 0)
  ```
- **Line 195**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 199**: `rt_atomic_bool_new()`
  ```simple
  val atomic = rt_atomic_bool_new(false)
  ```
- **Line 200**: `rt_atomic_bool_load()`
  ```simple
  expect(rt_atomic_bool_load(atomic) == false)
  ```
- **Line 201**: `rt_atomic_bool_free()`
  ```simple
  rt_atomic_bool_free(atomic)
  ```
- **Line 204**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(0)
  ```
- **Line 205**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 0)
  ```
- **Line 206**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 209**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(1000000)
  ```
- **Line 210**: `rt_atomic_int_fetch_add()`
  ```simple
  rt_atomic_int_fetch_add(atomic, 1000000)
  ```
- **Line 211**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 2000000)
  ```
- **Line 212**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 215**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(-100)
  ```
- **Line 216**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == -100)
  ```
- **Line 217**: `rt_atomic_int_fetch_add()`
  ```simple
  rt_atomic_int_fetch_add(atomic, 50)
  ```
- **Line 218**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == -50)
  ```
- **Line 219**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 222**: `rt_atomic_bool_new()`
  ```simple
  val atomic = rt_atomic_bool_new(false)
  ```
- **Line 223**: `rt_atomic_bool_swap()`
  ```simple
  rt_atomic_bool_swap(atomic, true)
  ```
- **Line 224**: `rt_atomic_bool_swap()`
  ```simple
  rt_atomic_bool_swap(atomic, false)
  ```
- **Line 225**: `rt_atomic_bool_swap()`
  ```simple
  rt_atomic_bool_swap(atomic, true)
  ```
- **Line 226**: `rt_atomic_bool_load()`
  ```simple
  expect(rt_atomic_bool_load(atomic) == true)
  ```
- **Line 227**: `rt_atomic_bool_free()`
  ```simple
  rt_atomic_bool_free(atomic)
  ```
- **Line 39**: `rt_atomic_bool_new()`
  ```simple
  val atomic = rt_atomic_bool_new(true)
  ```
- **Line 40**: `rt_atomic_bool_load()`
  ```simple
  expect(rt_atomic_bool_load(atomic) == true)
  ```
- **Line 41**: `rt_atomic_bool_free()`
  ```simple
  rt_atomic_bool_free(atomic)
  ```
- **Line 44**: `rt_atomic_bool_new()`
  ```simple
  val atomic = rt_atomic_bool_new(false)
  ```
- **Line 45**: `rt_atomic_bool_load()`
  ```simple
  expect(rt_atomic_bool_load(atomic) == false)
  ```
- **Line 46**: `rt_atomic_bool_free()`
  ```simple
  rt_atomic_bool_free(atomic)
  ```
- **Line 49**: `rt_atomic_bool_new()`
  ```simple
  val atomic = rt_atomic_bool_new(false)
  ```
- **Line 50**: `rt_atomic_bool_store()`
  ```simple
  rt_atomic_bool_store(atomic, true)
  ```
- **Line 51**: `rt_atomic_bool_load()`
  ```simple
  expect(rt_atomic_bool_load(atomic) == true)
  ```
- **Line 52**: `rt_atomic_bool_free()`
  ```simple
  rt_atomic_bool_free(atomic)
  ```
- **Line 55**: `rt_atomic_bool_new()`
  ```simple
  val atomic = rt_atomic_bool_new(true)
  ```
- **Line 56**: `rt_atomic_bool_swap()`
  ```simple
  val old_value = rt_atomic_bool_swap(atomic, false)
  ```
- **Line 58**: `rt_atomic_bool_load()`
  ```simple
  expect(rt_atomic_bool_load(atomic) == false)
  ```
- **Line 59**: `rt_atomic_bool_free()`
  ```simple
  rt_atomic_bool_free(atomic)
  ```
- **Line 62**: `rt_atomic_bool_new()`
  ```simple
  val atomic = rt_atomic_bool_new(false)
  ```
- **Line 63**: `rt_atomic_bool_store()`
  ```simple
  rt_atomic_bool_store(atomic, true)
  ```
- **Line 64**: `rt_atomic_bool_store()`
  ```simple
  rt_atomic_bool_store(atomic, false)
  ```
- **Line 65**: `rt_atomic_bool_store()`
  ```simple
  rt_atomic_bool_store(atomic, true)
  ```
- **Line 66**: `rt_atomic_bool_load()`
  ```simple
  expect(rt_atomic_bool_load(atomic) == true)
  ```
- **Line 67**: `rt_atomic_bool_free()`
  ```simple
  rt_atomic_bool_free(atomic)
  ```
- **Line 71**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(42)
  ```
- **Line 72**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 42)
  ```
- **Line 73**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 76**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(0)
  ```
- **Line 77**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 0)
  ```
- **Line 78**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 81**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(10)
  ```
- **Line 82**: `rt_atomic_int_store()`
  ```simple
  rt_atomic_int_store(atomic, 20)
  ```
- **Line 83**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 20)
  ```
- **Line 84**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 87**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(100)
  ```
- **Line 88**: `rt_atomic_int_swap()`
  ```simple
  val old_value = rt_atomic_int_swap(atomic, 200)
  ```
- **Line 90**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 200)
  ```
- **Line 91**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```
- **Line 95**: `rt_atomic_int_new()`
  ```simple
  val atomic = rt_atomic_int_new(42)
  ```
- **Line 96**: `rt_atomic_int_compare_exchange()`
  ```simple
  val success = rt_atomic_int_compare_exchange(atomic, 42, 100)
  ```
- **Line 98**: `rt_atomic_int_load()`
  ```simple
  expect(rt_atomic_int_load(atomic) == 100)
  ```
- **Line 99**: `rt_atomic_int_free()`
  ```simple
  rt_atomic_int_free(atomic)
  ```

#### `test/lib/std/unit/lsp/completion_spec.spl`

- **Line 92**: `rt_text()`
  ```simple
  .with_insert_text("fn ${1:name}():n    ${0}")
  ```

#### `test/lib/std/unit/mcp/tasks_spec.spl`

- **Line 197**: `rt_task()`
  ```simple
  val result = manager.start_task(task_id)
  ```
- **Line 216**: `rt_task()`
  ```simple
  manager.start_task(task_id)
  ```
- **Line 238**: `rt_task()`
  ```simple
  manager.start_task(task_id)
  ```
- **Line 250**: `rt_task()`
  ```simple
  manager.start_task(task_id)
  ```
- **Line 271**: `rt_task()`
  ```simple
  manager.start_task(task_id)
  ```
- **Line 292**: `rt_task()`
  ```simple
  manager.start_task(task_id)
  ```
- **Line 322**: `rt_task()`
  ```simple
  manager.start_task(id1)
  ```
- **Line 323**: `rt_task()`
  ```simple
  manager.start_task(id2)
  ```
- **Line 339**: `rt_task()`
  ```simple
  manager.start_task(id1)
  ```
- **Line 340**: `rt_task()`
  ```simple
  manager.start_task(id2)
  ```
- **Line 342**: `rt_task()`
  ```simple
  val result = manager.start_task(id3)
  ```
- **Line 354**: `rt_task()`
  ```simple
  manager.start_task(id1)
  ```

#### `test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl`

- **Line 112**: `rt_outer()`
  ```simple
  val result = @rt_outer(@rt_inner(5))
  ```
- **Line 126**: `rt_check()`
  ```simple
  if @rt_check()
  ```
- **Line 136**: `rt_torch_randn()`
  ```simple
  val handle1 = @rt_torch_randn(100)
  ```
- **Line 137**: `rt_torch_randn()`
  ```simple
  val handle2 = @rt_torch_randn(100)
  ```
- **Line 138**: `rt_torch_add()`
  ```simple
  val result = @rt_torch_add(handle1, handle2)
  ```
- **Line 147**: `rt_torch_linalg_det()`
  ```simple
  val det_handle = @rt_torch_linalg_det(dummy_handle)
  ```
- **Line 26**: `rt_test_add()`
  ```simple
  val result = @rt_test_add(5, 3)
  ```
- **Line 34**: `rt_test_square()`
  ```simple
  val result = @rt_test_square(4)
  ```
- **Line 40**: `rt_test_random()`
  ```simple
  val result = @rt_test_random()
  ```
- **Line 47**: `rt_get_value()`
  ```simple
  val x = @rt_get_value()
  ```
- **Line 56**: `rt_compute()`
  ```simple
  val result = process(@rt_compute(10))
  ```
- **Line 62**: `rt_get_number()`
  ```simple
  val result = @rt_get_number() + 42
  ```
- **Line 81**: `rt_test_hir()`
  ```simple
  val x = @rt_test_hir()
  ```
- **Line 87**: `rt_test_preserve()`
  ```simple
  val x = @rt_test_preserve()
  ```
- **Line 94**: `rt_test_typecheck()`
  ```simple
  val x = @rt_test_typecheck()
  ```

#### `test/lib/std/unit/ml/torch/test_ffi_unit.spl`

- **Line 10**: `rt_basic_test()`
  ```simple
  val result = @rt_basic_test()
  ```
- **Line 17**: `rt_add()`
  ```simple
  val result = @rt_add(10, 20)
  ```
- **Line 24**: `rt_add()`
  ```simple
  val x = @rt_add(5, 3)
  ```
- **Line 25**: `rt_mul()`
  ```simple
  val y = @rt_mul(2, 4)
  ```
- **Line 32**: `rt_get()`
  ```simple
  val result = @rt_get() + 100
  ```
- **Line 39**: `rt_double()`
  ```simple
  val result = @rt_double(@rt_double(5))
  ```

#### `test/lib/std/unit/ml/torch/test_torch_ffi_minimal.spl`

- **Line 17**: `rt_torch_linalg_det()`
  ```simple
  val handle = @rt_torch_linalg_det(dummy_handle)
  ```
- **Line 24**: `rt_torch_linalg_inv()`
  ```simple
  val handle = @rt_torch_linalg_inv(dummy_handle)
  ```
- **Line 30**: `rt_torch_clamp()`
  ```simple
  val clamped = @rt_torch_clamp(dummy_handle, -1.0, 1.0)
  ```
- **Line 36**: `rt_torch_relu()`
  ```simple
  val output = @rt_torch_relu(dummy_handle)
  ```

#### `test/lib/std/unit/parser/treesitter/grammar_test_spec.spl`

- **Line 22**: `rt_results()`
  ```simple
  fn report_results() -> text
  ```
- **Line 39**: `rt_results()`
  ```simple
  val result = test.report_results()
  ```

#### `test/lib/std/unit/set_spec.spl`

- **Line 103**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 0, "Set should be empty after clear")
  ```
- **Line 104**: `rt_true()`
  ```simple
  testing.assert_true(s.is_empty(), "Set should report empty after clear")
  ```
- **Line 112**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 3, "Should have 3 elements")
  ```
- **Line 113**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Alice"), "Should contain Alice")
  ```
- **Line 114**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Bob"), "Should contain Bob")
  ```
- **Line 115**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Charlie"), "Should contain Charlie")
  ```
- **Line 123**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 2, "Should have only 2 unique elements")
  ```
- **Line 132**: `rt_eq()`
  ```simple
  testing.assert_eq(list.len(), 3, "List should have 3 elements")
  ```
- **Line 139**: `rt_contains()`
  ```simple
  testing.assert_contains(list, "Alice", "List should contain Alice")
  ```
- **Line 140**: `rt_contains()`
  ```simple
  testing.assert_contains(list, "Bob", "List should contain Bob")
  ```
- **Line 153**: `rt_eq()`
  ```simple
  testing.assert_eq(count, 3, "Should execute action 3 times")
  ```
- **Line 166**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 4, "Union should have 4 elements")
  ```
- **Line 167**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Alice"), "Should contain Alice")
  ```
- **Line 168**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Bob"), "Should contain Bob")
  ```
- **Line 169**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Charlie"), "Should contain Charlie")
  ```
- **Line 170**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("David"), "Should contain David")
  ```
- **Line 184**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 4, "Union should have 4 unique elements")
  ```
- **Line 194**: `rt_eq()`
  ```simple
  testing.assert_eq(s1.len(), 1, "Original s1 should be unchanged")
  ```
- **Line 195**: `rt_eq()`
  ```simple
  testing.assert_eq(s2.len(), 1, "Original s2 should be unchanged")
  ```
- **Line 210**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 2, "Intersection should have 2 elements")
  ```
- **Line 211**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Bob"), "Should contain Bob")
  ```
- **Line 212**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Charlie"), "Should contain Charlie")
  ```
- **Line 224**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 0, "Intersection should be empty")
  ```
- **Line 235**: `rt_eq()`
  ```simple
  testing.assert_eq(s1.len(), 2, "Original s1 should be unchanged")
  ```
- **Line 236**: `rt_eq()`
  ```simple
  testing.assert_eq(s2.len(), 1, "Original s2 should be unchanged")
  ```
- **Line 251**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 1, "Difference should have 1 element")
  ```
- **Line 252**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Alice"), "Should contain Alice")
  ```
- **Line 253**: `rt_false()`
  ```simple
  testing.assert_false(result.contains("Bob"), "Should not contain Bob")
  ```
- **Line 254**: `rt_false()`
  ```simple
  testing.assert_false(result.contains("Charlie"), "Should not contain Charlie")
  ```
- **Line 267**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 0, "Difference should be empty")
  ```
- **Line 282**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 2, "Symmetric difference should have 2 elements")
  ```
- **Line 283**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Alice"), "Should contain Alice")
  ```
- **Line 284**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("David"), "Should contain David")
  ```
- **Line 285**: `rt_false()`
  ```simple
  testing.assert_false(result.contains("Bob"), "Should not contain Bob")
  ```
- **Line 286**: `rt_false()`
  ```simple
  testing.assert_false(result.contains("Charlie"), "Should not contain Charlie")
  ```
- **Line 298**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 4, "Symmetric difference should have all elements")
  ```
- **Line 311**: `rt_true()`
  ```simple
  testing.assert_true(s1.is_subset(s2), "s1 should be subset of s2")
  ```
- **Line 322**: `rt_true()`
  ```simple
  testing.assert_true(s1.is_subset(s2), "Equal sets are subsets")
  ```
- **Line 334**: `rt_false()`
  ```simple
  testing.assert_false(s1.is_subset(s2), "s1 should not be subset of s2")
  ```
- **Line 347**: `rt_true()`
  ```simple
  testing.assert_true(s1.is_superset(s2), "s1 should be superset of s2")
  ```
- **Line 359**: `rt_false()`
  ```simple
  testing.assert_false(s1.is_superset(s2), "s1 should not be superset of s2")
  ```
- **Line 371**: `rt_true()`
  ```simple
  testing.assert_true(s1.is_disjoint(s2), "Sets should be disjoint")
  ```
- **Line 382**: `rt_false()`
  ```simple
  testing.assert_false(s1.is_disjoint(s2), "Sets should not be disjoint")
  ```
- **Line 394**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 2, "Should have 2 even numbers")
  ```
- **Line 395**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("2"), "Should contain 2")
  ```
- **Line 396**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("4"), "Should contain 4")
  ```
- **Line 404**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 0, "Should be empty")
  ```
- **Line 414**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 3, "Should have 3 elements")
  ```
- **Line 415**: `rt_true()`
  ```simple
  testing.assert_true(result.contains(2), "Should contain 2")
  ```
- **Line 416**: `rt_true()`
  ```simple
  testing.assert_true(result.contains(4), "Should contain 4")
  ```
- **Line 417**: `rt_true()`
  ```simple
  testing.assert_true(result.contains(6), "Should contain 6")
  ```
- **Line 427**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 1, "Should have 1 element after deduplication")
  ```
- **Line 428**: `rt_true()`
  ```simple
  testing.assert_true(result.contains(42), "Should contain 42")
  ```
- **Line 438**: `rt_true()`
  ```simple
  testing.assert_true(result, "Should find element > 2")
  ```
- **Line 447**: `rt_false()`
  ```simple
  testing.assert_false(result, "Should not find element > 10")
  ```
- **Line 452**: `rt_false()`
  ```simple
  testing.assert_false(result, "Empty set should return false")
  ```
- **Line 462**: `rt_true()`
  ```simple
  testing.assert_true(result, "All elements > 0")
  ```
- **Line 471**: `rt_false()`
  ```simple
  testing.assert_false(result, "Not all elements > 1")
  ```
- **Line 476**: `rt_true()`
  ```simple
  testing.assert_true(result, "Empty set should return true (vacuous truth)")
  ```
- **Line 487**: `rt_eq()`
  ```simple
  testing.assert_eq(s1.len(), 2, "Original should have 2 elements")
  ```
- **Line 488**: `rt_eq()`
  ```simple
  testing.assert_eq(s2.len(), 3, "Clone should have 3 elements")
  ```
- **Line 489**: `rt_false()`
  ```simple
  testing.assert_false(s1.contains("Charlie"), "Original should not have Charlie")
  ```
- **Line 496**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 4, "Should have 4 elements")
  ```
- **Line 497**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Bob"), "Should contain Bob")
  ```
- **Line 498**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Charlie"), "Should contain Charlie")
  ```
- **Line 499**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("David"), "Should contain David")
  ```
- **Line 506**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 3, "Should have 3 unique elements")
  ```
- **Line 512**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 3, "Should have 3 unique elements")
  ```
- **Line 513**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Alice"), "Should contain Alice")
  ```
- **Line 514**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Bob"), "Should contain Bob")
  ```
- **Line 515**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Charlie"), "Should contain Charlie")
  ```
- **Line 534**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 1, "Should have 1 common element")
  ```
- **Line 535**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Charlie"), "Should contain Charlie")
  ```
- **Line 539**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 0, "Should be empty")
  ```
- **Line 54**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 0, "New set should be empty")
  ```
- **Line 555**: `rt_eq()`
  ```simple
  testing.assert_eq(result.len(), 4, "Should have 4 unique elements")
  ```
- **Line 556**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Alice"), "Should contain Alice")
  ```
- **Line 557**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Bob"), "Should contain Bob")
  ```
- **Line 558**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("Charlie"), "Should contain Charlie")
  ```
- **Line 559**: `rt_true()`
  ```simple
  testing.assert_true(result.contains("David"), "Should contain David")
  ```
- **Line 55**: `rt_true()`
  ```simple
  testing.assert_true(s.is_empty(), "New set should report empty")
  ```
- **Line 566**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 100, "Should have 100 elements")
  ```
- **Line 578**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 0, "Should be empty after removing all")
  ```
- **Line 585**: `rt_eq()`
  ```simple
  testing.assert_eq(union_result.len(), 0, "Union of empty sets should be empty")
  ```
- **Line 588**: `rt_eq()`
  ```simple
  testing.assert_eq(intersect_result.len(), 0, "Intersection of empty sets should be empty")
  ```
- **Line 590**: `rt_true()`
  ```simple
  testing.assert_true(s1.is_subset(s2), "Empty set is subset of empty set")
  ```
- **Line 591**: `rt_true()`
  ```simple
  testing.assert_true(s1.is_disjoint(s2), "Empty sets are disjoint")
  ```
- **Line 59**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 0, "Set with capacity should be empty")
  ```
- **Line 60**: `rt_true()`
  ```simple
  testing.assert_true(s.is_empty(), "Set with capacity should report empty")
  ```
- **Line 66**: `rt_true()`
  ```simple
  testing.assert_true(inserted, "Should return true for new element")
  ```
- **Line 67**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 1, "Set should have 1 element")
  ```
- **Line 73**: `rt_false()`
  ```simple
  testing.assert_false(inserted, "Should return false for duplicate")
  ```
- **Line 74**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 1, "Set should still have 1 element")
  ```
- **Line 79**: `rt_true()`
  ```simple
  testing.assert_true(s.contains("Alice"), "Should find inserted element")
  ```
- **Line 83**: `rt_false()`
  ```simple
  testing.assert_false(s.contains("Alice"), "Should not find missing element")
  ```
- **Line 89**: `rt_true()`
  ```simple
  testing.assert_true(removed, "Should return true for removed element")
  ```
- **Line 90**: `rt_eq()`
  ```simple
  testing.assert_eq(s.len(), 0, "Set should be empty after removal")
  ```
- **Line 95**: `rt_false()`
  ```simple
  testing.assert_false(removed, "Should return false for missing element")
  ```

#### `test/lib/std/unit/shell/path_spec.spl`

- **Line 91**: `rt_with()`
  ```simple
  expect(result).to_start_with("/")
  ```

#### `test/lib/std/unit/testing/helpers_spec.spl`

- **Line 101**: `rt_ok()`
  ```simple
  val value = helpers.assert_ok(res, "Should be Ok")
  ```
- **Line 102**: `rt_eq()`
  ```simple
  helpers.assert_eq(value, 42, "Should return unwrapped value")
  ```
- **Line 113**: `rt_err()`
  ```simple
  val error = helpers.assert_err(res, "Should be Err")
  ```
- **Line 114**: `rt_eq()`
  ```simple
  helpers.assert_eq(error, "error message", "Should return error value")
  ```
- **Line 132**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, 4950, "Result should be correct")
  ```
- **Line 133**: `rt_true()`
  ```simple
  helpers.assert_true(elapsed > 0, "Elapsed time should be positive")
  ```
- **Line 141**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, 42, "Result should be correct")
  ```
- **Line 142**: `rt_true()`
  ```simple
  helpers.assert_true(elapsed >= 10000, "Should take at least 10ms (10000μs)")
  ```
- **Line 146**: `rt_fast()`
  ```simple
  val result = helpers.assert_fast(
  ```
- **Line 151**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, 42, "Should return result")
  ```
- **Line 166**: `rt_eq()`
  ```simple
  helpers.assert_eq(spy.call_count(), 0, "Should start with 0 calls")
  ```
- **Line 171**: `rt_eq()`
  ```simple
  helpers.assert_eq(spy.call_count(), 1, "Should have 1 call")
  ```
- **Line 180**: `rt_called()`
  ```simple
  helpers.assert_called(mock_fn, 3)
  ```
- **Line 195**: `rt_called_with()`
  ```simple
  helpers.assert_called_with(mock_fn, ["Alice", "Bob"])
  ```
- **Line 208**: `rt_not_called()`
  ```simple
  helpers.assert_not_called(mock_fn)
  ```
- **Line 222**: `rt_contains()`
  ```simple
  helpers.assert_contains(list, "Bob", "Should contain Bob")
  ```
- **Line 234**: `rt_not_contains()`
  ```simple
  helpers.assert_not_contains(list, "David", "Should not contain David")
  ```
- **Line 246**: `rt_empty()`
  ```simple
  helpers.assert_empty(list, "Should be empty")
  ```
- **Line 258**: `rt_len()`
  ```simple
  helpers.assert_len(list, 3, "Should have 3 elements")
  ```
- **Line 278**: `rt_eq()`
  ```simple
  helpers.assert_eq(fixture, "setup_fixture", "Teardown receives fixture")
  ```
- **Line 282**: `rt_eq()`
  ```simple
  helpers.assert_eq(fixture, "setup_fixture", "Test receives fixture")
  ```
- **Line 287**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, "test_result", "Should return test result")
  ```
- **Line 297**: `rt_eq()`
  ```simple
  helpers.assert_eq(fixture[0], "temp_file.txt", "Teardown receives fixture")
  ```
- **Line 301**: `rt_eq()`
  ```simple
  helpers.assert_eq(fixture[0], "temp_file.txt", "Test receives fixture")
  ```
- **Line 305**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, "done", "Should return test result")
  ```
- **Line 314**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, 42, "Should return result")
  ```
- **Line 334**: `rt_true()`
  ```simple
  helpers.assert_true(elapsed >= 0.05, "Should take at least 50ms")
  ```
- **Line 335**: `rt_true()`
  ```simple
  helpers.assert_true(elapsed < 0.2, "Should take less than 200ms")
  ```
- **Line 33**: `rt_eq()`
  ```simple
  helpers.assert_eq(42, 42, "Values should be equal")
  ```
- **Line 342**: `rt_len()`
  ```simple
  helpers.assert_len(list, 3, "Should have 3 elements")
  ```
- **Line 343**: `rt_contains()`
  ```simple
  helpers.assert_contains(list, "Alice", "Should contain Alice")
  ```
- **Line 344**: `rt_contains()`
  ```simple
  helpers.assert_contains(list, "Bob", "Should contain Bob")
  ```
- **Line 345**: `rt_not_contains()`
  ```simple
  helpers.assert_not_contains(list, "David", "Should not contain David")
  ```
- **Line 353**: `rt_some()`
  ```simple
  val value = helpers.assert_some(opt, "Should be Some")
  ```
- **Line 354**: `rt_eq()`
  ```simple
  helpers.assert_eq(value, 42, "Should be 42")
  ```
- **Line 356**: `rt_ok()`
  ```simple
  val msg = helpers.assert_ok(res, "Should be Ok")
  ```
- **Line 357**: `rt_eq()`
  ```simple
  helpers.assert_eq(msg, "success", "Should be success")
  ```
- **Line 368**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, 499500, "Result should be correct")
  ```
- **Line 369**: `rt_true()`
  ```simple
  helpers.assert_true(elapsed > 0, "Should take some time")
  ```
- **Line 372**: `rt_fast()`
  ```simple
  val result = helpers.assert_fast(
  ```
- **Line 383**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, 4950, "Result should be correct")
  ```
- **Line 395**: `rt_called()`
  ```simple
  helpers.assert_called(mock_fn, 3)
  ```
- **Line 396**: `rt_true()`
  ```simple
  helpers.assert_true(mock_fn.was_called(), "Should have been called")
  ```
- **Line 397**: `rt_eq()`
  ```simple
  helpers.assert_eq(mock_fn.call_count(), 3, "Should have 3 call records")
  ```
- **Line 411**: `rt_len()`
  ```simple
  helpers.assert_len(fixture, 2, "Should have 2 elements")
  ```
- **Line 412**: `rt_contains()`
  ```simple
  helpers.assert_contains(fixture, "Alice", "Should contain Alice")
  ```
- **Line 413**: `rt_contains()`
  ```simple
  helpers.assert_contains(fixture, "Bob", "Should contain Bob")
  ```
- **Line 420**: `rt_len()`
  ```simple
  helpers.assert_len(list, 0, "Should be empty")
  ```
- **Line 421**: `rt_empty()`
  ```simple
  helpers.assert_empty(list, "Should be empty")
  ```
- **Line 437**: `rt_eq()`
  ```simple
  helpers.assert_eq(outer_result, 84, "Should be doubled")
  ```
- **Line 438**: `rt_true()`
  ```simple
  helpers.assert_true(outer_elapsed >= 0, "Should be non-negative")
  ```
- **Line 444**: `rt_len()`
  ```simple
  helpers.assert_len(fixture, 1, "Teardown sees fixture")
  ```
- **Line 447**: `rt_len()`
  ```simple
  helpers.assert_len(fixture, 1, "Test sees fixture")
  ```
- **Line 44**: `rt_ne()`
  ```simple
  helpers.assert_ne(42, 43, "Values should be different")
  ```
- **Line 452**: `rt_eq()`
  ```simple
  helpers.assert_eq(0, 0, "Zero should equal zero")
  ```
- **Line 455**: `rt_fast()`
  ```simple
  val result = helpers.assert_fast(
  ```
- **Line 460**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, 42, "Should return result")
  ```
- **Line 464**: `rt_eq()`
  ```simple
  helpers.assert_eq(result, 42, "Should return result")
  ```
- **Line 54**: `rt_true()`
  ```simple
  helpers.assert_true(true, "Condition should be true")
  ```
- **Line 55**: `rt_true()`
  ```simple
  helpers.assert_true(1 + 1 == 2, "Math should work")
  ```
- **Line 65**: `rt_false()`
  ```simple
  helpers.assert_false(false, "Condition should be false")
  ```
- **Line 66**: `rt_false()`
  ```simple
  helpers.assert_false(1 + 1 == 3, "Math should work")
  ```
- **Line 77**: `rt_some()`
  ```simple
  val value = helpers.assert_some(opt, "Should be Some")
  ```
- **Line 78**: `rt_eq()`
  ```simple
  helpers.assert_eq(value, 42, "Should return unwrapped value")
  ```
- **Line 89**: `rt_none()`
  ```simple
  helpers.assert_none(opt, "Should be None")
  ```

#### `test/lib/std/unit/testing/mock_phase4_spec.spl`

- **Line 211**: `rt_chain()`
  ```simple
  me start_chain(parent_id: i32, call: CallRecord) -> i32:
  ```
- **Line 386**: `rt_chain()`
  ```simple
  val id1 = tracker.start_chain(-1, call1)
  ```
- **Line 389**: `rt_chain()`
  ```simple
  val id2 = tracker.start_chain(id1, call2)
  ```
- **Line 398**: `rt_chain()`
  ```simple
  val id = tracker.start_chain(5, call)
  ```
- **Line 405**: `rt_chain()`
  ```simple
  val id1 = tracker.start_chain(-1, call1)
  ```
- **Line 406**: `rt_chain()`
  ```simple
  val id2 = tracker.start_chain(-1, call2)
  ```
- **Line 578**: `rt_chain()`
  ```simple
  val id1 = tracker.start_chain(-1, call1)
  ```
- **Line 579**: `rt_chain()`
  ```simple
  val id2 = tracker.start_chain(id1, call2)
  ```

#### `test/lib/std/unit/testing/mock_phase7_spec.spl`

- **Line 287**: `rt_order()`
  ```simple
  expect tracker.get_start_order().len() == 0
  ```
- **Line 294**: `rt_order()`
  ```simple
  expect tracker.get_start_order().len() == 1
  ```
- **Line 332**: `rt_order()`
  ```simple
  val starts = tracker.get_start_order()
  ```
- **Line 340**: `rt_order()`
  ```simple
  expect tracker.get_start_order().len() == 0
  ```

#### `test/lib/std/unit/tooling/config_ffi_spec.spl`

- **Line 100**: `rt_is_macro_trace_enabled()`
  ```simple
  assert not rt_is_macro_trace_enabled()
  ```
- **Line 101**: `rt_is_debug_mode_enabled()`
  ```simple
  assert rt_is_debug_mode_enabled()
  ```
- **Line 104**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(false)
  ```
- **Line 39**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(true)
  ```
- **Line 40**: `rt_is_macro_trace_enabled()`
  ```simple
  expect rt_is_macro_trace_enabled() == true
  ```
- **Line 41**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(false)
  ```
- **Line 66**: `rt_is_macro_trace_enabled()`
  ```simple
  assert not rt_is_macro_trace_enabled()
  ```
- **Line 69**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(true)
  ```
- **Line 70**: `rt_is_macro_trace_enabled()`
  ```simple
  assert rt_is_macro_trace_enabled()
  ```
- **Line 73**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(false)
  ```
- **Line 74**: `rt_is_macro_trace_enabled()`
  ```simple
  assert not rt_is_macro_trace_enabled()
  ```
- **Line 78**: `rt_is_debug_mode_enabled()`
  ```simple
  assert not rt_is_debug_mode_enabled()
  ```
- **Line 81**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(true)
  ```
- **Line 82**: `rt_is_debug_mode_enabled()`
  ```simple
  assert rt_is_debug_mode_enabled()
  ```
- **Line 85**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(false)
  ```
- **Line 86**: `rt_is_debug_mode_enabled()`
  ```simple
  assert not rt_is_debug_mode_enabled()
  ```
- **Line 90**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(true)
  ```
- **Line 91**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(false)
  ```
- **Line 93**: `rt_is_macro_trace_enabled()`
  ```simple
  assert rt_is_macro_trace_enabled()
  ```
- **Line 94**: `rt_is_debug_mode_enabled()`
  ```simple
  assert not rt_is_debug_mode_enabled()
  ```
- **Line 97**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(false)
  ```
- **Line 98**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(true)
  ```

#### `test/lib/std/unit/tooling/test_db_concurrency_spec.spl`

- **Line 322**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(lock_file, "999999")  # Non-existent PID
  ```
- **Line 87**: `rt_file_write_text()`
  ```simple
  rt_file_write_text(script_path, script_content)
  ```

#### `test/lib/std/unit/tooling/test_runner_simple_spec.spl`

- **Line 210**: `rt_process_run_timeout()`
  ```simple
  Uses `rt_process_run_timeout(cmd, args, timeout_ms)` which returns
  ```
- **Line 24**: `rt_process_run_timeout()`
  ```simple
  | Timeout | `rt_process_run_timeout(cmd, args, timeout_ms)` returns exit_code=-1 on timeout |
  ```

#### `test/lib/std/unit/ui/tui/ratatui_backend_spec.spl`

- **Line 164**: `rt_char()`
  ```simple
  buf.insert_char("a")
  ```
- **Line 165**: `rt_char()`
  ```simple
  buf.insert_char("b")
  ```
- **Line 166**: `rt_char()`
  ```simple
  buf.insert_char("c")
  ```
- **Line 183**: `rt_newline()`
  ```simple
  buf.insert_newline()
  ```
- **Line 184**: `rt_char()`
  ```simple
  buf.insert_char("2")
  ```
- **Line 252**: `rt_char()`
  ```simple
  buf.insert_char("x")
  ```
- **Line 46**: `rt_char()`
  ```simple
  me insert_char(c: text) -> ():
  ```
- **Line 55**: `rt_newline()`
  ```simple
  me insert_newline() -> ()
  ```

#### `test/lib/std/unit/ui/vulkan_phase1_validation.spl`

- **Line 361**: `rt_vk_device_create()`
  ```simple
  val device_handle = rt_vk_device_create()
  ```
- **Line 369**: `rt_vk_buffer_alloc()`
  ```simple
  val buffer_handle = rt_vk_buffer_alloc(device_handle, 4096)
  ```
- **Line 372**: `rt_vk_device_free()`
  ```simple
  rt_vk_device_free(device_handle)
  ```
- **Line 378**: `rt_vk_device_sync()`
  ```simple
  val sync_result = rt_vk_device_sync(device_handle)
  ```
- **Line 385**: `rt_vk_buffer_free()`
  ```simple
  val buf_result = rt_vk_buffer_free(buffer_handle)
  ```
- **Line 386**: `rt_vk_device_free()`
  ```simple
  val dev_result = rt_vk_device_free(device_handle)
  ```

#### `test/specs/async_default_spec.spl`

- **Line 325**: `rt_background_task()`
  ```simple
  sync fn start_background_task(id: TaskId):
  ```

#### `test/specs/metaprogramming_spec.spl`

- **Line 121**: `rt_eq()`
  ```simple
  assert_eq(1 + 1, 2)
  ```

#### `test/specs/suspension_operator_spec.spl`

- **Line 254**: `rt_fetch()`
  ```simple
  fn smart_fetch(id: UserId, use_cache: bool) -> User:
  ```
- **Line 79**: `rt_processing()`
  ```simple
  start_processing()
  ```

#### `test/system/db_sdn_spec.spl`

- **Line 20**: `rt_table_sdn()`
  ```simple
  db.export_table_sdn("users", "users.sdn")
  ```
- **Line 21**: `rt_table_sdn()`
  ```simple
  db.import_table_sdn("users", "users.sdn")
  ```
- **Line 27**: `rt_table_sdn()`
  ```simple
  fn export_table_sdn(table: str, path: str):
  ```
- **Line 30**: `rt_table_sdn()`
  ```simple
  fn import_table_sdn(table: str, path: str) -> i64:
  ```
- **Line 42**: `rt_users()`
  ```simple
  fn export_users(db: Database):
  ```
- **Line 43**: `rt_table_sdn()`
  ```simple
  db.export_table_sdn("users", "users.sdn")
  ```
- **Line 57**: `rt_users()`
  ```simple
  fn import_users(db: Database) -> i64:
  ```
- **Line 58**: `rt_table_sdn()`
  ```simple
  return db.import_table_sdn("users", "users.sdn")
  ```

#### `test/system/features/async_file_io/async_file_io_spec.spl`

- **Line 32**: `rt_loading()`
  ```simple
  async_file_start_loading(handle)
  ```

#### `test/system/features/database_synchronization/database_sync_spec.spl`

- **Line 872**: `rt_file_exists()`
  ```simple
  rt_file_exists(path)
  ```
- **Line 876**: `rt_file_read_text()`
  ```simple
  val result = rt_file_read_text(path)
  ```
- **Line 883**: `rt_file_atomic_write()`
  ```simple
  rt_file_atomic_write(path, content)
  ```
- **Line 887**: `rt_current_time_ms()`
  ```simple
  rt_current_time_ms()
  ```

#### `test/system/features/database_synchronization/helpers.spl`

- **Line 60**: `rt_file_exists()`
  ```simple
  rt_file_exists(path)
  ```
- **Line 64**: `rt_file_read_text()`
  ```simple
  rt_file_read_text(path)
  ```
- **Line 68**: `rt_file_atomic_write()`
  ```simple
  rt_file_atomic_write(path, content)
  ```
- **Line 72**: `rt_current_time_ms()`
  ```simple
  rt_current_time_ms()
  ```

#### `test/system/features/extern_functions/extern_functions_spec.spl`

- **Line 112**: `rt_math_sqrt()`
  ```simple
  val r1 = rt_math_sqrt(16.0)
  ```
- **Line 113**: `rt_math_sqrt()`
  ```simple
  val r2 = rt_math_sqrt(16.0)
  ```
- **Line 36**: `rt_math_sqrt()`
  ```simple
  val result = rt_math_sqrt(16.0)
  ```
- **Line 47**: `rt_math_pow()`
  ```simple
  val result = rt_math_pow(2.0, 3.0)
  ```
- **Line 51**: `rt_math_sqrt()`
  ```simple
  val result = rt_math_sqrt(25.0)
  ```
- **Line 73**: `rt_math_sqrt()`
  ```simple
  val result = rt_math_sqrt(9.0)
  ```
- **Line 89**: `rt_math_sqrt()`
  ```simple
  val result = rt_math_sqrt(-1.0)
  ```

#### `test/system/features/fault_detection/fault_detection_spec.spl`

- **Line 101**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(true)
  ```
- **Line 106**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(false)
  ```
- **Line 109**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(true)
  ```
- **Line 113**: `rt_fault_set_max_recursion_depth()`
  ```simple
  rt_fault_set_max_recursion_depth(100)
  ```
- **Line 116**: `rt_fault_set_max_recursion_depth()`
  ```simple
  rt_fault_set_max_recursion_depth(1000)
  ```
- **Line 119**: `rt_fault_set_max_recursion_depth()`
  ```simple
  rt_fault_set_max_recursion_depth(50000)
  ```
- **Line 122**: `rt_fault_set_max_recursion_depth()`
  ```simple
  rt_fault_set_max_recursion_depth(1000)
  ```
- **Line 126**: `rt_fault_set_timeout()`
  ```simple
  rt_fault_set_timeout(0)
  ```
- **Line 131**: `rt_fault_set_timeout()`
  ```simple
  rt_fault_set_timeout(60)
  ```
- **Line 134**: `rt_fault_set_timeout()`
  ```simple
  rt_fault_set_timeout(0)
  ```
- **Line 138**: `rt_fault_set_execution_limit()`
  ```simple
  rt_fault_set_execution_limit(1000000)
  ```
- **Line 143**: `rt_fault_set_execution_limit()`
  ```simple
  rt_fault_set_execution_limit(0)
  ```
- **Line 90**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(true)
  ```
- **Line 91**: `rt_fault_set_max_recursion_depth()`
  ```simple
  rt_fault_set_max_recursion_depth(1000)
  ```
- **Line 96**: `rt_fault_set_stack_overflow_detection()`
  ```simple
  rt_fault_set_stack_overflow_detection(true)
  ```

#### `test/system/features/ffi/rust_simple_ffi_spec.spl`

- **Line 131**: `rt_value_int()`
  ```simple
  val rv = rt_value_int(42)
  ```
- **Line 132**: `rt_value_as_int()`
  ```simple
  val result = rt_value_as_int(rv)
  ```
- **Line 136**: `rt_value_int()`
  ```simple
  val rv = rt_value_int(-100)
  ```
- **Line 137**: `rt_value_as_int()`
  ```simple
  val result = rt_value_as_int(rv)
  ```
- **Line 141**: `rt_value_int()`
  ```simple
  val rv = rt_value_int(0)
  ```
- **Line 142**: `rt_value_as_int()`
  ```simple
  val result = rt_value_as_int(rv)
  ```
- **Line 147**: `rt_value_float()`
  ```simple
  val rv = rt_value_float(3.14)
  ```
- **Line 148**: `rt_value_as_float()`
  ```simple
  val result = rt_value_as_float(rv)
  ```
- **Line 153**: `rt_value_bool()`
  ```simple
  val rv = rt_value_bool(true)
  ```
- **Line 154**: `rt_value_as_bool()`
  ```simple
  val result = rt_value_as_bool(rv)
  ```
- **Line 158**: `rt_value_bool()`
  ```simple
  val rv = rt_value_bool(false)
  ```
- **Line 159**: `rt_value_as_bool()`
  ```simple
  val result = rt_value_as_bool(rv)
  ```
- **Line 164**: `rt_value_nil()`
  ```simple
  val rv = rt_value_nil()
  ```
- **Line 165**: `rt_value_is_nil()`
  ```simple
  expect(rt_value_is_nil(rv)).to(eq(true))
  ```
- **Line 168**: `rt_value_int()`
  ```simple
  val rv = rt_value_int(42)
  ```
- **Line 169**: `rt_value_is_nil()`
  ```simple
  expect(rt_value_is_nil(rv)).to(eq(false))
  ```
- **Line 185**: `rt_array_new()`
  ```simple
  val arr = rt_array_new(10)
  ```
- **Line 186**: `rt_array_len()`
  ```simple
  expect(rt_array_len(arr)).to(eq(0))
  ```
- **Line 190**: `rt_array_new()`
  ```simple
  val arr = rt_array_new(10)
  ```
- **Line 191**: `rt_array_push()`
  ```simple
  rt_array_push(arr, rt_value_int(42))
  ```
- **Line 192**: `rt_array_push()`
  ```simple
  rt_array_push(arr, rt_value_int(100))
  ```
- **Line 194**: `rt_array_get()`
  ```simple
  val first = rt_array_get(arr, 0)
  ```
- **Line 195**: `rt_array_get()`
  ```simple
  val second = rt_array_get(arr, 1)
  ```
- **Line 197**: `rt_value_as_int()`
  ```simple
  expect(rt_value_as_int(first)).to(eq(42))
  ```
- **Line 198**: `rt_value_as_int()`
  ```simple
  expect(rt_value_as_int(second)).to(eq(100))
  ```
- **Line 201**: `rt_array_new()`
  ```simple
  val arr = rt_array_new(10)
  ```
- **Line 202**: `rt_array_push()`
  ```simple
  rt_array_push(arr, rt_value_int(1))
  ```
- **Line 203**: `rt_array_set()`
  ```simple
  rt_array_set(arr, 0, rt_value_int(999))
  ```
- **Line 205**: `rt_array_get()`
  ```simple
  val result = rt_array_get(arr, 0)
  ```
- **Line 206**: `rt_value_as_int()`
  ```simple
  expect(rt_value_as_int(result)).to(eq(999))
  ```
- **Line 209**: `rt_array_new()`
  ```simple
  val arr = rt_array_new(10)
  ```
- **Line 210**: `rt_array_push()`
  ```simple
  rt_array_push(arr, rt_value_int(1))
  ```
- **Line 211**: `rt_array_push()`
  ```simple
  rt_array_push(arr, rt_value_int(2))
  ```
- **Line 213**: `rt_array_pop()`
  ```simple
  val popped = rt_array_pop(arr)
  ```
- **Line 214**: `rt_value_as_int()`
  ```simple
  expect(rt_value_as_int(popped)).to(eq(2))
  ```
- **Line 215**: `rt_array_len()`
  ```simple
  expect(rt_array_len(arr)).to(eq(1))
  ```
- **Line 218**: `rt_array_new()`
  ```simple
  val arr = rt_array_new(10)
  ```
- **Line 219**: `rt_array_push()`
  ```simple
  rt_array_push(arr, rt_value_int(1))
  ```
- **Line 220**: `rt_array_push()`
  ```simple
  rt_array_push(arr, rt_value_int(2))
  ```
- **Line 222**: `rt_array_clear()`
  ```simple
  rt_array_clear(arr)
  ```
- **Line 223**: `rt_array_len()`
  ```simple
  expect(rt_array_len(arr)).to(eq(0))
  ```
- **Line 239**: `rt_dict_new()`
  ```simple
  val dict = rt_dict_new()
  ```
- **Line 240**: `rt_dict_len()`
  ```simple
  expect(rt_dict_len(dict)).to(eq(0))
  ```
- **Line 244**: `rt_dict_new()`
  ```simple
  val dict = rt_dict_new()
  ```
- **Line 245**: `rt_string_new()`
  ```simple
  val key = rt_string_new("name")
  ```
- **Line 246**: `rt_string_new()`
  ```simple
  val value = rt_string_new("Alice")
  ```
- **Line 248**: `rt_dict_set()`
  ```simple
  rt_dict_set(dict, key, value)
  ```
- **Line 249**: `rt_dict_get()`
  ```simple
  val result = rt_dict_get(dict, key)
  ```
- **Line 251**: `rt_string_eq()`
  ```simple
  expect(rt_string_eq(result, value)).to(eq(true))
  ```
- **Line 254**: `rt_dict_new()`
  ```simple
  val dict = rt_dict_new()
  ```
- **Line 255**: `rt_dict_set()`
  ```simple
  rt_dict_set(dict, rt_string_new("a"), rt_value_int(1))
  ```
- **Line 256**: `rt_dict_set()`
  ```simple
  rt_dict_set(dict, rt_string_new("b"), rt_value_int(2))
  ```
- **Line 258**: `rt_dict_len()`
  ```simple
  expect(rt_dict_len(dict)).to(eq(2))
  ```
- **Line 273**: `rt_string_new()`
  ```simple
  val s = rt_string_new("Hello")
  ```
- **Line 274**: `rt_string_len()`
  ```simple
  expect(rt_string_len(s)).to(eq(5))
  ```
- **Line 277**: `rt_string_new()`
  ```simple
  val a = rt_string_new("Hello, ")
  ```
- **Line 278**: `rt_string_new()`
  ```simple
  val b = rt_string_new("World!")
  ```
- **Line 279**: `rt_string_concat()`
  ```simple
  val result = rt_string_concat(a, b)
  ```
- **Line 281**: `rt_string_len()`
  ```simple
  expect(rt_string_len(result)).to(eq(13))
  ```
- **Line 297**: `rt_math_sin()`
  ```simple
  val result = rt_math_sin(0.0)
  ```
- **Line 301**: `rt_math_cos()`
  ```simple
  val result = rt_math_cos(0.0)
  ```
- **Line 306**: `rt_math_pow()`
  ```simple
  val result = rt_math_pow(2.0, 3.0)
  ```
- **Line 310**: `rt_math_sqrt()`
  ```simple
  val result = rt_math_sqrt(16.0)
  ```
- **Line 326**: `rt_env_home()`
  ```simple
  val home = rt_env_home()
  ```
- **Line 327**: `rt_value_is_nil()`
  ```simple
  expect(rt_value_is_nil(home)).to(eq(false))
  ```
- **Line 330**: `rt_env_temp()`
  ```simple
  val temp = rt_env_temp()
  ```
- **Line 331**: `rt_value_is_nil()`
  ```simple
  expect(rt_value_is_nil(temp)).to(eq(false))
  ```
- **Line 337**: `rt_env_set()`
  ```simple
  rt_env_set(name, value)
  ```
- **Line 338**: `rt_env_exists()`
  ```simple
  expect(rt_env_exists(name)).to(eq(true))
  ```
- **Line 341**: `rt_env_remove()`
  ```simple
  rt_env_remove(name)
  ```
- **Line 342**: `rt_env_exists()`
  ```simple
  expect(rt_env_exists(name)).to(eq(false))
  ```
- **Line 357**: `rt_is_debug_mode_enabled()`
  ```simple
  val original = rt_is_debug_mode_enabled()
  ```
- **Line 359**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(true)
  ```
- **Line 360**: `rt_is_debug_mode_enabled()`
  ```simple
  expect(rt_is_debug_mode_enabled()).to(eq(true))
  ```
- **Line 362**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(false)
  ```
- **Line 363**: `rt_is_debug_mode_enabled()`
  ```simple
  expect(rt_is_debug_mode_enabled()).to(eq(false))
  ```
- **Line 366**: `rt_set_debug_mode()`
  ```simple
  rt_set_debug_mode(original)
  ```
- **Line 369**: `rt_is_macro_trace_enabled()`
  ```simple
  val original = rt_is_macro_trace_enabled()
  ```
- **Line 371**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(true)
  ```
- **Line 372**: `rt_is_macro_trace_enabled()`
  ```simple
  expect(rt_is_macro_trace_enabled()).to(eq(true))
  ```
- **Line 374**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(false)
  ```
- **Line 375**: `rt_is_macro_trace_enabled()`
  ```simple
  expect(rt_is_macro_trace_enabled()).to(eq(false))
  ```
- **Line 378**: `rt_set_macro_trace()`
  ```simple
  rt_set_macro_trace(original)
  ```
- **Line 393**: `rt_value_int()`
  ```simple
  val rv = rt_value_int(42)
  ```
- **Line 394**: `rt_value_type_tag()`
  ```simple
  val tag = rt_value_type_tag(rv)
  ```
- **Line 398**: `rt_value_float()`
  ```simple
  val rv = rt_value_float(3.14)
  ```
- **Line 399**: `rt_value_type_tag()`
  ```simple
  val tag = rt_value_type_tag(rv)
  ```
- **Line 403**: `rt_value_nil()`
  ```simple
  val rv = rt_value_nil()
  ```
- **Line 404**: `rt_value_type_tag()`
  ```simple
  val tag = rt_value_type_tag(rv)
  ```
- **Line 420**: `rt_function_not_found()`
  ```simple
  val error = rt_function_not_found("nonexistent_function")
  ```
- **Line 421**: `rt_is_error()`
  ```simple
  expect(rt_is_error(error)).to(eq(true))
  ```
- **Line 424**: `rt_method_not_found()`
  ```simple
  val error = rt_method_not_found("SomeType", "missing_method")
  ```
- **Line 425**: `rt_is_error()`
  ```simple
  expect(rt_is_error(error)).to(eq(true))
  ```

#### `test/system/features/module_loader/module_loader_spec.spl`

- **Line 176**: `rt_resolution()`
  ```simple
  fn test_import_resolution() -> bool
  ```
- **Line 180**: `rt_resolution()`
  ```simple
  expect test_import_resolution()
  ```

#### `test/system/features/no_paren_calls/no_paren_calls_spec.spl`

- **Line 75**: `rt_argument()`
  ```simple
  - `can_start_argument()` - Checks if token can begin an argument
  ```

#### `test/system/features/type_inference/dyn_trait_spec.spl`

- **Line 111**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 136**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 162**: `rt_dispatch_mode()`
  ```simple
  assert_dispatch_mode(serializer, "Static")
  ```
- **Line 163**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 188**: `rt_dispatch_mode()`
  ```simple
  assert_dispatch_mode(serializer, "Dynamic")
  ```
- **Line 189**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 239**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 267**: `rt_type()`
  ```simple
  assert_type(value) == "i64"
  ```
- **Line 268**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 271**: `rt_type_checks()`
  ```simple
  fn assert_type_checks()
  ```
- **Line 279**: `rt_dispatch_mode()`
  ```simple
  fn assert_dispatch_mode(obj, mode: str):
  ```
- **Line 283**: `rt_type()`
  ```simple
  fn assert_type(value) -> str
  ```
- **Line 35**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 80**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```

#### `test/system/features/type_inference/transitive_mixin_spec.spl`

- **Line 101**: `rt_has_field()`
  ```simple
  assert_has_field(doc, "id")
  ```
- **Line 103**: `rt_has_field()`
  ```simple
  assert_has_field(doc, "created_at")
  ```
- **Line 104**: `rt_has_field()`
  ```simple
  assert_has_field(doc, "updated_at")
  ```
- **Line 106**: `rt_has_field()`
  ```simple
  assert_has_field(doc, "version")
  ```
- **Line 108**: `rt_has_field()`
  ```simple
  assert_has_field(doc, "title")
  ```
- **Line 109**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 133**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "id")
  ```
- **Line 135**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "left_field")
  ```
- **Line 137**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "right_field")
  ```
- **Line 139**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "own_field")
  ```
- **Line 142**: `rt_field_count()`
  ```simple
  assert_field_count(obj, "id") == 1
  ```
- **Line 143**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 182**: `rt_type()`
  ```simple
  assert_type(entity_id) == "i64"
  ```
- **Line 183**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 211**: `rt_type()`
  ```simple
  assert_type(info) == "str"
  ```
- **Line 212**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 243**: `rt_field_count()`
  ```simple
  assert_field_count(obj, "root_id") == 1
  ```
- **Line 246**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "root_id")    # Root
  ```
- **Line 247**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "a_field")    # A
  ```
- **Line 248**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "b_field")    # B
  ```
- **Line 249**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "c_field")    # C
  ```
- **Line 250**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "d_field")    # D
  ```
- **Line 251**: `rt_has_field()`
  ```simple
  assert_has_field(obj, "own_field")  # Complex
  ```
- **Line 253**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 281**: `rt_type()`
  ```simple
  assert_type(container.id) == "str"
  ```
- **Line 282**: `rt_type()`
  ```simple
  assert_type(container.items) == "[str]"
  ```
- **Line 283**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 330**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 340**: `rt_has_field()`
  ```simple
  fn assert_has_field(obj, field_name: str):
  ```
- **Line 344**: `rt_field_count()`
  ```simple
  fn assert_field_count(obj, field_name: str) -> i64:
  ```
- **Line 348**: `rt_type()`
  ```simple
  fn assert_type(value) -> str
  ```
- **Line 352**: `rt_type_checks()`
  ```simple
  fn assert_type_checks()
  ```
- **Line 38**: `rt_has_field()`
  ```simple
  assert_has_field(user, "created_at")
  ```
- **Line 39**: `rt_has_field()`
  ```simple
  assert_has_field(user, "updated_at")
  ```
- **Line 40**: `rt_has_field()`
  ```simple
  assert_has_field(user, "name")
  ```
- **Line 41**: `rt_has_field()`
  ```simple
  assert_has_field(user, "email")
  ```
- **Line 42**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```
- **Line 65**: `rt_has_field()`
  ```simple
  assert_has_field(article, "id")
  ```
- **Line 67**: `rt_has_field()`
  ```simple
  assert_has_field(article, "created_at")
  ```
- **Line 68**: `rt_has_field()`
  ```simple
  assert_has_field(article, "updated_at")
  ```
- **Line 70**: `rt_has_field()`
  ```simple
  assert_has_field(article, "title")
  ```
- **Line 71**: `rt_has_field()`
  ```simple
  assert_has_field(article, "content")
  ```
- **Line 72**: `rt_type_checks()`
  ```simple
  assert_type_checks()
  ```

#### `test/system/mixin_spec.spl`

- **Line 320**: `rt_fails_with()`
  ```simple
  assert_fails_with("field 'id' conflicts")
  ```
- **Line 342**: `rt_fails_with()`
  ```simple
  assert_fails_with("method 'log' is ambiguous")
  ```
- **Line 373**: `rt_fails_with()`
  ```simple
  fn assert_fails_with(msg: str):
  ```

#### `test/system/static_polymorphism_spec.spl`

- **Line 242**: `rt_fails_with()`
  ```simple
  assert_fails_with("type mismatch")
  ```
- **Line 371**: `rt_fails_with()`
  ```simple
  fn assert_fails_with(msg: str):
  ```

## Wrapper Functions Found

The following wrapper functions were detected:

- `abort_after()` → wraps `rt_after()`
- `absolute()` → wraps `rt_path_absolute()`
- `acos()` → wraps `rt_math_acos()`
- `all_gather()` → wraps `rt_torch_dist_all_gather()`
- `all_reduce()` → wraps `rt_torch_dist_all_reduce()`
- `all()` → wraps `rt_args_all()`
- `all()` → wraps `rt_env_all()`
- `apply_collected_fixes()` → wraps `rt_by()`
- `apply_config()` → wraps `rt_fault_set_stack_overflow_detection()`
- `apply_fixes()` → wraps `rt_by()`
- `apply_sandbox()` → wraps `rt_sandbox_reset()`
- `apply_to_disk()` → wraps `rt_file_write_text()`
- `archive_module()` → wraps `rt_items()`
- `args()` → wraps `rt_args_all()`
- `asin()` → wraps `rt_math_asin()`
- `assert_eq()` → wraps `rt_eq()`
- `assert_false()` → wraps `rt_false()`
- `assert_not_null()` → wraps `rt_not_null()`
- `assert_true()` → wraps `rt_true()`
- `atan()` → wraps `rt_math_atan()`
- `atomic_read_file()` → wraps `rt_file_exists()`
- `atomic_update_file()` → wraps `rt_file_exists()`
- `atomic_write_file_locked()` → wraps `rt_file_atomic_write()`
- `available_parallelism()` → wraps `rt_thread_available_parallelism()`
- `barrier()` → wraps `rt_torch_dist_barrier()`
- `basename()` → wraps `rt_path_basename()`
- `binary_search_insert_pos()` → wraps `rt_pos()`
- `bootstrap_test()` → wraps `rt_exec()`
- `broadcast()` → wraps `rt_torch_dist_broadcast()`
- `btreemap_contains()` → wraps `rt_btreemap_contains()`
- `btreemap_free()` → wraps `rt_btreemap_free()`
- `btreemap_get()` → wraps `rt_btreemap_get()`
- `btreemap_insert()` → wraps `rt_btreemap_insert()`
- `btreemap_keys()` → wraps `rt_btreemap_keys()`
- `btreemap_len()` → wraps `rt_btreemap_len()`
- `btreemap_new()` → wraps `rt_btreemap_new()`
- `btreemap_remove()` → wraps `rt_btreemap_remove()`
- `canonicalize()` → wraps `rt_file_canonicalize()`
- `capture_after_ffi()` → wraps `rt_screenshot_capture_after_terminal()`
- `capture_before_ffi()` → wraps `rt_screenshot_capture_before_terminal()`
- `cargo_build()` → wraps `rt_cargo_build()`
- `cargo_check()` → wraps `rt_cargo_check()`
- `cargo_clean()` → wraps `rt_cargo_clean()`
- `cargo_fmt()` → wraps `rt_cargo_fmt()`
- `cargo_lint()` → wraps `rt_cargo_lint()`
- `cargo_test_doc()` → wraps `rt_cargo_test_doc()`
- `cargo_test()` → wraps `rt_cargo_test()`
- `ceil()` → wraps `rt_math_ceil()`
- `check_file_path()` → wraps `rt_check_file_path()`
- `check_onnx()` → wraps `rt_onnx()`
- `checkpoint()` → wraps `rt_torch_checkpoint()`
- `clamp()` → wraps `rt_torch_clamp()`
- `cleanup_lock_files()` → wraps `rt_dir_glob()`
- `cleanup_temp_files()` → wraps `rt_dir_glob()`
- `clear_ffi_captures()` → wraps `rt_screenshot_clear_captures()`
- `clear_ffi_recording()` → wraps `rt_diagram_clear()`
- `clear_ffi_test_context()` → wraps `rt_screenshot_clear_context()`
- `cli_check()` → wraps `rt_cli_run_check()`
- `cli_compile()` → wraps `rt_cli_handle_compile()`
- `cli_constr()` → wraps `rt_cli_run_constr()`
- `cli_exit()` → wraps `rt_cli_exit()`
- `cli_file_exists()` → wraps `rt_cli_file_exists()`
- `cli_gen_lean()` → wraps `rt_cli_run_gen_lean()`
- `cli_get_args()` → wraps `rt_cli_get_args()`
- `cli_handle_diagram()` → wraps `rt_cli_handle_diagram()`
- `cli_handle_linkers()` → wraps `rt_cli_handle_linkers()`
- `cli_handle_run()` → wraps `rt_cli_handle_run()`
- `cli_handle_web()` → wraps `rt_cli_handle_web()`
- `cli_info()` → wraps `rt_cli_run_info()`
- `cli_module()` → wraps `rt_items()`
- `clip_grad_norm()` → wraps `rt_torch_clip_grad_norm()`
- `clip_grad_value()` → wraps `rt_torch_clip_grad_value()`
- `cli_read_file()` → wraps `rt_cli_read_file()`
- `cli_replay()` → wraps `rt_cli_run_replay()`
- `cli_run_brief()` → wraps `rt_cli_run_brief()`
- `cli_run_code()` → wraps `rt_cli_run_code()`
- `cli_run_diff()` → wraps `rt_cli_run_diff()`
- `cli_run_feature_gen()` → wraps `rt_cli_run_feature_gen()`
- `cli_run_ffi_gen()` → wraps `rt_cli_run_ffi_gen()`
- `cli_run_file()` → wraps `rt_cli_run_file()`
- `cli_run_fix()` → wraps `rt_cli_run_fix()`
- `cli_run_fmt()` → wraps `rt_cli_run_fmt()`
- `cli_run_lex()` → wraps `rt_cli_run_lex()`
- `cli_run_lint()` → wraps `rt_cli_run_lint()`
- `cli_run_mcp()` → wraps `rt_cli_run_mcp()`
- `cli_run_migrate()` → wraps `rt_cli_run_migrate()`
- `cli_run_query()` → wraps `rt_cli_run_query()`
- `cli_run_repl()` → wraps `rt_cli_run_repl()`
- `cli_run_spec_coverage()` → wraps `rt_cli_run_spec_coverage()`
- `cli_run_spec_gen()` → wraps `rt_cli_run_spec_gen()`
- `cli_run_sspec_docgen()` → wraps `rt_cli_run_sspec_docgen()`
- `cli_run_task_gen()` → wraps `rt_cli_run_task_gen()`
- `cli_run_tests()` → wraps `rt_cli_run_tests()`
- `cli_run_todo_gen()` → wraps `rt_cli_run_todo_gen()`
- `cli_run_verify()` → wraps `rt_cli_run_verify()`
- `cli_todo_scan()` → wraps `rt_cli_run_todo_scan()`
- `cli_watch_file()` → wraps `rt_cli_watch_file()`
- `close_file()` → wraps `rt_file_close()`
- `cmd_run()` → wraps `rt_run()`
- `coco_classes()` → wraps `rt_torch_vision_imagenet_count()`
- `codegen_module()` → wraps `rt_items()`
- `collate_tensors()` → wraps `rt_torch_mnist_download()`
- `collect_spl_files()` → wraps `rt_walk_directory()`
- `concurrent_module()` → wraps `rt_parallel_map()`
- `constant()` → wraps `rt_torch_init_constant()`
- `context_generate()` → wraps `rt_context_generate()`
- `context_stats()` → wraps `rt_context_stats()`
- `convert_arguments()` → wraps `rt_arguments()`
- `convert_array_literal()` → wraps `rt_array_literal()`
- `convert_binary_expression()` → wraps `rt_binary_expression()`
- `convert_block()` → wraps `rt_block()`
- `convert_call_expression()` → wraps `rt_call_expression()`
- `convert_case_clause()` → wraps `rt_case_clause()`
- `convert_dict_entry()` → wraps `rt_dict_entry()`
- `convert_dict_literal()` → wraps `rt_dict_literal()`
- `convert_enum_def()` → wraps `rt_enum_def()`
- `convert_enum_pattern()` → wraps `rt_enum_pattern()`
- `convert_enum_variant()` → wraps `rt_enum_variant()`
- `convert_expression()` → wraps `rt_expression()`
- `convert_field_expression()` → wraps `rt_field_expression()`
- `convert_field_pattern()` → wraps `rt_field_pattern()`
- `convert_for_statement()` → wraps `rt_for_statement()`
- `convert_function_def()` → wraps `rt_function_def()`
- `convert_if_expression()` → wraps `rt_if_expression()`
- `convert_if_statement()` → wraps `rt_if_statement()`
- `convert_impl_def()` → wraps `rt_impl_def()`
- `convert_import()` → wraps `rt_import()`
- `convert_index_expression()` → wraps `rt_index_expression()`
- `convert_key_code()` → wraps `rt_key_code()`
- `convert_key_event()` → wraps `rt_key_event()`
- `convert_lambda_params()` → wraps `rt_lambda_params()`
- `convert_lambda()` → wraps `rt_lambda()`
- `convert_let_statement()` → wraps `rt_let_statement()`
- `convert_literal()` → wraps `rt_literal()`
- `convert_loop_statement()` → wraps `rt_loop_statement()`
- `convert_match_arm()` → wraps `rt_match_arm()`
- `convert_match_expression()` → wraps `rt_match_expression()`
- `convert_match_statement()` → wraps `rt_match_statement()`
- `convert_method_call()` → wraps `rt_method_call()`
- `convert_mouse_event()` → wraps `rt_mouse_event()`
- `convert_parameters()` → wraps `rt_parameters()`
- `convert_parameter()` → wraps `rt_parameter()`
- `convert_pattern()` → wraps `rt_pattern()`
- `convert_range_expression()` → wraps `rt_range_expression()`
- `convert_return_statement()` → wraps `rt_return_statement()`
- `convert_statement()` → wraps `rt_statement()`
- `convert_struct_def()` → wraps `rt_struct_def()`
- `convert_struct_field()` → wraps `rt_struct_field()`
- `convert_struct_pattern()` → wraps `rt_struct_pattern()`
- `convert_test_name_to_symbols()` → wraps `rt_test_name_to_symbols()`
- `convert_to_dashboard_todo()` → wraps `rt_to_dashboard_todo()`
- `convert_tuple_literal()` → wraps `rt_tuple_literal()`
- `convert_unary_expression()` → wraps `rt_unary_expression()`
- `convert_variant_fields()` → wraps `rt_variant_fields()`
- `convert_var_statement()` → wraps `rt_var_statement()`
- `convert_while_statement()` → wraps `rt_while_statement()`
- `copy_dir()` → wraps `rt_dir_create()`
- `copy_file()` → wraps `rt_package_copy_file()`
- `copy_source()` → wraps `rt_file_exists()`
- `copy_strategy()` → wraps `rt_by()`
- `copy()` → wraps `rt_file_copy()`
- `cos()` → wraps `rt_math_cos()`
- `_cos()` → wraps `rt_torch_cos()`
- `count()` → wraps `rt_args_count()`
- `coverage_clear()` → wraps `rt_coverage_clear()`
- `coverage_dump_sdn()` → wraps `rt_coverage_dump_sdn()`
- `coverage_enabled()` → wraps `rt_coverage_enabled()`
- `cpu_count()` → wraps `rt_system_cpu_count()`
- `cranelift_append_block_param()` → wraps `rt_cranelift_append_block_param()`
- `cranelift_band()` → wraps `rt_cranelift_band()`
- `cranelift_bconst()` → wraps `rt_cranelift_bconst()`
- `cranelift_begin_function()` → wraps `rt_cranelift_begin_function()`
- `cranelift_bitcast()` → wraps `rt_cranelift_bitcast()`
- `cranelift_block_param()` → wraps `rt_cranelift_block_param()`
- `cranelift_bnot()` → wraps `rt_cranelift_bnot()`
- `cranelift_bor()` → wraps `rt_cranelift_bor()`
- `cranelift_brif()` → wraps `rt_cranelift_brif()`
- `cranelift_bxor()` → wraps `rt_cranelift_bxor()`
- `cranelift_call_function_ptr()` → wraps `rt_cranelift_call_function_ptr()`
- `cranelift_call_indirect()` → wraps `rt_cranelift_call_indirect()`
- `cranelift_call()` → wraps `rt_cranelift_call()`
- `cranelift_create_block()` → wraps `rt_cranelift_create_block()`
- `cranelift_define_function()` → wraps `rt_cranelift_define_function()`
- `cranelift_emit_object()` → wraps `rt_cranelift_emit_object()`
- `cranelift_end_function()` → wraps `rt_cranelift_end_function()`
- `cranelift_fadd()` → wraps `rt_cranelift_fadd()`
- `cranelift_fcmp()` → wraps `rt_cranelift_fcmp()`
- `cranelift_fconst()` → wraps `rt_cranelift_fconst()`
- `cranelift_fcvt_from_sint()` → wraps `rt_cranelift_fcvt_from_sint()`
- `cranelift_fcvt_from_uint()` → wraps `rt_cranelift_fcvt_from_uint()`
- `cranelift_fcvt_to_sint()` → wraps `rt_cranelift_fcvt_to_sint()`
- `cranelift_fcvt_to_uint()` → wraps `rt_cranelift_fcvt_to_uint()`
- `cranelift_fdiv()` → wraps `rt_cranelift_fdiv()`
- `cranelift_finalize_module()` → wraps `rt_cranelift_finalize_module()`
- `cranelift_fmul()` → wraps `rt_cranelift_fmul()`
- `cranelift_free_module()` → wraps `rt_cranelift_free_module()`
- `cranelift_fsub()` → wraps `rt_cranelift_fsub()`
- `cranelift_get_function_ptr()` → wraps `rt_cranelift_get_function_ptr()`
- `cranelift_iadd()` → wraps `rt_cranelift_iadd()`
- `cranelift_icmp()` → wraps `rt_cranelift_icmp()`
- `cranelift_iconst()` → wraps `rt_cranelift_iconst()`
- `cranelift_imul()` → wraps `rt_cranelift_imul()`
- `cranelift_ireduce()` → wraps `rt_cranelift_ireduce()`
- `cranelift_ishl()` → wraps `rt_cranelift_ishl()`
- `cranelift_isub()` → wraps `rt_cranelift_isub()`
- `cranelift_jump()` → wraps `rt_cranelift_jump()`
- `cranelift_load()` → wraps `rt_cranelift_load()`
- `cranelift_new_aot_module()` → wraps `rt_cranelift_new_aot_module()`
- `cranelift_new_module()` → wraps `rt_cranelift_new_module()`
- `cranelift_new_signature()` → wraps `rt_cranelift_new_signature()`
- `cranelift_null()` → wraps `rt_cranelift_null()`
- `cranelift_return_void()` → wraps `rt_cranelift_return_void()`
- `cranelift_return()` → wraps `rt_cranelift_return()`
- `cranelift_sdiv()` → wraps `rt_cranelift_sdiv()`
- `cranelift_seal_all_blocks()` → wraps `rt_cranelift_seal_all_blocks()`
- `cranelift_seal_block()` → wraps `rt_cranelift_seal_block()`
- `cranelift_sextend()` → wraps `rt_cranelift_sextend()`
- `cranelift_sig_add_param()` → wraps `rt_cranelift_sig_add_param()`
- `cranelift_sig_set_return()` → wraps `rt_cranelift_sig_set_return()`
- `cranelift_srem()` → wraps `rt_cranelift_srem()`
- `cranelift_sshr()` → wraps `rt_cranelift_sshr()`
- `cranelift_stack_addr()` → wraps `rt_cranelift_stack_addr()`
- `cranelift_stack_slot()` → wraps `rt_cranelift_stack_slot()`
- `cranelift_store()` → wraps `rt_cranelift_store()`
- `cranelift_switch_to_block()` → wraps `rt_cranelift_switch_to_block()`
- `cranelift_trap()` → wraps `rt_cranelift_trap()`
- `cranelift_udiv()` → wraps `rt_cranelift_udiv()`
- `cranelift_uextend()` → wraps `rt_cranelift_uextend()`
- `cranelift_urem()` → wraps `rt_cranelift_urem()`
- `cranelift_ushr()` → wraps `rt_cranelift_ushr()`
- `create_dir()` → wraps `rt_dir_create()`
- `create_hir_lowering()` → wraps `rt_file_read_text()`
- `create_symlink()` → wraps `rt_package_create_symlink()`
- `create_tarball()` → wraps `rt_package_create_tarball()`
- `crypto_module()` → wraps `rt_items()`
- `current_date_string()` → wraps `rt_time_now_unix_micros()`
- `current_time_ms()` → wraps `rt_current_time_ms()`
- `current_time_ms()` → wraps `rt_time_now_seconds()`
- `current_timestamp_string()` → wraps `rt_time_now_unix_micros()`
- `current_timestamp()` → wraps `rt_time_now_unix_micros()`
- `current_time_unix()` → wraps `rt_getpid()`
- `current_time_unix()` → wraps `rt_time_now_seconds()`
- `current_time_us()` → wraps `rt_time_now_us()`
- `cwd()` → wraps `rt_env_cwd()`
- `data_module()` → wraps `rt_items()`
- `decode_png_simple()` → wraps `rt_vk_buffer_alloc()`
- `deserialize_checkpoint()` → wraps `rt_torch_checkpoint_len()`
- `detect_engine_version()` → wraps `rt_file_read_text()`
- `det()` → wraps `rt_torch_linalg_det()`
- `device_from_code()` → wraps `rt_torch_cuda_available()`
- `diagram_placeholder()` → wraps `rt_diagram_enable()`
- `diff_children()` → wraps `rt_child()`
- `dir_create_all()` → wraps `rt_dir_create_all()`
- `dir_create()` → wraps `rt_dir_create()`
- `dir_list()` → wraps `rt_dir_list()`
- `dirname()` → wraps `rt_path_dirname()`
- `dir_remove_all()` → wraps `rt_package_remove_dir_all()`
- `dir_remove()` → wraps `rt_dir_remove()`
- `dir_walk()` → wraps `rt_dir_walk()`
- `disable_ffi_recording()` → wraps `rt_diagram_disable()`
- `disable_ffi_screenshots()` → wraps `rt_screenshot_disable()`
- `disable_stack_overflow_detection()` → wraps `rt_fault_set_stack_overflow_detection()`
- `discover_directory_config()` → wraps `rt_file_exists()`
- `discover_file_config()` → wraps `rt_file_exists()`
- `discover_project_config()` → wraps `rt_file_exists()`
- `elu()` → wraps `rt_torch_elu()`
- `emit()` → wraps `rt_log_emit()`
- `enable_ffi_recording()` → wraps `rt_diagram_enable()`
- `enable_ffi_screenshots()` → wraps `rt_screenshot_enable()`
- `enable_stack_overflow_detection()` → wraps `rt_fault_set_stack_overflow_detection()`
- `ensure_dir()` → wraps `rt_dir_create()`
- `env_get_ptr()` → wraps `rt_env_get()`
- `env_get()` → wraps `rt_env_get()`
- `env_set_ptr()` → wraps `rt_env_set()`
- `env_set()` → wraps `rt_env_set()`
- `eprintln()` → wraps `rt_eprintln()`
- `eval_binary()` → wraps `rt_error_division_by_zero()`
- `eval_builtin()` → wraps `rt_value()`
- `eval_expr_simple()` → wraps `rt_ast_expr_tag()`
- `eval_unary()` → wraps `rt_error_type_mismatch()`
- `example_comparison()` → wraps `rt_impl()`
- `execute_command()` → wraps `rt_execute_command()`
- `exec()` → wraps `rt_exec()`
- `exist()` → wraps `rt_env_exists()`
- `exist()` → wraps `rt_file_exists()`
- `exist()` → wraps `rt_path_exists()`
- `export_codecov()` → wraps `rt_codecov()`
- `export_coverage_json_compact()` → wraps `rt_coverage_json_compact()`
- `export_coverage_json()` → wraps `rt_coverage_json()`
- `export_coveralls()` → wraps `rt_coveralls()`
- `export_layout_sdn()` → wraps `rt_layout_sdn()`
- `export_onnx()` → wraps `rt_onnx()`
- `export_requires_access_spec()` → wraps `rt_requires_access_spec()`
- `exp()` → wraps `rt_math_exp()`
- `extension()` → wraps `rt_path_ext()`
- `extract_brief_from_file()` → wraps `rt_file_exists()`
- `extract_directory()` → wraps `rt_path_dirname()`
- `extract_import_target()` → wraps `rt_target()`
- `extract_project_root()` → wraps `rt_path_dirname()`
- `extract_tarball()` → wraps `rt_package_extract_tarball()`
- `fault_set_execution_limit()` → wraps `rt_fault_set_execution_limit()`
- `fault_set_max_recursion_depth()` → wraps `rt_fault_set_max_recursion_depth()`
- `fault_set_stack_overflow_detection()` → wraps `rt_fault_set_stack_overflow_detection()`
- `fault_set_timeout()` → wraps `rt_fault_set_timeout()`
- `ffi_compile_to_native()` → wraps `rt_compile_to_native()`
- `ffi_execute_native()` → wraps `rt_execute_native()`
- `ffi_file_delete()` → wraps `rt_file_delete()`
- `ffi_time_now_unix_micros()` → wraps `rt_time_now_unix_micros()`
- `fftn()` → wraps `rt_torch_fftn()`
- `fftshift()` → wraps `rt_torch_fftshift()`
- `fft()` → wraps `rt_torch_fft()`
- `file_append()` → wraps `rt_file_append_text()`
- `file_atomic_write()` → wraps `rt_file_atomic_write()`
- `file_copy()` → wraps `rt_file_copy()`
- `file_delete_ptr()` → wraps `rt_file_delete()`
- `file_delete()` → wraps `rt_file_delete()`
- `file_exists_ptr()` → wraps `rt_file_exists()`
- `file_exists()` → wraps `rt_file_exists()`
- `file_hash()` → wraps `rt_file_hash()`
- `file_lock()` → wraps `rt_file_lock()`
- `file_modified_time()` → wraps `rt_file_modified_time()`
- `file_read_bytes()` → wraps `rt_file_read_bytes()`
- `file_read_lines()` → wraps `rt_file_read_lines()`
- `file_read_text_ptr()` → wraps `rt_file_read_text()`
- `file_read_text()` → wraps `rt_file_read_text()`
- `file_read()` → wraps `rt_file_read_text()`
- `file_remove()` → wraps `rt_file_remove()`
- `file_size_raw()` → wraps `rt_file_size()`
- `file_size()` → wraps `rt_package_file_size()`
- `file_unlock()` → wraps `rt_file_unlock()`
- `file_write_bytes()` → wraps `rt_file_write_bytes()`
- `file_write_text_ptr()` → wraps `rt_file_write_text()`
- `file_write()` → wraps `rt_file_write_text()`
- `find_port_value()` → wraps `rt_value()`
- `find_runtime_lib_dir()` → wraps `rt_env_get()`
- `find_simple_old_binary()` → wraps `rt_env_get()`
- `find()` → wraps `rt_file_find()`
- `finish_run()` → wraps `rt_time_now_unix_micros()`
- `floor()` → wraps `rt_math_floor()`
- `fn_rt_codegen_compile_module()` → wraps `rt_codegen_compile_module()`
- `fn_rt_codegen_get_function_ptr()` → wraps `rt_codegen_get_function_ptr()`
- `fn_rt_codegen_init()` → wraps `rt_codegen_init()`
- `fn_rt_current_time_ms()` → wraps `rt_current_time_ms()`
- `fn_rt_dir_create_all()` → wraps `rt_dir_create_all()`
- `fn_rt_dir_create()` → wraps `rt_dir_create()`
- `fn_rt_dir_list()` → wraps `rt_dir_list()`
- `fn_rt_dir_remove()` → wraps `rt_dir_remove()`
- `fn_rt_dir_walk()` → wraps `rt_dir_walk()`
- `fn_rt_env_cwd()` → wraps `rt_env_cwd()`
- `fn_rt_env_get()` → wraps `rt_env_get()`
- `fn_rt_env_home()` → wraps `rt_env_home()`
- `fn_rt_env_set()` → wraps `rt_env_set()`
- `fn_rt_file_atomic_write()` → wraps `rt_file_atomic_write()`
- `fn_rt_file_copy()` → wraps `rt_file_copy()`
- `fn_rt_file_delete()` → wraps `rt_file_delete()`
- `fn_rt_file_exists()` → wraps `rt_file_exists()`
- `fn_rt_file_read_text()` → wraps `rt_file_read_text()`
- `fn_rt_file_write_text()` → wraps `rt_file_write_text()`
- `fn_rt_gc_collect()` → wraps `rt_gc_collect()`
- `fn_rt_gc_get_free_bytes()` → wraps `rt_gc_get_free_bytes()`
- `fn_rt_gc_get_heap_size()` → wraps `rt_gc_get_heap_size()`
- `fn_rt_gc_init()` → wraps `rt_gc_init()`
- `fn_rt_gc_malloc_atomic()` → wraps `rt_gc_malloc_atomic()`
- `fn_rt_gc_malloc()` → wraps `rt_gc_malloc()`
- `fn_rt_getpid()` → wraps `rt_getpid()`
- `fn_rt_glob()` → wraps `rt_glob()`
- `fn_rt_gzip_compress()` → wraps `rt_gzip_compress()`
- `fn_rt_gzip_decompress()` → wraps `rt_gzip_decompress()`
- `fn_rt_hostname()` → wraps `rt_hostname()`
- `fn_rt_http_get()` → wraps `rt_http_get()`
- `fn_rt_http_post()` → wraps `rt_http_post()`
- `fn_rt_json_get()` → wraps `rt_json_get()`
- `fn_rt_json_parse()` → wraps `rt_json_parse()`
- `fn_rt_json_stringify()` → wraps `rt_json_stringify()`
- `fn_rt_parallel_map()` → wraps `rt_parallel_map()`
- `fn_rt_process_output()` → wraps `rt_process_output()`
- `fn_rt_process_run_timeout()` → wraps `rt_process_run_timeout()`
- `fn_rt_process_run()` → wraps `rt_process_run()`
- `fn_rt_readline_with_prompt()` → wraps `rt_readline_with_prompt()`
- `fn_rt_readline()` → wraps `rt_readline()`
- `fn_rt_regex_find_all()` → wraps `rt_regex_find_all()`
- `fn_rt_regex_match()` → wraps `rt_regex_match()`
- `fn_rt_regex_replace()` → wraps `rt_regex_replace()`
- `fn_rt_shell_exec()` → wraps `rt_shell_exec()`
- `fn_rt_shell()` → wraps `rt_shell()`
- `fn_rt_system_cpu_count()` → wraps `rt_system_cpu_count()`
- `fn_rt_tar_create()` → wraps `rt_tar_create()`
- `fn_rt_tar_extract()` → wraps `rt_tar_extract()`
- `fn_rt_thread_count()` → wraps `rt_thread_count()`
- `fn_rt_time_now_unix_micros()` → wraps `rt_time_now_unix_micros()`
- `fn_rt_timestamp_get_day()` → wraps `rt_timestamp_get_day()`
- `fn_rt_timestamp_get_hour()` → wraps `rt_timestamp_get_hour()`
- `fn_rt_timestamp_get_minute()` → wraps `rt_timestamp_get_minute()`
- `fn_rt_timestamp_get_month()` → wraps `rt_timestamp_get_month()`
- `fn_rt_timestamp_get_second()` → wraps `rt_timestamp_get_second()`
- `fn_rt_timestamp_get_year()` → wraps `rt_timestamp_get_year()`
- `fn_rt_toml_parse()` → wraps `rt_toml_parse()`
- `fn_rt_value_add()` → wraps `rt_value_add()`
- `fn_rt_value_array_new()` → wraps `rt_value_array_new()`
- `fn_rt_value_as_bool()` → wraps `rt_value_as_bool()`
- `fn_rt_value_as_float()` → wraps `rt_value_as_float()`
- `fn_rt_value_as_int()` → wraps `rt_value_as_int()`
- `fn_rt_value_as_string()` → wraps `rt_value_as_string()`
- `fn_rt_value_bool()` → wraps `rt_value_bool()`
- `fn_rt_value_clone()` → wraps `rt_value_clone()`
- `fn_rt_value_dict_new()` → wraps `rt_value_dict_new()`
- `fn_rt_value_div()` → wraps `rt_value_div()`
- `fn_rt_value_eq()` → wraps `rt_value_eq()`
- `fn_rt_value_float()` → wraps `rt_value_float()`
- `fn_rt_value_free()` → wraps `rt_value_free()`
- `fn_rt_value_int()` → wraps `rt_value_int()`
- `fn_rt_value_is_array()` → wraps `rt_value_is_array()`
- `fn_rt_value_is_bool()` → wraps `rt_value_is_bool()`
- `fn_rt_value_is_dict()` → wraps `rt_value_is_dict()`
- `fn_rt_value_is_float()` → wraps `rt_value_is_float()`
- `fn_rt_value_is_int()` → wraps `rt_value_is_int()`
- `fn_rt_value_is_nil()` → wraps `rt_value_is_nil()`
- `fn_rt_value_is_string()` → wraps `rt_value_is_string()`
- `fn_rt_value_lt()` → wraps `rt_value_lt()`
- `fn_rt_value_mul()` → wraps `rt_value_mul()`
- `fn_rt_value_nil()` → wraps `rt_value_nil()`
- `fn_rt_value_println()` → wraps `rt_value_println()`
- `fn_rt_value_print()` → wraps `rt_value_print()`
- `fn_rt_value_string()` → wraps `rt_value_string()`
- `fn_rt_value_sub()` → wraps `rt_value_sub()`
- `fn_rt_value_type()` → wraps `rt_value_type()`
- `fnv_hash()` → wraps `rt_fnv_hash()`
- `format_performance_table()` → wraps `rt_timings()`
- `from_data()` → wraps `rt_torch_tensor()`
- `gc_collect()` → wraps `rt_gc_collect()`
- `gc_init()` → wraps `rt_gc_init()`
- `gc_malloc()` → wraps `rt_gc_malloc()`
- `gc_module()` → wraps `rt_items()`
- `gelu()` → wraps `rt_torch_gelu()`
- `generate_arch_ffi()` → wraps `rt_diagram_generate_arch()`
- `generate_class_ffi()` → wraps `rt_diagram_generate_class()`
- `generate_html_report_with_source()` → wraps `rt_with_source()`
- `_generate_id()` → wraps `rt_time_now_seconds()`
- `generate_import()` → wraps `rt_items()`
- `generate_run_id()` → wraps `rt_time_now_unix_micros()`
- `generate_sequence_ffi()` → wraps `rt_diagram_generate_sequence()`
- `generate_spec_spl()` → wraps `rt_compiles()`
- `get_current_time()` → wraps `rt_time_now_unix_micros()`
- `get_document()` → wraps `rt_before()`
- `get_elapsed_time()` → wraps `rt_progress_get_elapsed_seconds()`
- `get_env_cwd()` → wraps `rt_env_cwd()`
- `get_env_home()` → wraps `rt_env_home()`
- `get_env_temp()` → wraps `rt_env_temp()`
- `get_env_vars()` → wraps `rt_env_all()`
- `get_env()` → wraps `rt_env_exists()`
- `get_file_info()` → wraps `rt_file_exists()`
- `get_file_modified_time()` → wraps `rt_file_read_text()`
- `get_file_size()` → wraps `rt_package_file_size()`
- `get_files_recursive()` → wraps `rt_dir_list()`
- `get_flag_value()` → wraps `rt_args_all()`
- `get_opt()` → wraps `rt_env_exists()`
- `get_or()` → wraps `rt_env_get()`
- `getpid()` → wraps `rt_getpid()`
- `get_screenshot_path_ffi()` → wraps `rt_screenshot_get_path()`
- `_get_timestamp_ms()` → wraps `rt_time_now_seconds()`
- `get()` → wraps `rt_args_count()`
- `get()` → wraps `rt_env_get()`
- `glob_match()` → wraps `rt_by()`
- `glob()` → wraps `rt_dir_glob()`
- `glob()` → wraps `rt_glob()`
- `gzip_compress()` → wraps `rt_gzip_compress()`
- `gzip_decompress()` → wraps `rt_gzip_decompress()`
- `handle_semantic_tokens_full()` → wraps `rt_by()`
- `handle_web_serve()` → wraps `rt_value()`
- `hashmap_clear()` → wraps `rt_hashmap_clear()`
- `hashmap_contains()` → wraps `rt_hashmap_contains()`
- `hashmap_entries()` → wraps `rt_hashmap_keys()`
- `hashmap_free()` → wraps `rt_hashmap_free()`
- `hashmap_get()` → wraps `rt_hashmap_get()`
- `hashmap_insert()` → wraps `rt_hashmap_insert()`
- `hashmap_keys()` → wraps `rt_hashmap_keys()`
- `hashmap_len()` → wraps `rt_hashmap_len()`
- `hashmap_new()` → wraps `rt_hashmap_new()`
- `hashmap_remove()` → wraps `rt_hashmap_remove()`
- `hashmap_values()` → wraps `rt_hashmap_values()`
- `hashset_clear()` → wraps `rt_hashset_clear()`
- `hashset_contains()` → wraps `rt_hashset_contains()`
- `hashset_free()` → wraps `rt_hashset_free()`
- `hashset_insert()` → wraps `rt_hashset_insert()`
- `hashset_len()` → wraps `rt_hashset_len()`
- `hashset_new()` → wraps `rt_hashset_new()`
- `hashset_remove()` → wraps `rt_hashset_remove()`
- `hashset_to_array()` → wraps `rt_hashset_to_array()`
- `has_lockfile()` → wraps `rt_package_exists()`
- `has()` → wraps `rt_args_all()`
- `heightfield_sphere_collision()` → wraps `rt_by_axis()`
- `home()` → wraps `rt_env_home()`
- `hostname()` → wraps `rt_hostname()`
- `ifftshift()` → wraps `rt_torch_ifftshift()`
- `ifft()` → wraps `rt_torch_ifft()`
- `import_exists_spec()` → wraps `rt_exists_spec()`
- `indices_to_bytes()` → wraps `rt_vk_image_upload()`
- `init_process_group()` → wraps `rt_torch_dist_init_process_group()`
- `init_progress()` → wraps `rt_progress_init()`
- `inv()` → wraps `rt_torch_linalg_inv()`
- `io_module()` → wraps `rt_items()`
- `irfft()` → wraps `rt_torch_irfft()`
- `is_available()` → wraps `rt_torch_dist_is_available()`
- `is_directory()` → wraps `rt_package_is_dir()`
- `is_dir()` → wraps `rt_dir_list()`
- `is_dir()` → wraps `rt_package_is_dir()`
- `is_ffi_screenshots_enabled()` → wraps `rt_screenshot_is_enabled()`
- `is_file()` → wraps `rt_dir_list()`
- `is_method_start_class()` → wraps `rt_class()`
- `kaiming_normal()` → wraps `rt_torch_init_kaiming_normal()`
- `kaiming_uniform()` → wraps `rt_torch_init_kaiming_uniform()`
- `leaky_relu()` → wraps `rt_torch_leaky_relu()`
- `line_start_offset()` → wraps `rt_offset()`
- `list_dir()` → wraps `rt_dir_list()`
- `load_image()` → wraps `rt_torch_vision_load_image()`
- `load_onnx()` → wraps `rt_torch_onnx_load()`
- `load_torchscript()` → wraps `rt_torch_jit_load()`
- `load()` → wraps `rt_torch_load()`
- `log()` → wraps `rt_math_log()`
- `longest_increasing_subsequence()` → wraps `rt_pos()`
- `loop_mode_from_int()` → wraps `rt_key()`
- `main()` → wraps `rt_env_cwd()`
- `main()` → wraps `rt_exec()`
- `main()` → wraps `rt_server()`
- `mark_architectural()` → wraps `rt_diagram_mark_architectural()`
- `mir_type_to_lean()` → wraps `rt_module()`
- `mir_type_to_llvm()` → wraps `rt_function()`
- `mish()` → wraps `rt_torch_mish()`
- `mkdir_all()` → wraps `rt_package_mkdir_all()`
- `net_module()` → wraps `rt_items()`
- `new_channel()` → wraps `rt_channel_new()`
- `normal()` → wraps `rt_torch_init_normal()`
- `ones()` → wraps `rt_torch_init_constant()`
- `open_file()` → wraps `rt_file_open()`
- `ordering_to_int()` → wraps `rt_atomic_int_new()`
- `orthogonal()` → wraps `rt_torch_init_orthogonal()`
- `parse_alert_config()` → wraps `rt_config()`
- `parse_assert_statement()` → wraps `rt_statement()`
- `parse_auto_import()` → wraps `rt_opt()`
- `parse_class_body()` → wraps `rt_class()`
- `parse_common_use()` → wraps `rt_target()`
- `parse_execution_config()` → wraps `rt_env_get()`
- `parse_export_statement()` → wraps `rt_statement()`
- `parse_export_use()` → wraps `rt_use()`
- `parse_file()` → wraps `rt_file_read_text()`
- `parse_from_import()` → wraps `rt_target()`
- `parse_import_alias()` → wraps `rt_alias()`
- `parse_import_line()` → wraps `rt_line()`
- `parse_import_names()` → wraps `rt_names()`
- `parse_import_path()` → wraps `rt_path()`
- `parse_import_statement()` → wraps `rt_statement()`
- `parse_import_target()` → wraps `rt_target()`
- `parse_import()` → wraps `rt_body()`
- `parse_int_helper()` → wraps `rt_env_all()`
- `parse_lean_import_block()` → wraps `rt_block()`
- `parse_lockfile_file()` → wraps `rt_package_exists()`
- `parse_toml_config()` → wraps `rt_config()`
- `parse_use_or_import_body()` → wraps `rt_body()`
- `parse_use_path_and_target()` → wraps `rt_target()`
- `parse_use_statement()` → wraps `rt_target()`
- `parse_use()` → wraps `rt_body()`
- `passes_for_level()` → wraps `rt_function()`
- `path_basename()` → wraps `rt_path_basename()`
- `path_exists()` → wraps `rt_package_exists()`
- `pow()` → wraps `rt_math_pow()`
- `preprocess_imagenet()` → wraps `rt_torch_vision_preprocess_imagenet()`
- `process_module()` → wraps `rt_items()`
- `process_output()` → wraps `rt_process_output()`
- `process_run_timeout()` → wraps `rt_process_run_timeout()`
- `process_run_with_limits()` → wraps `rt_process_run_with_limits()`
- `process_run()` → wraps `rt_process_run()`
- `program_name()` → wraps `rt_args_count()`
- `progress_get_elapsed_seconds()` → wraps `rt_progress_get_elapsed_seconds()`
- `progress_init()` → wraps `rt_progress_init()`
- `progress_reset()` → wraps `rt_progress_reset()`
- `prune_by_halving()` → wraps `rt_time_micros()`
- `quick_sort_helper()` → wraps `rt_helper()`
- `quick_sort_partition()` → wraps `rt_partition()`
- `quick_sort()` → wraps `rt_helper()`
- `random_getstate()` → wraps `rt_random_getstate()`
- `random_next()` → wraps `rt_random_next()`
- `random_randint()` → wraps `rt_random_randint()`
- `random_random()` → wraps `rt_random_random()`
- `random_seed()` → wraps `rt_random_seed()`
- `random_setstate()` → wraps `rt_random_setstate()`
- `random_uniform()` → wraps `rt_random_uniform()`
- `read_file_content()` → wraps `rt_file_read_text()`
- `read_file_to_string()` → wraps `rt_file_read_text()`
- `read_file()` → wraps `rt_file_read_text()`
- `read_file()` → wraps `rt_read_file()`
- `read_text()` → wraps `rt_file_read_text()`
- `read_to_bytes()` → wraps `rt_file_mmap_read_text()`
- `reduce_scatter()` → wraps `rt_torch_dist_reduce_scatter()`
- `register_event_handler()` → wraps `rt_child_at()`
- `release_lock()` → wraps `rt_file_unlock()`
- `relu()` → wraps `rt_torch_relu()`
- `remove_dir_all()` → wraps `rt_package_remove_dir_all()`
- `remove_dir()` → wraps `rt_dir_remove()`
- `remove_env()` → wraps `rt_env_remove()`
- `remove()` → wraps `rt_env_remove()`
- `remove()` → wraps `rt_file_remove()`
- `rename()` → wraps `rt_file_rename()`
- `request()` → wraps `rt_after()`
- `reset_progress()` → wraps `rt_progress_reset()`
- `resolve()` → wraps `rt_file_exists()`
- `rfft()` → wraps `rt_torch_rfft()`
- `_rt_coverage_clear()` → wraps `rt_coverage_clear()`
- `rt_coverage_clear()` → wraps `rt_coverage_clear()`
- `_rt_coverage_dump_sdn()` → wraps `rt_coverage_dump_sdn()`
- `rt_coverage_dump_sdn()` → wraps `rt_coverage_dump_sdn()`
- `_rt_coverage_enabled()` → wraps `rt_coverage_enabled()`
- `rt_coverage_enabled()` → wraps `rt_coverage_enabled()`
- `rt_coverage_free_sdn()` → wraps `rt_coverage_free_sdn()`
- `rt_cstring_to_text()` → wraps `rt_cstring_to_text()`
- `_rt_dir_entries()` → wraps `rt_dir_entries()`
- `_rt_file_mtime()` → wraps `rt_file_mtime()`
- `_rt_file_read_text()` → wraps `rt_file_read_text()`
- `_rt_file_size()` → wraps `rt_file_size()`
- `_rt_file_write_text()` → wraps `rt_file_write_text()`
- `rt_math_abs_extern()` → wraps `rt_math_abs_extern()`
- `rt_math_abs()` → wraps `rt_math_abs()`
- `rt_math_acos_extern()` → wraps `rt_math_acos_extern()`
- `rt_math_acos()` → wraps `rt_math_acos()`
- `rt_math_asin_extern()` → wraps `rt_math_asin_extern()`
- `rt_math_asin()` → wraps `rt_math_asin()`
- `rt_math_atan_extern()` → wraps `rt_math_atan_extern()`
- `rt_math_atan()` → wraps `rt_math_atan()`
- `rt_math_cbrt_extern()` → wraps `rt_math_cbrt_extern()`
- `rt_math_cbrt()` → wraps `rt_math_cbrt()`
- `rt_math_ceil_extern()` → wraps `rt_math_ceil_extern()`
- `rt_math_ceil_f()` → wraps `rt_math_ceil_f()`
- `rt_math_clamp_extern()` → wraps `rt_math_clamp_extern()`
- `rt_math_clamp()` → wraps `rt_math_clamp()`
- `rt_math_cos_extern()` → wraps `rt_math_cos_extern()`
- `rt_math_cosh_extern()` → wraps `rt_math_cosh_extern()`
- `rt_math_cosh()` → wraps `rt_math_cosh()`
- `rt_math_cos()` → wraps `rt_math_cos()`
- `rt_math_exp_extern()` → wraps `rt_math_exp_extern()`
- `rt_math_exp()` → wraps `rt_math_exp()`
- `rt_math_floor_extern()` → wraps `rt_math_floor_extern()`
- `rt_math_floor_f()` → wraps `rt_math_floor_f()`
- `rt_math_fract_extern()` → wraps `rt_math_fract_extern()`
- `rt_math_fract()` → wraps `rt_math_fract()`
- `rt_math_gcd_extern()` → wraps `rt_math_gcd_extern()`
- `rt_math_gcd()` → wraps `rt_math_gcd()`
- `rt_math_hypot_extern()` → wraps `rt_math_hypot_extern()`
- `rt_math_hypot()` → wraps `rt_math_hypot()`
- `rt_math_inf_extern()` → wraps `rt_math_inf_extern()`
- `rt_math_inf()` → wraps `rt_math_inf()`
- `rt_math_is_finite_extern()` → wraps `rt_math_is_finite_extern()`
- `rt_math_is_finite()` → wraps `rt_math_is_finite()`
- `rt_math_is_inf_extern()` → wraps `rt_math_is_inf_extern()`
- `rt_math_is_inf()` → wraps `rt_math_is_inf()`
- `rt_math_is_nan_extern()` → wraps `rt_math_is_nan_extern()`
- `rt_math_is_nan()` → wraps `rt_math_is_nan()`
- `rt_math_lcm_extern()` → wraps `rt_math_lcm_extern()`
- `rt_math_lcm()` → wraps `rt_math_lcm()`
- `rt_math_log_extern()` → wraps `rt_math_log_extern()`
- `rt_math_log()` → wraps `rt_math_log()`
- `rt_math_max_f_extern()` → wraps `rt_math_max_f_extern()`
- `rt_math_max_f()` → wraps `rt_math_max_f()`
- `rt_math_min_f_extern()` → wraps `rt_math_min_f_extern()`
- `rt_math_min_f()` → wraps `rt_math_min_f()`
- `rt_math_nan_extern()` → wraps `rt_math_nan_extern()`
- `rt_math_nan()` → wraps `rt_math_nan()`
- `rt_math_pow_extern()` → wraps `rt_math_pow_extern()`
- `rt_math_pow()` → wraps `rt_math_pow()`
- `rt_math_rem_extern()` → wraps `rt_math_rem_extern()`
- `rt_math_rem()` → wraps `rt_math_rem()`
- `rt_math_round_extern()` → wraps `rt_math_round_extern()`
- `rt_math_round()` → wraps `rt_math_round()`
- `rt_math_sign_extern()` → wraps `rt_math_sign_extern()`
- `rt_math_sign()` → wraps `rt_math_sign()`
- `rt_math_sin_extern()` → wraps `rt_math_sin_extern()`
- `rt_math_sinh_extern()` → wraps `rt_math_sinh_extern()`
- `rt_math_sinh()` → wraps `rt_math_sinh()`
- `rt_math_sin()` → wraps `rt_math_sin()`
- `rt_math_sqrt_extern()` → wraps `rt_math_sqrt_extern()`
- `rt_math_sqrt()` → wraps `rt_math_sqrt()`
- `rt_math_tan_extern()` → wraps `rt_math_tan_extern()`
- `rt_math_tanh_extern()` → wraps `rt_math_tanh_extern()`
- `rt_math_tanh()` → wraps `rt_math_tanh()`
- `rt_math_tan()` → wraps `rt_math_tan()`
- `rt_math_trunc_extern()` → wraps `rt_math_trunc_extern()`
- `rt_math_trunc()` → wraps `rt_math_trunc()`
- `_rt_process_run()` → wraps `rt_process_run()`
- `_rt_progress_get_elapsed_seconds()` → wraps `rt_progress_get_elapsed_seconds()`
- `_rt_progress_init()` → wraps `rt_progress_init()`
- `_rt_progress_reset()` → wraps `rt_progress_reset()`
- `_rt_random_getstate()` → wraps `rt_random_getstate()`
- `_rt_random_next()` → wraps `rt_random_next()`
- `_rt_random_randint()` → wraps `rt_random_randint()`
- `_rt_random_random()` → wraps `rt_random_random()`
- `_rt_random_seed()` → wraps `rt_random_seed()`
- `_rt_random_setstate()` → wraps `rt_random_setstate()`
- `_rt_random_uniform()` → wraps `rt_random_uniform()`
- `_rt_sdn_check()` → wraps `rt_sdn_check()`
- `_rt_sdn_fmt()` → wraps `rt_sdn_fmt()`
- `_rt_sdn_from_json()` → wraps `rt_sdn_from_json()`
- `_rt_sdn_get()` → wraps `rt_sdn_get()`
- `_rt_sdn_set()` → wraps `rt_sdn_set()`
- `_rt_sdn_to_json()` → wraps `rt_sdn_to_json()`
- `_rt_time_now_seconds()` → wraps `rt_time_now_seconds()`
- `_rt_time_now_unix_micros()` → wraps `rt_time_now_unix_micros()`
- `_rt_timestamp_add_days()` → wraps `rt_timestamp_add_days()`
- `_rt_timestamp_diff_days()` → wraps `rt_timestamp_diff_days()`
- `_rt_timestamp_from_components()` → wraps `rt_timestamp_from_components()`
- `_rt_timestamp_get_day()` → wraps `rt_timestamp_get_day()`
- `_rt_timestamp_get_hour()` → wraps `rt_timestamp_get_hour()`
- `_rt_timestamp_get_microsecond()` → wraps `rt_timestamp_get_microsecond()`
- `_rt_timestamp_get_minute()` → wraps `rt_timestamp_get_minute()`
- `_rt_timestamp_get_month()` → wraps `rt_timestamp_get_month()`
- `_rt_timestamp_get_second()` → wraps `rt_timestamp_get_second()`
- `_rt_timestamp_get_year()` → wraps `rt_timestamp_get_year()`
- `run_alert_add()` → wraps `rt_add()`
- `run_alert_list()` → wraps `rt_list()`
- `run_alert_remove()` → wraps `rt_remove()`
- `run_dashboard()` → wraps `rt_add()`
- `run_dev_server()` → wraps `rt_file_watcher()`
- `runtime_value_module()` → wraps `rt_value_nil()`
- `save_image()` → wraps `rt_torch_vision_save_image()`
- `save_torchscript()` → wraps `rt_torch_jit_save()`
- `save()` → wraps `rt_torch_save()`
- `screenshot_exists_ffi()` → wraps `rt_screenshot_exists()`
- `script()` → wraps `rt_torch_jit_script()`
- `sdn_check()` → wraps `rt_sdn_check()`
- `sdn_fmt()` → wraps `rt_sdn_fmt()`
- `sdn_from_json()` → wraps `rt_sdn_from_json()`
- `sdn_get()` → wraps `rt_sdn_get()`
- `sdn_set()` → wraps `rt_sdn_set()`
- `sdn_to_json()` → wraps `rt_sdn_to_json()`
- `select_where()` → wraps `rt_torch_where()`
- `select()` → wraps `rt_torch_where()`
- `separator()` → wraps `rt_path_separator()`
- `serde_module()` → wraps `rt_items()`
- `serialize_work_item()` → wraps `rt_file_write()`
- `set_env()` → wraps `rt_env_set()`
- `set_execution_limit()` → wraps `rt_fault_set_execution_limit()`
- `set_ffi_output_dir()` → wraps `rt_screenshot_set_output_dir()`
- `set_ffi_refresh()` → wraps `rt_screenshot_set_refresh()`
- `set_ffi_test_context()` → wraps `rt_screenshot_set_context()`
- `set_permissions()` → wraps `rt_package_chmod()`
- `set_recursion_limit()` → wraps `rt_fault_set_stack_overflow_detection()`
- `set_timeout()` → wraps `rt_fault_set_timeout()`
- `settlement_main()` → wraps `rt_settlement_main()`
- `set()` → wraps `rt_env_set()`
- `shell_exec()` → wraps `rt_shell_exec()`
- `shell()` → wraps `rt_shell()`
- `sigmoid()` → wraps `rt_torch_sigmoid()`
- `silu()` → wraps `rt_torch_silu()`
- `sin()` → wraps `rt_math_sin()`
- `sleep()` → wraps `rt_thread_sleep()`
- `softmax()` → wraps `rt_torch_softmax()`
- `softplus()` → wraps `rt_torch_softplus()`
- `solve()` → wraps `rt_torch_linalg_solve()`
- `_sort_handlers_by_priority()` → wraps `rt_handlers_by_priority()`
- `sort_timings()` → wraps `rt_timings()`
- `sparse()` → wraps `rt_torch_init_sparse()`
- `spawn_isolated()` → wraps `rt_thread_spawn_isolated()`
- `spawn_limited()` → wraps `rt_thread_spawn_limited()`
- `spin_loop_hint()` → wraps `rt_spin_loop_hint()`
- `sqrt_extern()` → wraps `rt_extern()`
- `sqrt()` → wraps `rt_math_sqrt()`
- `stack()` → wraps `rt_torch_stack()`
- `start_diagram_recording()` → wraps `rt_diagram_recording()`
- `start_file_watcher()` → wraps `rt_file_watcher()`
- `start_polling_watcher()` → wraps `rt_polling_watcher()`
- `start_prefetch()` → wraps `rt_prefetch()`
- `start_recording()` → wraps `rt_recording()`
- `start_server()` → wraps `rt_server()`
- `start_with()` → wraps `rt_with()`
- `stateful_actor()` → wraps `rt_count()`
- `string_free()` → wraps `rt_string_free()`
- `sys_close()` → wraps `rt_file_close()`
- `sys_file_size()` → wraps `rt_file_get_size()`
- `sys_madvise()` → wraps `rt_file_madvise()`
- `sys_mmap()` → wraps `rt_file_mmap()`
- `sys_munmap()` → wraps `rt_file_munmap()`
- `sys_open()` → wraps `rt_file_open()`
- `system_module()` → wraps `rt_items()`
- `tanh()` → wraps `rt_torch_tanh()`
- `tan()` → wraps `rt_math_tan()`
- `temp()` → wraps `rt_env_temp()`
- `test_arithmetic()` → wraps `rt_value_int()`
- `test_comparison()` → wraps `rt_value_int()`
- `test_exec_ffi()` → wraps `rt_exec()`
- `test_file_hash_ffi()` → wraps `rt_file_hash()`
- `test_gc_malloc_atomic()` → wraps `rt_gc_malloc_atomic()`
- `test_gc_malloc()` → wraps `rt_gc_init()`
- `test_value_creation()` → wraps `rt_value_free()`
- `test_value_int()` → wraps `rt_value_int()`
- `test_value_nil()` → wraps `rt_value_nil()`
- `test_value_string()` → wraps `rt_value_string()`
- `time_module()` → wraps `rt_items()`
- `time_now_seconds()` → wraps `rt_time_now_seconds()`
- `time_now_unix_micros()` → wraps `rt_time_now_unix_micros()`
- `time_now()` → wraps `rt_time_now_seconds()`
- `timestamp_add_days()` → wraps `rt_timestamp_add_days()`
- `timestamp_day()` → wraps `rt_timestamp_get_day()`
- `timestamp_diff_days()` → wraps `rt_timestamp_diff_days()`
- `timestamp_from_components()` → wraps `rt_timestamp_from_components()`
- `timestamp_get_day()` → wraps `rt_timestamp_get_day()`
- `timestamp_get_hour()` → wraps `rt_timestamp_get_hour()`
- `timestamp_get_microsecond()` → wraps `rt_timestamp_get_microsecond()`
- `timestamp_get_minute()` → wraps `rt_timestamp_get_minute()`
- `timestamp_get_month()` → wraps `rt_timestamp_get_month()`
- `timestamp_get_second()` → wraps `rt_timestamp_get_second()`
- `timestamp_get_year()` → wraps `rt_timestamp_get_year()`
- `timestamp_hour()` → wraps `rt_timestamp_get_hour()`
- `timestamp_minute()` → wraps `rt_timestamp_get_minute()`
- `timestamp_month()` → wraps `rt_timestamp_get_month()`
- `timestamp_second()` → wraps `rt_timestamp_get_second()`
- `timestamp_year()` → wraps `rt_timestamp_get_year()`
- `trace_call()` → wraps `rt_diagram_trace_method()`
- `trace_method()` → wraps `rt_diagram_trace_method_with_args()`
- `trace_return()` → wraps `rt_diagram_trace_return()`
- `trace()` → wraps `rt_torch_jit_trace()`
- `tree_to_expression()` → wraps `rt_expression()`
- `tree_to_module()` → wraps `rt_import()`
- `trim_start_all()` → wraps `rt_all()`
- `type_registry_has()` → wraps `rt_type_registry_has()`
- `type_registry_lookup()` → wraps `rt_type_registry_lookup()`
- `uniform()` → wraps `rt_torch_init_uniform()`
- `update_test_database()` → wraps `rt_run()`
- `validate_run_record()` → wraps `rt_process_exists()`
- `validate_verified_function()` → wraps `rt_missing_termination()`
- `value_add()` → wraps `rt_value_add()`
- `value_array_new()` → wraps `rt_value_array_new()`
- `value_as_bool()` → wraps `rt_value_as_bool()`
- `value_as_float()` → wraps `rt_value_as_float()`
- `value_as_int()` → wraps `rt_value_as_int()`
- `value_as_string()` → wraps `rt_value_as_string()`
- `value_bool()` → wraps `rt_value_bool()`
- `value_clone()` → wraps `rt_value_clone()`
- `value_dict_new()` → wraps `rt_value_dict_new()`
- `value_div()` → wraps `rt_value_div()`
- `value_eq()` → wraps `rt_value_eq()`
- `value_float()` → wraps `rt_value_float()`
- `value_free()` → wraps `rt_value_free()`
- `value_int()` → wraps `rt_value_int()`
- `value_is_array()` → wraps `rt_value_is_array()`
- `value_is_bool()` → wraps `rt_value_is_bool()`
- `value_is_dict()` → wraps `rt_value_is_dict()`
- `value_is_float()` → wraps `rt_value_is_float()`
- `value_is_int()` → wraps `rt_value_is_int()`
- `value_is_nil()` → wraps `rt_value_is_nil()`
- `value_is_string()` → wraps `rt_value_is_string()`
- `value_lt()` → wraps `rt_value_lt()`
- `value_mul()` → wraps `rt_value_mul()`
- `value_nil()` → wraps `rt_value_nil()`
- `value_println()` → wraps `rt_value_println()`
- `value_print()` → wraps `rt_value_print()`
- `value_string()` → wraps `rt_value_string()`
- `value_sub()` → wraps `rt_value_sub()`
- `value_type()` → wraps `rt_value_type()`
- `vec_clear()` → wraps `rt_vec_clear()`
- `vec_free()` → wraps `rt_vec_free()`
- `vec_get()` → wraps `rt_vec_get()`
- `vec_len()` → wraps `rt_vec_len()`
- `vec_new()` → wraps `rt_vec_new()`
- `vec_pop()` → wraps `rt_vec_pop()`
- `vec_push()` → wraps `rt_vec_push()`
- `vec_set()` → wraps `rt_vec_set()`
- `vec_to_array()` → wraps `rt_vec_to_array()`
- `walk_directory()` → wraps `rt_walk_directory()`
- `well_formed()` → wraps `rt_file_exists()`
- `with_diagrams()` → wraps `rt_diagram_recording()`
- `write_file()` → wraps `rt_file_write_text()`
- `write_file()` → wraps `rt_write_file()`
- `write_lockfile()` → wraps `rt_file_write_text()`
- `write_text()` → wraps `rt_file_write_text()`
- `xavier_normal()` → wraps `rt_torch_init_xavier_normal()`
- `xavier_uniform()` → wraps `rt_torch_init_xavier_uniform()`
- `yield_thread()` → wraps `rt_thread_yield()`
- `zeros_like()` → wraps `rt_torch_tensor()`
- `zeros()` → wraps `rt_torch_init_constant()`

## Recommendations

### Pattern 1: Use Existing Wrapper

If a wrapper exists, import and use it:

```simple
# ❌ Before (direct FFI call)
extern fn rt_file_exists(path: text) -> bool
val exists = rt_file_exists(path)

# ✅ After (use wrapper)
use app.io.{file_exists}
val exists = file_exists(path)
```

### Pattern 2: Create Missing Wrapper

If no wrapper exists, add it to the appropriate FFI module:

**In `src/app/io/mod.spl` or `src/compiler/ffi.spl`:**

```simple
# Tier 1: Extern declaration
extern fn rt_new_function(arg: text) -> i64

# Tier 2: Wrapper function
fn new_function(arg: text) -> i64:
    rt_new_function(arg)

# Export
export new_function
```

### Pattern 3: Add TODO Comment

For temporary direct access (e.g., in tests or prototypes):

```simple
# TODO: Replace with wrapper from app.io once available
extern fn rt_file_exists(path: text) -> bool
val exists = rt_file_exists(path)
```

## Action Items

1. **Review each direct call** - Check if wrapper exists
2. **Update imports** - Use wrappers from `app.io` or `compiler.ffi`
3. **Create missing wrappers** - Add to appropriate FFI module
4. **Add TODO comments** - For cases that can't be fixed immediately
5. **Validate** - Re-run this script after fixes

## Excluded Locations

The following are excluded from this audit (expected to have direct FFI):

- `/core/` - Core runtime implementation
- `/ffi.spl` - FFI declaration modules
- `io/mod.spl` - FFI wrapper module itself
- Wrapper function definitions (where they call the FFI)

## Script Location

This report was generated by: `scripts/audit_ffi_usage.sh`

To re-run: `bash scripts/audit_ffi_usage.sh`
