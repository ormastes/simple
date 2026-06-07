# Interp Resource Tracker Specification

> 1. ft reset

<!-- sdn-diagram:id=interp_resource_tracker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interp_resource_tracker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interp_resource_tracker_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interp_resource_tracker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Resource Tracker Specification

## Scenarios

### func_table_remove

#### removes a registered function

1. ft reset
2. ft register
   - Expected: before equals `100`
   - Expected: removed is true
   - Expected: after equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ft_reset()
ft_register("test_remove_fn", 100)
val before = ft_lookup("test_remove_fn")
expect(before).to_equal(100)
val removed = ft_remove("test_remove_fn")
expect(removed).to_equal(true)
val after = ft_lookup("test_remove_fn")
expect(after).to_equal(-1)
```

</details>

#### returns false for unknown function

1. ft reset
   - Expected: removed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ft_reset()
val removed = ft_remove("nonexistent_fn_xyz")
expect(removed).to_equal(false)
```

</details>

#### remove does not break other entries

1. ft reset
2. ft register
3. ft register
4. ft register
5. ft remove
   - Expected: ft_lookup("tr_keep_a") equals `200`
   - Expected: ft_lookup("tr_keep_c") equals `202`
   - Expected: ft_lookup("tr_remove_b") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ft_reset()
ft_register("tr_keep_a", 200)
ft_register("tr_remove_b", 201)
ft_register("tr_keep_c", 202)
ft_remove("tr_remove_b")
expect(ft_lookup("tr_keep_a")).to_equal(200)
expect(ft_lookup("tr_keep_c")).to_equal(202)
expect(ft_lookup("tr_remove_b")).to_equal(-1)
```

</details>

### struct_table_remove

#### removes a registered struct

1. st reset
2. st register
   - Expected: before equals `300`
   - Expected: removed is true
   - Expected: after equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
st_reset()
st_register("TestRemoveStruct", 300)
val before = st_lookup("TestRemoveStruct")
expect(before).to_equal(300)
val removed = st_remove("TestRemoveStruct")
expect(removed).to_equal(true)
val after = st_lookup("TestRemoveStruct")
expect(after).to_equal(-1)
```

</details>

#### returns false for unknown struct

1. st reset
   - Expected: removed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
st_reset()
val removed = st_remove("UnknownStructXYZ")
expect(removed).to_equal(false)
```

</details>

### env_remove_global

#### removes a global variable

1. ge reset
2. ge define
   - Expected: before equals `500`
   - Expected: removed is true
   - Expected: after equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ge_reset()
ge_define("test_remove_global", 500)
val before = ge_lookup("test_remove_global")
expect(before).to_equal(500)
val removed = ge_remove("test_remove_global")
expect(removed).to_equal(true)
val after = ge_lookup("test_remove_global")
expect(after).to_equal(-1)
```

</details>

#### returns false for unknown global

1. ge reset
   - Expected: removed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ge_reset()
val removed = ge_remove("nonexistent_global_xyz")
expect(removed).to_equal(false)
```

</details>

### InterpreterResourceTracker

### module tracking

#### begins tracking a module

1. mock irt init
2. mock irt begin module
   - Expected: mock_irt_is_tracked("test_module_a") is true
   - Expected: mock_irt_tracked_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("test_module_a")
expect(mock_irt_is_tracked("test_module_a")).to_equal(true)
expect(mock_irt_tracked_count()).to_equal(1)
```

</details>

#### does not double-track

1. mock irt init
2. mock irt begin module
3. mock irt begin module
   - Expected: mock_irt_tracked_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("test_module_dup")
mock_irt_begin_module("test_module_dup")
expect(mock_irt_tracked_count()).to_equal(1)
```

</details>

#### tracks multiple modules

1. mock irt init
2. mock irt begin module
3. mock irt begin module
   - Expected: mock_irt_tracked_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("mod_x")
mock_irt_begin_module("mod_y")
expect(mock_irt_tracked_count()).to_equal(2)
```

</details>

### name registration

#### tracks function names

1. mock irt init
2. mock irt begin module
3. mock irt track func
4. mock irt track func
   - Expected: mock_irt_get_func_count("fn_mod") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("fn_mod")
mock_irt_track_func("fn_mod", "func_a")
mock_irt_track_func("fn_mod", "func_b")
expect(mock_irt_get_func_count("fn_mod")).to_equal(2)
```

</details>

#### tracks struct names

1. mock irt init
2. mock irt begin module
3. mock irt track struct
   - Expected: mock_irt_get_struct_count("st_mod") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("st_mod")
mock_irt_track_struct("st_mod", "Point")
expect(mock_irt_get_struct_count("st_mod")).to_equal(1)
```

</details>

#### ignores tracking for unregistered module

1. mock irt init
2. mock irt track func
   - Expected: mock_irt_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_track_func("unknown_mod", "func_a")
expect(mock_irt_tracked_count()).to_equal(0)
```

</details>

### module unload

#### removes tracked functions from table

1. mock irt init
2. mock irt begin module
3. ft register
4. ft register
5. mock irt track func
6. mock irt track func
   - Expected: ft_lookup("irt_test_fn_1") equals `-1`
   - Expected: ft_lookup("irt_test_fn_2") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("unload_test_mod")
ft_register("irt_test_fn_1", 900)
ft_register("irt_test_fn_2", 901)
mock_irt_track_func("unload_test_mod", "irt_test_fn_1")
mock_irt_track_func("unload_test_mod", "irt_test_fn_2")
val removed = mock_irt_unload_module("unload_test_mod")
expect(removed).to_be_greater_than(0)
expect(ft_lookup("irt_test_fn_1")).to_equal(-1)
expect(ft_lookup("irt_test_fn_2")).to_equal(-1)
```

</details>

#### removes tracked globals from env

1. mock irt init
2. mock irt begin module
3. ge define
4. mock irt track global
5. mock irt unload module
   - Expected: ge_lookup("irt_test_global") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("global_unload_mod")
ge_define("irt_test_global", 800)
mock_irt_track_global("global_unload_mod", "irt_test_global")
mock_irt_unload_module("global_unload_mod")
expect(ge_lookup("irt_test_global")).to_equal(-1)
```

</details>

#### tombstones tracker slot after unload

1. mock irt init
2. mock irt begin module
3. mock irt track func
4. mock irt unload module
   - Expected: mock_irt_is_tracked("tombstone_mod") is false
   - Expected: mock_irt_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("tombstone_mod")
mock_irt_track_func("tombstone_mod", "fn_x")
mock_irt_unload_module("tombstone_mod")
expect(mock_irt_is_tracked("tombstone_mod")).to_equal(false)
expect(mock_irt_tracked_count()).to_equal(0)
```

</details>

#### returns 0 for untracked module

1. mock irt init
   - Expected: removed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
val removed = mock_irt_unload_module("never_tracked")
expect(removed).to_equal(0)
```

</details>

### init resets state

#### clears all tracking on init

1. mock irt init
2. mock irt begin module
3. mock irt track func
4. mock irt init
   - Expected: mock_irt_tracked_count() equals `0`
   - Expected: mock_irt_is_tracked("pre_init_mod") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_irt_init()
mock_irt_begin_module("pre_init_mod")
mock_irt_track_func("pre_init_mod", "fn_pre")
mock_irt_init()
expect(mock_irt_tracked_count()).to_equal(0)
expect(mock_irt_is_tracked("pre_init_mod")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/interp_resource_tracker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- func_table_remove
- struct_table_remove
- env_remove_global
- InterpreterResourceTracker
- module tracking
- name registration
- module unload
- init resets state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
