# Leak Check Specification

> <details>

<!-- sdn-diagram:id=leak_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=leak_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

leak_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=leak_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Leak Check Specification

## Scenarios

### Load/Unload cycle

#### module is tracked after load

- mock registry reset
- mock registry register
   - Expected: mock_registry_is_tracked("/lib/module_a.smf") is true
   - Expected: mock_registry_module_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/module_a.smf")
expect(mock_registry_is_tracked("/lib/module_a.smf")).to_equal(true)
expect(mock_registry_module_count()).to_equal(1)
```

</details>

#### module is not tracked before load

- mock registry reset
   - Expected: mock_registry_is_tracked("/lib/not_loaded.smf") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
expect(mock_registry_is_tracked("/lib/not_loaded.smf")).to_equal(false)
```

</details>

#### exec symbols tracked per module

- mock registry reset
- mock registry register
- mock registry add exec symbol
- mock registry add exec symbol
   - Expected: mock_exec_mapped_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/module_a.smf")
mock_registry_add_exec_symbol("/lib/module_a.smf", "fn_foo")
mock_registry_add_exec_symbol("/lib/module_a.smf", "fn_bar")
expect(mock_exec_mapped_count()).to_equal(2)
```

</details>

#### unload frees all exec symbols

- mock registry reset
- mock registry register
- mock registry add exec symbol
- mock registry add exec symbol
- mock registry unload
   - Expected: mock_exec_mapped_count() equals `0`
   - Expected: mock_exec_was_freed("fn_foo") is true
   - Expected: mock_exec_was_freed("fn_bar") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/module_a.smf")
mock_registry_add_exec_symbol("/lib/module_a.smf", "fn_foo")
mock_registry_add_exec_symbol("/lib/module_a.smf", "fn_bar")
mock_registry_unload("/lib/module_a.smf")
expect(mock_exec_mapped_count()).to_equal(0)
expect(mock_exec_was_freed("fn_foo")).to_equal(true)
expect(mock_exec_was_freed("fn_bar")).to_equal(true)
```

</details>

#### unload removes module from registry

- mock registry reset
- mock registry register
- mock registry unload
   - Expected: mock_registry_is_tracked("/lib/module_a.smf") is false
   - Expected: mock_registry_module_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/module_a.smf")
mock_registry_unload("/lib/module_a.smf")
expect(mock_registry_is_tracked("/lib/module_a.smf")).to_equal(false)
expect(mock_registry_module_count()).to_equal(0)
```

</details>

#### unload of unknown module is safe (no crash)

- mock registry reset
- mock registry unload
   - Expected: mock_registry_module_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_unload("/lib/nonexistent.smf")
expect(mock_registry_module_count()).to_equal(0)
```

</details>

### Hot-reload cycle

#### old symbols freed before new ones registered

- mock registry reset
- mock registry register
- mock registry add exec symbol
   - Expected: mock_exec_was_freed("hot_fn") is false
- mock registry unload
   - Expected: mock_exec_was_freed("hot_fn") is true
- mock exec reset
- mock registry register
- mock registry add exec symbol
   - Expected: mock_exec_mapped_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
# First load
mock_registry_register("/lib/module_hot.smf")
mock_registry_add_exec_symbol("/lib/module_hot.smf", "hot_fn")
expect(mock_exec_was_freed("hot_fn")).to_equal(false)
# Unload (simulates hot-reload)
mock_registry_unload("/lib/module_hot.smf")
expect(mock_exec_was_freed("hot_fn")).to_equal(true)
# Re-register (new load)
mock_exec_reset()
mock_registry_register("/lib/module_hot.smf")
mock_registry_add_exec_symbol("/lib/module_hot.smf", "hot_fn")
expect(mock_exec_mapped_count()).to_equal(1)
```

</details>

#### multiple load/unload cycles clean up correctly

- mock registry reset
- mock registry register
- mock registry add exec symbol
- mock registry unload
   - Expected: mock_registry_module_count() equals `0`
   - Expected: mock_exec_mapped_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
var cycle = 0
while cycle < 3:
    mock_registry_register("/lib/cycle_mod.smf")
    mock_registry_add_exec_symbol("/lib/cycle_mod.smf", "cycle_fn")
    mock_registry_unload("/lib/cycle_mod.smf")
    cycle = cycle + 1
expect(mock_registry_module_count()).to_equal(0)
expect(mock_exec_mapped_count()).to_equal(0)
```

</details>

### JIT symbol attribution

#### JIT symbol attributed to triggering module

- mock registry reset
- mock registry register
- mock registry add jit symbol
   - Expected: origin equals `/lib/caller.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/caller.smf")
mock_registry_add_jit_symbol("/lib/caller.smf", "Vec$i64_push")
val origin = mock_registry_get_jit_origin("Vec$i64_push")
expect(origin).to_equal("/lib/caller.smf")
```

</details>

#### JIT symbol freed when originating module unloads

- mock registry reset
- mock registry register
- mock registry add exec symbol
- mock registry add jit symbol
- mock registry unload
   - Expected: mock_exec_was_freed("Vec$i64_push") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/caller.smf")
mock_registry_add_exec_symbol("/lib/caller.smf", "Vec$i64_push")
mock_registry_add_jit_symbol("/lib/caller.smf", "Vec$i64_push")
mock_registry_unload("/lib/caller.smf")
expect(mock_exec_was_freed("Vec$i64_push")).to_equal(true)
```

</details>

#### JIT origin removed after unload

- mock registry reset
- mock registry register
- mock registry add jit symbol
- mock registry unload
   - Expected: origin equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/caller.smf")
mock_registry_add_jit_symbol("/lib/caller.smf", "Map$text_i64_insert")
mock_registry_unload("/lib/caller.smf")
val origin = mock_registry_get_jit_origin("Map$text_i64_insert")
expect(origin).to_equal("")
```

</details>

#### JIT symbols from different modules tracked independently

- mock registry reset
- mock registry register
- mock registry register
- mock registry add jit symbol
- mock registry add jit symbol
- mock registry unload
   - Expected: mock_registry_get_jit_origin("jit_sym_a") equals ``
   - Expected: mock_registry_get_jit_origin("jit_sym_b") equals `/lib/mod_b.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/mod_a.smf")
mock_registry_register("/lib/mod_b.smf")
mock_registry_add_jit_symbol("/lib/mod_a.smf", "jit_sym_a")
mock_registry_add_jit_symbol("/lib/mod_b.smf", "jit_sym_b")
mock_registry_unload("/lib/mod_a.smf")
# mod_a's JIT freed; mod_b's JIT still tracked
expect(mock_registry_get_jit_origin("jit_sym_a")).to_equal("")
expect(mock_registry_get_jit_origin("jit_sym_b")).to_equal("/lib/mod_b.smf")
```

</details>

### SMF cache ref counting

#### SMF ref count increases when module accesses it

- mock smf reset
- mock smf inc
   - Expected: mock_smf_get_count("/cache/std.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_smf_reset()
mock_smf_inc("/cache/std.smf")
expect(mock_smf_get_count("/cache/std.smf")).to_equal(1)
```

</details>

#### SMF not evicted while ref count > 0

- mock smf reset
- mock smf inc
- mock smf inc
- mock smf dec
   - Expected: mock_smf_was_evicted("/cache/shared.smf") is false
   - Expected: mock_smf_get_count("/cache/shared.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_smf_reset()
mock_smf_inc("/cache/shared.smf")
mock_smf_inc("/cache/shared.smf")
mock_smf_dec("/cache/shared.smf")
expect(mock_smf_was_evicted("/cache/shared.smf")).to_equal(false)
expect(mock_smf_get_count("/cache/shared.smf")).to_equal(1)
```

</details>

#### SMF evicted when last module unloads

- mock smf reset
- mock smf inc
- mock smf dec
   - Expected: mock_smf_was_evicted("/cache/shared.smf") is true
   - Expected: mock_smf_get_count("/cache/shared.smf") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_smf_reset()
mock_smf_inc("/cache/shared.smf")
mock_smf_dec("/cache/shared.smf")
expect(mock_smf_was_evicted("/cache/shared.smf")).to_equal(true)
expect(mock_smf_get_count("/cache/shared.smf")).to_equal(0)
```

</details>

#### multiple modules share SMF — eviction only on last unload

- mock registry reset
- mock registry register
- mock registry register
- mock registry add smf
- mock registry add smf
- mock registry unload
   - Expected: mock_smf_was_evicted("/cache/shared.smf") is false
   - Expected: mock_smf_get_count("/cache/shared.smf") equals `1`
- mock registry unload
   - Expected: mock_smf_was_evicted("/cache/shared.smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/mod_a.smf")
mock_registry_register("/lib/mod_b.smf")
mock_registry_add_smf("/lib/mod_a.smf", "/cache/shared.smf")
mock_registry_add_smf("/lib/mod_b.smf", "/cache/shared.smf")
# Unload first module — SMF still ref'd by mod_b
mock_registry_unload("/lib/mod_a.smf")
expect(mock_smf_was_evicted("/cache/shared.smf")).to_equal(false)
expect(mock_smf_get_count("/cache/shared.smf")).to_equal(1)
# Unload second module — SMF now evicted
mock_registry_unload("/lib/mod_b.smf")
expect(mock_smf_was_evicted("/cache/shared.smf")).to_equal(true)
```

</details>

### Full teardown

#### teardown frees all modules

- mock registry reset
- mock registry register
- mock registry register
- mock registry register
- mock registry add exec symbol
- mock registry add exec symbol
- mock registry unload
   - Expected: mock_registry_module_count() equals `0`
   - Expected: mock_exec_mapped_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/mod_a.smf")
mock_registry_register("/lib/mod_b.smf")
mock_registry_register("/lib/mod_c.smf")
mock_registry_add_exec_symbol("/lib/mod_a.smf", "fn_a")
mock_registry_add_exec_symbol("/lib/mod_b.smf", "fn_b")
# Simulate destroy() — unload all
val paths_to_unload = ["/lib/mod_a.smf", "/lib/mod_b.smf", "/lib/mod_c.smf"]
for path in paths_to_unload:
    mock_registry_unload(path)
expect(mock_registry_module_count()).to_equal(0)
expect(mock_exec_mapped_count()).to_equal(0)
```

</details>

#### teardown with zero modules is safe

- mock registry reset
   - Expected: mock_registry_module_count() equals `0`
   - Expected: mock_exec_mapped_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
# No modules loaded — teardown should be a no-op
expect(mock_registry_module_count()).to_equal(0)
expect(mock_exec_mapped_count()).to_equal(0)
```

</details>

#### after teardown, re-registration works (REPL restart)

- mock registry reset
- mock registry register
- mock registry add exec symbol
- mock registry unload
- mock exec reset
- mock registry register
- mock registry add exec symbol
   - Expected: mock_registry_is_tracked("/lib/mod.smf") is true
   - Expected: mock_exec_mapped_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_registry_reset()
mock_registry_register("/lib/mod.smf")
mock_registry_add_exec_symbol("/lib/mod.smf", "fn_x")
mock_registry_unload("/lib/mod.smf")
mock_exec_reset()
# Re-register after teardown (simulates REPL restart)
mock_registry_register("/lib/mod.smf")
mock_registry_add_exec_symbol("/lib/mod.smf", "fn_x")
expect(mock_registry_is_tracked("/lib/mod.smf")).to_equal(true)
expect(mock_exec_mapped_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/leak_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Load/Unload cycle
- Hot-reload cycle
- JIT symbol attribution
- SMF cache ref counting
- Full teardown

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
