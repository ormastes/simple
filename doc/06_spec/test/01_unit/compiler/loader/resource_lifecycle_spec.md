# resource_lifecycle_spec

> Resource Lifecycle Manager Specification

<!-- sdn-diagram:id=resource_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_lifecycle_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# resource_lifecycle_spec

Resource Lifecycle Manager Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2001-2010 |
| Category | Infrastructure |
| Status | Active |
| Design | doc/05_design/resource_lifecycle_manager_design.md |
| Source | `test/01_unit/compiler/loader/resource_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Resource Lifecycle Manager Specification

Tests the resource lifecycle manager's logic using mock implementations.
The actual compiler modules depend on FFI/loader internals not available
in interpreter mode, so we mock the core abstractions here.

## Scenarios

### ResourceLifecycleManager

### module tracking

#### tracks a new module after on_module_load

1. lm reset
2. lm on module load
   - Expected: lm_is_tracked("/test/mod_a.smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_reset()
lm_on_module_load("/test/mod_a.smf")
expect(lm_is_tracked("/test/mod_a.smf")).to_equal(true)
```

</details>

#### reports false for untracked module

1. lm reset
   - Expected: lm_is_tracked("/nonexistent") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_reset()
expect(lm_is_tracked("/nonexistent")).to_equal(false)
```

</details>

#### counts multiple tracked modules

1. lm reset
2. lm on module load
3. lm on module load
   - Expected: lm_tracked_module_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_reset()
lm_on_module_load("/a.smf")
lm_on_module_load("/b.smf")
expect(lm_tracked_module_count()).to_equal(2)
```

</details>

### symbol and JIT tracking

#### records symbols mapped for a module

1. lm reset
2. lm on module load
3. lm on symbol mapped
4. lm on symbol mapped
   - Expected: lm_get_symbols_for("/mod.smf") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_reset()
lm_on_module_load("/mod.smf")
lm_on_symbol_mapped("/mod.smf", "func_a")
lm_on_symbol_mapped("/mod.smf", "func_b")
expect(lm_get_symbols_for("/mod.smf")).to_equal(2)
```

</details>

#### records JIT symbol origin for unload

1. lm reset
2. lm on module load
3. lm on jit triggered
   - Expected: lm_tracked_jit_count() equals `1`
   - Expected: origin equals `/mod.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_reset()
lm_on_module_load("/mod.smf")
lm_on_jit_triggered("/mod.smf", "Vec$i64_push")
expect(lm_tracked_jit_count()).to_equal(1)
val origin = lm_get_jit_origin("Vec$i64_push")
expect(origin).to_equal("/mod.smf")
```

</details>

#### returns empty for unknown JIT symbol

1. lm reset
   - Expected: origin equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_reset()
val origin = lm_get_jit_origin("nonexistent")
expect(origin).to_equal("")
```

</details>

### metadata and SMF tracking

#### records metadata path for module

1. lm reset
2. lm on module load
3. lm on metadata loaded
   - Expected: lm_is_tracked("/mod.smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_reset()
lm_on_module_load("/mod.smf")
lm_on_metadata_loaded("/mod.smf", "/mod.smf")
expect(lm_is_tracked("/mod.smf")).to_equal(true)
```

</details>

#### tracks SMF cache access

1. lm reset
2. smf reset
3. lm on module load
4. lm on smf accessed
5. smf inc
   - Expected: smf_get_ref_count("/shared.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_reset()
smf_reset()
lm_on_module_load("/mod.smf")
lm_on_smf_accessed("/mod.smf", "/shared.smf")
smf_inc("/shared.smf")
expect(smf_get_ref_count("/shared.smf")).to_equal(1)
```

</details>

### SmfCacheManager

### ref counting

#### starts at zero ref count

1. smf reset
   - Expected: smf_get_ref_count("/test.smf") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_reset()
expect(smf_get_ref_count("/test.smf")).to_equal(0)
```

</details>

#### increments ref count

1. smf reset
2. smf inc
   - Expected: smf_get_ref_count("/test.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_reset()
smf_inc("/test.smf")
expect(smf_get_ref_count("/test.smf")).to_equal(1)
```

</details>

#### increments multiple times

1. smf reset
2. smf inc
3. smf inc
4. smf inc
   - Expected: smf_get_ref_count("/test.smf") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_reset()
smf_inc("/test.smf")
smf_inc("/test.smf")
smf_inc("/test.smf")
expect(smf_get_ref_count("/test.smf")).to_equal(3)
```

</details>

#### decrements ref count

1. smf reset
2. smf inc
3. smf inc
4. smf dec
   - Expected: smf_get_ref_count("/test.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_reset()
smf_inc("/test.smf")
smf_inc("/test.smf")
smf_dec("/test.smf")
expect(smf_get_ref_count("/test.smf")).to_equal(1)
```

</details>

#### evicts when ref count reaches zero

1. smf reset
2. smf inc
3. smf dec
   - Expected: smf_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_reset()
smf_inc("/test.smf")
smf_dec("/test.smf")
expect(smf_tracked_count()).to_equal(0)
```

</details>

### multi-path tracking

#### tracks independent paths

1. smf reset
2. smf inc
3. smf inc
   - Expected: smf_tracked_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_reset()
smf_inc("/a.smf")
smf_inc("/b.smf")
expect(smf_tracked_count()).to_equal(2)
```

</details>

#### force clear resets all

1. smf reset
2. smf inc
3. smf inc
4. smf force clear
   - Expected: smf_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_reset()
smf_inc("/a.smf")
smf_inc("/b.smf")
smf_force_clear()
expect(smf_tracked_count()).to_equal(0)
```

</details>

#### ignores dec on untracked path

1. smf reset
2. smf dec
   - Expected: smf_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smf_reset()
smf_dec("/nonexistent.smf")
expect(smf_tracked_count()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/resource_lifecycle_manager_design.md](doc/05_design/resource_lifecycle_manager_design.md)


</details>
