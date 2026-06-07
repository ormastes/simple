# Gc Runtime Contract Specification

> <details>

<!-- sdn-diagram:id=gc_runtime_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_runtime_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_runtime_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_runtime_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Runtime Contract Specification

## Scenarios

### nogc_sync_mut GC and reference contracts

#### exports usable GC configuration and metadata types

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_config = GcConfig.default()
expect(default_config.young_size).to_equal(1024 * 1024)
expect(default_config.old_size).to_equal(4 * 1024 * 1024)
expect(default_config.incremental).to_equal(false)

val sized_config = GcConfig.with_heap_size(10 * 1024)
expect(sized_config.young_size).to_equal(2 * 1024)
expect(sized_config.old_size).to_equal(8 * 1024)

val header = GcObjectHeader.new(64, 7)
expect(header.size).to_equal(64)
expect(header.type_id).to_equal(7)
expect(header.color).to_equal(GcColor.White)
expect(header.marked).to_equal(false)
```

</details>

#### tracks empty GC stats deterministically

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = GcStats.new()
expect(stats.collections).to_equal(0)
expect(stats.objects_allocated).to_equal(0)
expect(stats.avg_pause_time()).to_equal(0)
expect(stats.survival_rate()).to_equal(0.0)
```

</details>

#### exports pointer ownership helpers from the no-GC backend

1. unique reset
   - Expected: unique_get(unique) equals `-1`
   - Expected: unique_get(moved) equals `41`
2. weak reset
   - Expected: weak_upgrade(weak) equals `77`
3. weak invalidate
   - Expected: weak_upgrade(weak) equals `-1`
4. handle pool new
   - Expected: handle_deref(handle) equals `13`
   - Expected: handle_free(handle) is true
   - Expected: handle_deref(handle) equals `-1`
   - Expected: state.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
unique_reset()
val unique = unique_new(41, "gc-contract")
val moved = unique_move(unique)
expect(unique_get(unique)).to_equal(-1)
expect(unique_get(moved)).to_equal(41)

weak_reset()
val weak_id = weak_register(77)
val weak = weak_create(weak_id)
expect(weak_upgrade(weak)).to_equal(77)
weak_invalidate(weak_id)
expect(weak_upgrade(weak)).to_equal(-1)

handle_pool_new(4)
val handle = handle_alloc(13)
expect(handle_deref(handle)).to_equal(13)
expect(handle_free(handle)).to_equal(true)
expect(handle_deref(handle)).to_equal(-1)

val state = ptr_state_valid()
expect(state.valid).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_sync_mut GC and reference contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
