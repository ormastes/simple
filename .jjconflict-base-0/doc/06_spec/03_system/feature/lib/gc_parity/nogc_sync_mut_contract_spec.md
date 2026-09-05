# NoGC Sync Mutable Runtime Contracts

> The sync mutable runtime-family surface is no-GC-first. GC metadata, rooting-adjacent pointer helpers, and reference utilities that are needed by hosted sync code live under `nogc_sync_mut` unless a separate GC sync family is explicitly designed later.

<!-- sdn-diagram:id=nogc_sync_mut_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nogc_sync_mut_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nogc_sync_mut_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nogc_sync_mut_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NoGC Sync Mutable Runtime Contracts

The sync mutable runtime-family surface is no-GC-first. GC metadata, rooting-adjacent pointer helpers, and reference utilities that are needed by hosted sync code live under `nogc_sync_mut` unless a separate GC sync family is explicitly designed later.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/03_system/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The sync mutable runtime-family surface is no-GC-first. GC metadata,
rooting-adjacent pointer helpers, and reference utilities that are needed by
hosted sync code live under `nogc_sync_mut` unless a separate GC sync family is
explicitly designed later.

## Scenarios

### NoGC sync mutable runtime contracts

#### when configuring GC-adjacent hosted services

#### uses nogc_sync_mut for sync GC metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = GcConfig.with_heap_size(20 * 1024)
expect(config.young_size).to_equal(4 * 1024)
expect(config.old_size).to_equal(16 * 1024)

val stats = GcStats.new()
expect(stats.collections).to_equal(0)
expect(stats.bytes_allocated).to_equal(0)
```

</details>

#### when using pointer handles

#### uses nogc_sync_mut pointer helpers as the sync backend

1. handle pool new
   - Expected: handle_deref(handle) equals `99`
   - Expected: handle_free(handle) is true
   - Expected: handle_deref(handle) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
handle_pool_new(2)
val handle = handle_alloc(99)
expect(handle_deref(handle)).to_equal(99)
expect(handle_free(handle)).to_equal(true)
expect(handle_deref(handle)).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
