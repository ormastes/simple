# Nvfs Facade Specification

> <details>

<!-- sdn-diagram:id=nvfs_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Facade Specification

## Scenarios

### gc_async_mut fs nvfs facade

#### re-exports NVFS extent, superblock, and arena contract records

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = ArenaHandle(id: 7)
expect(handle.id).to_equal(7)
val extent = ExtentMapEntry(logical_off: 0, arena_id: handle.id, phys_off: 4096, length: 8192, generation: 3)
expect(extent.arena_id).to_equal(7)
expect(extent.length).to_equal(8192)
val header = SuperblockHeader(
    magic: 0x4e564653,
    version_major: 1,
    version_minor: 0,
    fs_uuid_lo: 11,
    fs_uuid_hi: 22,
    checkpoint_gen: 5,
    created_unix_ns: 123456
)
expect(header.version_major).to_equal(1)
expect(header.checkpoint_gen).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/fs/nvfs/nvfs_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut fs nvfs facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
