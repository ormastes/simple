# Nvfs Backend Parity Specification

> <details>

<!-- sdn-diagram:id=nvfs_backend_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_backend_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_backend_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_backend_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Backend Parity Specification

## Scenarios

### gc_async_mut NVFS backend facade

#### re-exports arena operations from the canonical backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aid = arena_create_impl(0, 4096)
expect(aid > 0).to_equal(true)
val data: [u8] = [0x41, 0x42]
expect(arena_append_impl(aid, data, 0)).to_equal(2)
val rd = arena_readv_impl(aid, 0, 2)
expect(rd.len() as i64).to_equal(2)
expect(rd[0]).to_equal(0x41)
expect(rd[1]).to_equal(0x42)
expect(arena_seal_impl(aid, 1)).to_equal(true)
expect(arena_is_sealed_impl(aid)).to_equal(true)
```

</details>

#### re-exports superblock and storage constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = NvfsSuperblock(
    magic: NVFS_MAGIC,
    version: 1,
    uuid_hi: 0,
    uuid_lo: 0,
    feature_bits: 0,
    mount_generation: 1,
    checkpoint_root: 2,
    replica_id: 0u8,
    valid: true,
    checksum: 0,
    compat_v1: false
)
expect(sb.magic).to_equal(NVFS_MAGIC)
expect(STORAGE_CLASS_DB_WAL > 0).to_equal(true)
expect(DURABILITY_DATA_DURABLE > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/fs_driver/nvfs_backend_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut NVFS backend facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
