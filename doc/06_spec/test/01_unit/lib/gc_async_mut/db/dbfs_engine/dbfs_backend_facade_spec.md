# Dbfs Backend Facade Specification

> <details>

<!-- sdn-diagram:id=dbfs_backend_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_backend_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_backend_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_backend_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Backend Facade Specification

## Scenarios

### gc_async_mut DBFS backend facade

#### re-exports filesystem driver and disk metadata contracts

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drv = DbfsFsDriver.new()
val fh = drv.open_path(Path(raw: "/facade.txt"), OpenFlags.create_write()).unwrap()
expect(fh.id > 0).to_equal(true)
expect(drv.write_handle(fh, "async dbfs").is_ok()).to_equal(true)
val rd = drv.open_path(Path(raw: "/facade.txt"), OpenFlags.read_only()).unwrap()
expect(drv.read_handle(rd, 10).unwrap()).to_equal("async dbfs")
val info = drv.stat_path(Path(raw: "/facade.txt")).unwrap()
expect(info.is_file).to_equal(true)
expect(info.size).to_equal(10)

val sb = DbfsSuperblock(
    magic: DBFS_MAGIC,
    version: DBFS_VERSION,
    uuid_hi: 1u64,
    uuid_lo: 2u64,
    mount_generation: 1u64,
    valid: true,
    checksum: 0
)
expect(sb.magic).to_equal(DBFS_MAGIC)
expect(sb.version).to_equal(DBFS_VERSION)

val arena = RawNvmeArena(base_block: 32, block_count: 8)
expect(arena.arena_handle().id).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_backend_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut DBFS backend facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
