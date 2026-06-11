# Nvfs Posix Facade Specification

> 1. var table = FdTable new

<!-- sdn-diagram:id=nvfs_posix_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_posix_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_posix_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_posix_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Posix Facade Specification

## Scenarios

### gc_async_mut fs nvfs_posix facade

#### re-exports fd, cow, and driver contracts

1. var table = FdTable new
   - Expected: fd equals `1u32`
   - Expected: table.refcount(fd) equals `1u32`
   - Expected: table.dup(fd).is_ok() is true
   - Expected: table.refcount(fd) equals `2u32`
   - Expected: table.close(fd).is_ok() is true
   - Expected: table.refcount(fd) equals `1u32`
   - Expected: driver.name equals `nvfs-posix-v1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val null_fd = FdId.null()
expect(null_fd.is_null()).to_equal(true)
val shadow = CowShadow(base_arena: 7, staging: [1u8, 2u8], prefix_len: 3u64, suffix_start: 5u64)
expect(shadow.base_arena).to_equal(7)
var table = FdTable.new()
val fd = table.open(11, 0u32)
expect(fd).to_equal(1u32)
expect(table.refcount(fd)).to_equal(1u32)
expect(table.dup(fd).is_ok()).to_equal(true)
expect(table.refcount(fd)).to_equal(2u32)
expect(table.close(fd).is_ok()).to_equal(true)
expect(table.refcount(fd)).to_equal(1u32)
val driver = NvfsPosixDriver.new()
expect(driver.name).to_equal("nvfs-posix-v1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/fs/nvfs_posix/nvfs_posix_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut fs nvfs_posix facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
