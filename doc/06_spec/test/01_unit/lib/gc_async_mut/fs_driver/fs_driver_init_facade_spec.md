# Fs Driver Init Facade Specification

> <details>

<!-- sdn-diagram:id=fs_driver_init_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fs_driver_init_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fs_driver_init_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fs_driver_init_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fs Driver Init Facade Specification

## Scenarios

### gc_async_mut fs_driver package facade

#### re-exports core fs-driver contracts and NVFS helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Path.root().raw).to_equal("/")
expect(OpenFlags.create_write().is_writable()).to_equal(true)
expect(MountOptions.read_only().read_only).to_equal(true)
expect(FsCapabilitySet.of(Capability.PosixCompat).has(Capability.PosixCompat)).to_equal(true)
expect(errno_of(FsError.NotFound)).to_equal(2)
val driver = NvfsDriver.new("gc-async-fs-driver")
expect(driver.preferred_io_unit_bytes()).to_equal(512)
val aid = arena_create_impl(0, 64)
val data: [u8] = [0x66, 0x73]
expect(arena_append_impl(aid, data, 0)).to_equal(2)
expect(arena_total_bytes_impl(aid)).to_equal(2)
expect(NVFS_MAGIC > 0u32).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/fs_driver/fs_driver_init_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut fs_driver package facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
