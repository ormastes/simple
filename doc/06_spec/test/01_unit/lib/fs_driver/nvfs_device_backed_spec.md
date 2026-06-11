# Nvfs Device Backed Specification

> <details>

<!-- sdn-diagram:id=nvfs_device_backed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_device_backed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_device_backed_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_device_backed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Device Backed Specification

## Scenarios

### NvfsDriver device-backed construction

#### opens on the shared BlockDevice surface used by NVMe filesystem leases

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(1024u64, 512u32)
val opened = NvfsDriver.new_on_device("nvfs-device", dev, 8i64, 256i64)
expect(opened.is_ok()).to_equal(true)
val driver = opened.unwrap()
expect(driver.name).to_equal("nvfs-device")
expect(driver.preferred_io_unit_bytes()).to_equal(512)
expect(driver.preferred_batch_bytes()).to_equal(512)
expect(driver.has_trim_support()).to_equal(false)
expect(driver.has_write_zeroes_support()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/nvfs_device_backed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NvfsDriver device-backed construction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
