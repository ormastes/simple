# Nvfs Superblock Disk Specification

> 1. var dev =  make device

<!-- sdn-diagram:id=nvfs_superblock_disk_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_superblock_disk_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_superblock_disk_spec -> std
nvfs_superblock_disk_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_superblock_disk_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Superblock Disk Specification

## Scenarios

### NVFS superblock disk I/O

#### device registration works

1. var dev =  make device

2. nvfs superblock set device
   - Expected: nvfs_superblock_has_device() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_superblock_set_device(dev)
expect(nvfs_superblock_has_device()).to_equal(true)
```

</details>

#### probe returns false on blank disk

1. var dev =  make device

2. nvfs superblock set device
   - Expected: found is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_superblock_set_device(dev)
val found = nvfs_superblock_probe_disk()
expect(found).to_equal(false)
```

</details>

#### format returns true on valid device

1. var dev =  make device

2. nvfs superblock set device
   - Expected: ok is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_superblock_set_device(dev)
val ok = nvfs_superblock_format_disk(0x1234u64, 0x5678u64)
expect(ok).to_equal(true)
```

</details>

#### raw sector write and read round-trips

1. var dev =  make device

2. nvfs superblock set device

3. var buf = rt bytes alloc
   - Expected: w is true
   - Expected: rd.len() >= 512 is true
   - Expected: rd[0] equals `0xAA`
   - Expected: rd[1] equals `0xBB`
   - Expected: rd[511] equals `0xFF`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_superblock_set_device(dev)
var buf = rt_bytes_alloc(512)
buf[0] = 0xAAu8
buf[1] = 0xBBu8
buf[511] = 0xFFu8
val w = nvfs_raw_write_sector(0u64, buf)
expect(w).to_equal(true)
val rd = nvfs_raw_read_sector(0u64)
expect(rd.len() >= 512).to_equal(true)
expect(rd[0]).to_equal(0xAA)
expect(rd[1]).to_equal(0xBB)
expect(rd[511]).to_equal(0xFF)
```

</details>

#### probe returns true after format

1. var dev =  make device

2. nvfs superblock set device
   - Expected: ok is true
   - Expected: found is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_superblock_set_device(dev)
val ok = nvfs_superblock_format_disk(0xAAAAu64, 0xBBBBu64)
expect(ok).to_equal(true)
val found = nvfs_superblock_probe_disk()
expect(found).to_equal(true)
```

</details>

#### read-back after format has correct fields

1. var dev =  make device

2. nvfs superblock set device
   - Expected: ok is true
   - Expected: sb.valid is true
   - Expected: sb.magic == NVFS_MAGIC is true
   - Expected: sb.version == NVFS_VERSION is true
   - Expected: sb.uuid_hi == 0x1111u64 is true
   - Expected: sb.uuid_lo == 0x2222u64 is true
   - Expected: sb.mount_generation == 1u64 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_superblock_set_device(dev)
val ok = nvfs_superblock_format_disk(0x1111u64, 0x2222u64)
expect(ok).to_equal(true)
val sb = nvfs_superblock_read_from_disk()
expect(sb.valid).to_equal(true)
expect(sb.magic == NVFS_MAGIC).to_equal(true)
expect(sb.version == NVFS_VERSION).to_equal(true)
expect(sb.uuid_hi == 0x1111u64).to_equal(true)
expect(sb.uuid_lo == 0x2222u64).to_equal(true)
expect(sb.mount_generation == 1u64).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/nvfs_superblock_disk_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVFS superblock disk I/O

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
