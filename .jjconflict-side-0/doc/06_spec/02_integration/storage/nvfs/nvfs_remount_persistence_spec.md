# Nvfs Remount Persistence Specification

> <details>

<!-- sdn-diagram:id=nvfs_remount_persistence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_remount_persistence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_remount_persistence_spec -> std
nvfs_remount_persistence_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_remount_persistence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Remount Persistence Specification

## Scenarios

### NVFS remount persistence — data survives across mount cycles

#### superblock survives format then re-read

- var dev =  make device
- nvfs arena set block device
- nvfs superblock set device
   - Expected: fmt_ok is true
   - Expected: probe_ok is true
   - Expected: sb.valid is true
   - Expected: sb.uuid_hi == 0xCAFEu64 is true
   - Expected: sb.uuid_lo == 0xBABEu64 is true
   - Expected: sb.mount_generation == 1u64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
nvfs_superblock_set_device(dev)
val fmt_ok = nvfs_superblock_format_disk(0xCAFEu64, 0xBABEu64)
expect(fmt_ok).to_equal(true)
val probe_ok = nvfs_superblock_probe_disk()
expect(probe_ok).to_equal(true)
val sb = nvfs_superblock_read_from_disk()
expect(sb.valid).to_equal(true)
expect(sb.uuid_hi == 0xCAFEu64).to_equal(true)
expect(sb.uuid_lo == 0xBABEu64).to_equal(true)
expect(sb.mount_generation == 1u64).to_equal(true)
```

</details>

#### arena data written to NVMe sectors can be read back via raw sector read

- var dev =  make device
- nvfs arena set block device
   - Expected: aid > 0 is true
   - Expected: w equals `8`
   - Expected: raw.len() >= 8 is true
   - Expected: raw[0] equals `0xDE`
   - Expected: raw[1] equals `0xAD`
   - Expected: raw[2] equals `0xBE`
   - Expected: raw[3] equals `0xEF`
   - Expected: raw[4] equals `0x01`
   - Expected: raw[7] equals `0x04`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val aid = arena_create_nvme_impl(0, 4096, 4, 32)
expect(aid > 0).to_equal(true)
val data: [u8] = [0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x02, 0x03, 0x04]
val w = arena_append_impl(aid, data, 0)
expect(w).to_equal(8)
val raw = nvfs_raw_read_sector(5u64)
expect(raw.len() >= 8).to_equal(true)
expect(raw[0]).to_equal(0xDE)
expect(raw[1]).to_equal(0xAD)
expect(raw[2]).to_equal(0xBE)
expect(raw[3]).to_equal(0xEF)
expect(raw[4]).to_equal(0x01)
expect(raw[7]).to_equal(0x04)
```

</details>

#### full write-read cycle: format superblock + write arena + read both back

- var dev =  make device
- nvfs arena set block device
- nvfs superblock set device
   - Expected: fmt_ok is true
   - Expected: aid > 0 is true
   - Expected: w equals `5`
   - Expected: sb.valid is true
   - Expected: sb.uuid_hi == 0x1111u64 is true
   - Expected: arena_data.len() as i64 equals `5`
   - Expected: arena_data[0] equals `0x41`
   - Expected: arena_data[4] equals `0x45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
nvfs_superblock_set_device(dev)
val fmt_ok = nvfs_superblock_format_disk(0x1111u64, 0x2222u64)
expect(fmt_ok).to_equal(true)
val aid = arena_create_nvme_impl(0, 4096, 8, 16)
expect(aid > 0).to_equal(true)
val payload: [u8] = [0x41, 0x42, 0x43, 0x44, 0x45]
val w = arena_append_impl(aid, payload, 0)
expect(w).to_equal(5)
val sb = nvfs_superblock_read_from_disk()
expect(sb.valid).to_equal(true)
expect(sb.uuid_hi == 0x1111u64).to_equal(true)
val arena_data = arena_readv_impl(aid, 0, 5)
expect(arena_data.len() as i64).to_equal(5)
expect(arena_data[0]).to_equal(0x41)
expect(arena_data[4]).to_equal(0x45)
```

</details>

#### multiple arena writes persist across reads

- var dev =  make device
- nvfs arena set block device
   - Expected: aid > 0 is true
   - Expected: w1 equals `3`
   - Expected: w2 equals `2`
   - Expected: arena_total_bytes_impl(aid) equals `5`
   - Expected: raw[0] equals `0x10`
   - Expected: raw[1] equals `0x20`
   - Expected: raw[2] equals `0x30`
   - Expected: raw[3] equals `0x40`
   - Expected: raw[4] equals `0x50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val aid = arena_create_nvme_impl(0, 4096, 16, 16)
expect(aid > 0).to_equal(true)
val d1: [u8] = [0x10, 0x20, 0x30]
val w1 = arena_append_impl(aid, d1, 0)
expect(w1).to_equal(3)
val d2: [u8] = [0x40, 0x50]
val w2 = arena_append_impl(aid, d2, 0)
expect(w2).to_equal(2)
expect(arena_total_bytes_impl(aid)).to_equal(5)
val raw = nvfs_raw_read_sector(17u64)
expect(raw[0]).to_equal(0x10)
expect(raw[1]).to_equal(0x20)
expect(raw[2]).to_equal(0x30)
expect(raw[3]).to_equal(0x40)
expect(raw[4]).to_equal(0x50)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/nvfs_remount_persistence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVFS remount persistence — data survives across mount cycles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
