# Nvfs Nvme Arena Specification

> <details>

<!-- sdn-diagram:id=nvfs_nvme_arena_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_nvme_arena_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_nvme_arena_spec -> std
nvfs_nvme_arena_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_nvme_arena_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Nvme Arena Specification

## Scenarios

### NVFS NVMe-backed arena — basic I/O

#### in-memory arena still works after adding NVMe support

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aid = arena_create_impl(0, 4096)
expect(aid > 0).to_equal(true)
val data: [u8] = [0x41, 0x42, 0x43, 0x44]
val w = arena_append_impl(aid, data, 0)
expect(w).to_equal(4)
val rd = arena_readv_impl(aid, 0, 4)
expect(rd.len() as i64).to_equal(4)
expect(rd[0]).to_equal(0x41)
expect(rd[3]).to_equal(0x44)
```

</details>

#### NVMe arena create requires block device

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aid = arena_create_nvme_impl(0, 4096, 100, 64)
expect(aid).to_equal(-1)
```

</details>

#### NVMe arena write and read round-trip

1. var dev =  make device

2. nvfs arena set block device
   - Expected: nvfs_arena_has_block_device() is true
   - Expected: aid > 0 is true
   - Expected: w equals `6`
   - Expected: arena_total_bytes_impl(aid) equals `6`
   - Expected: rd.len() as i64 equals `6`
   - Expected: rd[0] equals `0xDE`
   - Expected: rd[1] equals `0xAD`
   - Expected: rd[4] equals `0xCA`
   - Expected: rd[5] equals `0xFE`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
expect(nvfs_arena_has_block_device()).to_equal(true)
val aid = arena_create_nvme_impl(0, 4096, 0, 64)
expect(aid > 0).to_equal(true)
val data: [u8] = [0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE]
val w = arena_append_impl(aid, data, 0)
expect(w).to_equal(6)
expect(arena_total_bytes_impl(aid)).to_equal(6)
val rd = arena_readv_impl(aid, 0, 6)
expect(rd.len() as i64).to_equal(6)
expect(rd[0]).to_equal(0xDE)
expect(rd[1]).to_equal(0xAD)
expect(rd[4]).to_equal(0xCA)
expect(rd[5]).to_equal(0xFE)
```

</details>

#### NVMe arena supports multiple appends

1. var dev =  make device

2. nvfs arena set block device
   - Expected: aid > 0 is true
   - Expected: w1 equals `3`
   - Expected: w2 equals `2`
   - Expected: arena_total_bytes_impl(aid) equals `5`
   - Expected: rd.len() as i64 equals `5`
   - Expected: rd[0] equals `0x11`
   - Expected: rd[2] equals `0x33`
   - Expected: rd[3] equals `0x44`
   - Expected: rd[4] equals `0x55`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val aid = arena_create_nvme_impl(0, 4096, 0, 32)
expect(aid > 0).to_equal(true)
val d1: [u8] = [0x11, 0x22, 0x33]
val w1 = arena_append_impl(aid, d1, 0)
expect(w1).to_equal(3)
val d2: [u8] = [0x44, 0x55]
val w2 = arena_append_impl(aid, d2, 0)
expect(w2).to_equal(2)
expect(arena_total_bytes_impl(aid)).to_equal(5)
val rd = arena_readv_impl(aid, 0, 5)
expect(rd.len() as i64).to_equal(5)
expect(rd[0]).to_equal(0x11)
expect(rd[2]).to_equal(0x33)
expect(rd[3]).to_equal(0x44)
expect(rd[4]).to_equal(0x55)
```

</details>

#### NVMe arena seal prevents further writes

1. var dev =  make device

2. nvfs arena set block device
   - Expected: sealed is true
   - Expected: arena_is_sealed_impl(aid) is true
   - Expected: w2 equals `-2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val aid = arena_create_nvme_impl(0, 4096, 0, 32)
val d: [u8] = [0xAA]
val _ = arena_append_impl(aid, d, 0)
val sealed = arena_seal_impl(aid, 1)
expect(sealed).to_equal(true)
expect(arena_is_sealed_impl(aid)).to_equal(true)
val w2 = arena_append_impl(aid, d, 0)
expect(w2).to_equal(-2)
```

</details>

#### NVMe arena discard prevents reads

1. var dev =  make device

2. nvfs arena set block device
   - Expected: ok is true
   - Expected: rd.len() as i64 equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val aid = arena_create_nvme_impl(0, 4096, 0, 32)
val d: [u8] = [0xBB]
val _ = arena_append_impl(aid, d, 0)
val ok = arena_discard_impl(aid)
expect(ok).to_equal(true)
val rd = arena_readv_impl(aid, 0, 1)
expect(rd.len() as i64).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/nvfs_nvme_arena_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVFS NVMe-backed arena — basic I/O

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
