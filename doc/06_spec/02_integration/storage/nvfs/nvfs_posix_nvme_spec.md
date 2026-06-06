# Nvfs Posix Nvme Specification

> 1. var dev =  make posix device

<!-- sdn-diagram:id=nvfs_posix_nvme_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_posix_nvme_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_posix_nvme_spec -> std
nvfs_posix_nvme_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_posix_nvme_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Posix Nvme Specification

## Scenarios

### NvfsPosixDriver NVMe-backed open/read/write

#### write and read round-trip through NVMe backend

1. var dev =  make posix device

2. nvfs arena set block device
   - Expected: nvfs_arena_has_block_device() is true
   - Expected: trip.ok is true
   - Expected: trip.write_n equals `5`
   - Expected: trip.read_n equals `5`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_posix_device()
nvfs_arena_set_block_device(dev)
expect(nvfs_arena_has_block_device()).to_equal(true)
val data: [u8] = [0x48, 0x65, 0x6C, 0x6C, 0x6F]
# _nvme_next_block starts at 64; this test allocates base=64, data LBA=65
val trip = _do_round_trip(data, 65u64)
expect(trip.ok).to_equal(true)
expect(trip.write_n).to_equal(5)
expect(trip.read_n).to_equal(5)
```

</details>

#### data lands on NVMe sectors (raw sector verification)

1. var dev =  make posix device

2. nvfs arena set block device
   - Expected: trip.ok is true
   - Expected: trip.sec0 equals `0xDE`
   - Expected: trip.sec1 equals `0xAD`
   - Expected: trip.sec2 equals `0xBE`
   - Expected: trip.sec3 equals `0xEF`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_posix_device()
nvfs_arena_set_block_device(dev)
val data: [u8] = [0xDE, 0xAD, 0xBE, 0xEF]
# Test 1 consumed base=64; test 2 gets base=96, data LBA=97
val trip = _do_round_trip(data, 97u64)
expect(trip.ok).to_equal(true)
# bytes must appear at the start of the data sector
expect(trip.sec0).to_equal(0xDE)
expect(trip.sec1).to_equal(0xAD)
expect(trip.sec2).to_equal(0xBE)
expect(trip.sec3).to_equal(0xEF)
```

</details>

#### multiple files each get distinct NVMe sector regions

1. var dev =  make posix device

2. nvfs arena set block device
   - Expected: result.ok is true
   - Expected: result.rn1 equals `3`
   - Expected: result.rn2 equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_posix_device()
nvfs_arena_set_block_device(dev)
val result = _do_two_files(dev)
expect(result.ok).to_equal(true)
expect(result.rn1).to_equal(3)
expect(result.rn2).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/nvfs_posix_nvme_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NvfsPosixDriver NVMe-backed open/read/write

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
