# Nvfs Elf Load Specification

> 1. var dev =  make device

<!-- sdn-diagram:id=nvfs_elf_load_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_elf_load_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_elf_load_spec -> std
nvfs_elf_load_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_elf_load_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Elf Load Specification

## Scenarios

### ELF binary from NVFS arena — store and load chain

#### synthetic ELF64 x86 round-trips through NVMe arena

1. var dev =  make device

2. nvfs arena set block device
   - Expected: elf_bytes.len() as i64 equals `120`
   - Expected: elf_bytes[0] equals `0x7F`
   - Expected: elf_bytes[1] equals `0x45`
   - Expected: aid > 0 is true
   - Expected: w equals `120`
   - Expected: arena_total_bytes_impl(aid) equals `120`
   - Expected: readback.len() as i64 equals `120`
   - Expected: readback[0] equals `0x7F`
   - Expected: readback[1] equals `0x45`
   - Expected: readback[2] equals `0x4C`
   - Expected: readback[3] equals `0x46`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val elf_bytes = _make_elf64_x86()
expect(elf_bytes.len() as i64).to_equal(120)
expect(elf_bytes[0]).to_equal(0x7F)
expect(elf_bytes[1]).to_equal(0x45)
val aid = arena_create_nvme_impl(0, 4096, 4, 32)
expect(aid > 0).to_equal(true)
val w = arena_append_impl(aid, elf_bytes, 0)
expect(w).to_equal(120)
expect(arena_total_bytes_impl(aid)).to_equal(120)
val readback = arena_readv_impl(aid, 0, 120)
expect(readback.len() as i64).to_equal(120)
expect(readback[0]).to_equal(0x7F)
expect(readback[1]).to_equal(0x45)
expect(readback[2]).to_equal(0x4C)
expect(readback[3]).to_equal(0x46)
```

</details>

#### ELF loader parses bytes read from NVMe arena

1. var dev =  make device

2. nvfs arena set block device
   - Expected: aid > 0 is true
   - Expected: w equals `120`
   - Expected: readback.len() as i64 equals `120`
   - Expected: result.is_ok() is true
   - Expected: image.entry > 0 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val elf_bytes = _make_elf64_x86()
val aid = arena_create_nvme_impl(0, 4096, 40, 32)
expect(aid > 0).to_equal(true)
val w = arena_append_impl(aid, elf_bytes, 0)
expect(w).to_equal(120)
val readback = arena_readv_impl(aid, 0, 120)
expect(readback.len() as i64).to_equal(120)
val result = load_user_executable(readback, Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val image = result.unwrap()
expect(image.entry > 0).to_equal(true)
```

</details>

#### boot_fs_load_and_validate_elf rejects too-small arena data

1. var dev =  make device

2. nvfs arena set block device
   - Expected: aid > 0 is true
   - Expected: w equals `2`
   - Expected: readback.len() as i64 equals `2`
   - Expected: result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device()
nvfs_arena_set_block_device(dev)
val aid = arena_create_nvme_impl(0, 4096, 76, 8)
expect(aid > 0).to_equal(true)
val tiny: [u8] = [0x00, 0x01]
val w = arena_append_impl(aid, tiny, 0)
expect(w).to_equal(2)
val readback = arena_readv_impl(aid, 0, 2)
expect(readback.len() as i64).to_equal(2)
val result = load_user_executable(readback, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/kernel/nvfs_elf_load_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ELF binary from NVFS arena — store and load chain

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
