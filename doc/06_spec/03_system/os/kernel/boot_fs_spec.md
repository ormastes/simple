# Boot Fs Specification

> <details>

<!-- sdn-diagram:id=boot_fs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=boot_fs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

boot_fs_spec -> std
boot_fs_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=boot_fs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Fs Specification

## Scenarios

### BootFsConfig — default configuration

#### default config targets NVFS

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = BootFsConfig.default_config()
expect(cfg.root_device).to_equal("nvme0n1")
expect(cfg.init_binary).to_equal("/sbin/init")
val is_nvfs = _boot_fs_type_is_nvfs(cfg.fs_type)
expect(is_nvfs).to_equal(true)
```

</details>

#### fat32 fallback config targets FAT32

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = BootFsConfig.fat32_fallback()
expect(cfg.init_binary).to_equal("/SYS/APPS/HELLOSMF.SMF")
val is_fat32 = _boot_fs_type_is_fat32(cfg.fs_type)
expect(is_fat32).to_equal(true)
```

</details>

### BootFsResult — result structure

#### result carries filesystem type and pid

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = BootFsResult(
    mounted:   true,
    fs_type:   BootFsType.Nvfs,
    init_pid:  42,
    init_path: "/sbin/init"
)
expect(result.mounted).to_equal(true)
expect(result.init_pid).to_equal(42)
expect(result.init_path).to_equal("/sbin/init")
```

</details>

#### unmounted result has negative pid

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = BootFsResult(
    mounted:   false,
    fs_type:   BootFsType.None_,
    init_pid:  -1,
    init_path: ""
)
expect(result.mounted).to_equal(false)
expect(result.init_pid).to_equal(-1)
```

</details>

### BootFsType — filesystem type enum

#### all four variants are distinct

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nvfs_ord = _boot_fs_type_ord(BootFsType.Nvfs)
val dbfs_ord = _boot_fs_type_ord(BootFsType.Dbfs)
val fat32_ord = _boot_fs_type_ord(BootFsType.Fat32)
val none_ord = _boot_fs_type_ord(BootFsType.None_)
expect(nvfs_ord != dbfs_ord).to_equal(true)
expect(dbfs_ord != fat32_ord).to_equal(true)
expect(fat32_ord != none_ord).to_equal(true)
```

</details>

### Boot FS module state — initial state

#### not mounted before boot_fs_sequence

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(boot_fs_is_mounted()).to_equal(false)
```

</details>

#### init pid is -1 before launch

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(boot_fs_init_pid()).to_equal(-1)
```

</details>

### Boot FS production sequence

#### keeps C-bridge NVFS and DBFS probing out of the default sequence

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(boot_fs_sequence_uses_c_bridge_roots_for_test()).to_equal(false)
expect(boot_fs_development_sequence_uses_c_bridge_roots_for_test()).to_equal(true)
```

</details>

### BootFsType.Dbfs — native DBFS boot support (AC-1)

#### AC-1: DBFS_ARENA_BASE_LBA constant is 4 (arena starts after LBA 0-3)

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DBFS superblock occupies LBA 2-3; arena must start at LBA 4
expect(DBFS_ARENA_BASE_LBA).to_equal(4i64)
```

</details>

#### AC-1: BootFsType.Dbfs is a valid distinct enum variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dbfs_ord = _boot_fs_type_ord(BootFsType.Dbfs)
expect(dbfs_ord).to_equal(2)
```

</details>

#### AC-1: BootFsResult can carry BootFsType.Dbfs

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = BootFsResult(
    mounted:   true,
    fs_type:   BootFsType.Dbfs,
    init_pid:  1,
    init_path: "/sbin/init"
)
val is_dbfs = _boot_fs_type_ord(result.fs_type) == 2
expect(is_dbfs).to_equal(true)
expect(result.mounted).to_equal(true)
expect(result.init_path).to_equal("/sbin/init")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/kernel/boot_fs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BootFsConfig — default configuration
- BootFsResult — result structure
- BootFsType — filesystem type enum
- Boot FS module state — initial state
- Boot FS production sequence
- BootFsType.Dbfs — native DBFS boot support (AC-1)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
