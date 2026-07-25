# Vfs Pure Fat Production Guard Specification

> 1.  assert no legacy fat driver

<!-- sdn-diagram:id=vfs_pure_fat_production_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vfs_pure_fat_production_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vfs_pure_fat_production_guard_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vfs_pure_fat_production_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vfs Pure Fat Production Guard Specification

## Scenarios

### SimpleOS production FAT purity guard

#### keeps VFS and boot production paths on the shared pure Simple FAT core

1.  assert no legacy fat driver
2.  assert no legacy fat driver
3.  assert no legacy fat driver
4.  assert no legacy fat driver
5.  assert no legacy fat driver
   - Expected: boot_source contains `use os.services.fat32.shared_fat32_driver.{" + shared_fat + " as Fat32Core}`
   - Expected: boot_source contains `boot_nvme_production_handoff_provision(g_adapter, transfer_evidence, lease)\n... (full value in folded executable source)`
   - Expected: boot_source contains `g_vfs_nvme_active_leases = [lease]\n    g_vfs_nvme_direct_adapter_leases = [l... (full value in folded executable source)`
   - Expected: mount_source contains `use std.fs_driver.fat32_stub.{" + fs_fat + "}`
   - Expected: shared_source contains `me fn sync() -> Result<bool, text>:`
   - Expected: shared_source contains `val rc = self.inner.sync()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_no_legacy_fat_driver("src/os/services/vfs/vfs_boot_init.spl")
_assert_no_legacy_fat_driver("src/os/services/vfs/vfs_init.spl")
_assert_no_legacy_fat_driver("src/os/services/vfs/vfs_write_ops.spl")
_assert_no_legacy_fat_driver("src/os/services/vfs/nvme_filesystem_mounts.spl")
_assert_no_legacy_fat_driver("src/os/kernel/boot/boot_fs_mount.spl")

val boot_source = read_file("src/os/services/vfs/vfs_boot_init.spl")
val mount_source = read_file("src/os/services/vfs/nvme_filesystem_mounts.spl")
val shared_source = read_file("src/os/services/fat32/shared_fat32_driver.spl")
val shared_fat = "SharedFat32" + "Driver"
val fs_fat = "FsFat32" + "Driver"
expect(boot_source.contains("use os.services.fat32.shared_fat32_driver.{" + shared_fat + " as Fat32Core}")).to_equal(true)
expect(boot_source.contains("boot_nvme_production_handoff_provision(g_adapter, transfer_evidence, lease)\n    var root = Fat32Core.new(g_adapter)")).to_equal(true)
expect(boot_source.contains("g_vfs_nvme_active_leases = [lease]\n    g_vfs_nvme_direct_adapter_leases = [lease]\n    g_vfs_nvme_direct_adapters = [g_adapter]")).to_equal(true)
expect(mount_source.contains("use std.fs_driver.fat32_stub.{" + fs_fat + "}")).to_equal(true)
expect(shared_source.contains("me fn sync() -> Result<bool, text>:")).to_equal(true)
expect(shared_source.contains("val rc = self.inner.sync()")).to_equal(true)
```

</details>

#### keeps the SimpleOS source tree off legacy FAT outside the isolated compatibility module

1.  assert os tree no production legacy fat driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_os_tree_no_production_legacy_fat_driver()
```

</details>

#### keeps legacy FAT unit coverage from instantiating the retired driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("test/unit/os/services/fat32/fat32_spec.spl")
val legacy_type = "Fat32" + "Driver"
expect(source.contains(legacy_type + ".new(")).to_equal(false)
expect(source.contains("resolve_path(")).to_equal(false)
expect(source.contains("readdir(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/vfs_pure_fat_production_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS production FAT purity guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
