# Vfs Rootfs Porting Specification

> <details>

<!-- sdn-diagram:id=vfs_rootfs_porting_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vfs_rootfs_porting_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vfs_rootfs_porting_spec -> std
vfs_rootfs_porting_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vfs_rootfs_porting_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vfs Rootfs Porting Specification

## Scenarios

### SimpleOS rootfs helpers — DBFS and NVFS porting

#### gates transitional C FAT32 bridge fallbacks when boot storage is pure Simple

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init_source = read_file("src/os/services/vfs/vfs_init.spl")
val write_source = read_file("src/os/services/vfs/vfs_write_ops.spl")

expect(init_source.contains("fn _vfs_c_fat32_bridge_allowed() -> bool:")).to_equal(true)
expect(init_source.contains("g_vfs_initialized and not vfs_boot_storage_is_pure_simple()")).to_equal(true)
expect(init_source.contains("if not _vfs_c_fat32_bridge_allowed():\n        return []\n    val signed_size = simpleos_fat32_read_path_size(path)")).to_equal(true)
expect(init_source.contains("if _vfs_c_fat32_bridge_allowed():\n        val direct_size = simpleos_fat32_read_path_size(name)")).to_equal(true)
expect(write_source.contains("vfs_boot_storage_is_pure_simple")).to_equal(true)
expect(write_source.contains("if _vfs_c_fat32_bridge_allowed():\n        if simpleos_fat32_read_path_size(name) > 0:")).to_equal(true)
```

</details>

#### DBFS rootfs can write, read, size, and existence-check through g_vfs_*

1.  clear vfs rootfs for test
   - Expected: _mount_hosted_rootfs_for_test(_dbfs_root()) is true
   - Expected: g_vfs_write_file_text("/etc/hostname", "simpleos-dbfs\n") is true
   - Expected: g_vfs_file_exists("/etc/hostname") is true
   - Expected: g_vfs_file_size("/etc/hostname").unwrap().to_i64() equals `14`
   - Expected: g_vfs_read_file_text("/etc/hostname") equals `simpleos-dbfs\n`
   - Expected: bytes.len() equals `14`
   - Expected: bytes[0] equals `115u8`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_dbfs_root())).to_equal(true)
expect(g_vfs_write_file_text("/etc/hostname", "simpleos-dbfs\n")).to_equal(true)
expect(g_vfs_file_exists("/etc/hostname")).to_equal(true)
expect(g_vfs_file_size("/etc/hostname").unwrap().to_i64()).to_equal(14)
expect(g_vfs_read_file_text("/etc/hostname")).to_equal("simpleos-dbfs\n")
val bytes = g_vfs_read_file_bytes("/etc/hostname")
expect(bytes.len()).to_equal(14)
expect(bytes[0]).to_equal(115u8)
```

</details>

#### NvfsPosix rootfs can write, read, size, and existence-check through g_vfs_*

1.  clear vfs rootfs for test
   - Expected: _mount_hosted_rootfs_for_test(_nvfs_posix_root()) is true
   - Expected: g_vfs_write_file_text("/sys/version.txt", "simpleos-nvfs\n") is true
   - Expected: g_vfs_file_exists("/sys/version.txt") is true
   - Expected: g_vfs_file_size("/sys/version.txt").unwrap().to_i64() equals `14`
   - Expected: g_vfs_read_file_text("/sys/version.txt") equals `simpleos-nvfs\n`
   - Expected: bytes.len() equals `14`
   - Expected: bytes[0] equals `115u8`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_nvfs_posix_root())).to_equal(true)
expect(g_vfs_write_file_text("/sys/version.txt", "simpleos-nvfs\n")).to_equal(true)
expect(g_vfs_file_exists("/sys/version.txt")).to_equal(true)
expect(g_vfs_file_size("/sys/version.txt").unwrap().to_i64()).to_equal(14)
expect(g_vfs_read_file_text("/sys/version.txt")).to_equal("simpleos-nvfs\n")
val bytes = g_vfs_read_file_bytes("/sys/version.txt")
expect(bytes.len()).to_equal(14)
expect(bytes[0]).to_equal(115u8)
```

</details>

#### NvfsPosix rootfs rewrite replaces instead of appending

1.  clear vfs rootfs for test
   - Expected: _mount_hosted_rootfs_for_test(_nvfs_posix_root()) is true
   - Expected: g_vfs_write_file_text("/sys/apps/hello_world", "first") is true
   - Expected: g_vfs_write_file_text("/sys/apps/hello_world", "second") is true
   - Expected: g_vfs_file_size("/sys/apps/hello_world").unwrap().to_i64() equals `6`
   - Expected: g_vfs_read_file_text("/sys/apps/hello_world") equals `second`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_nvfs_posix_root())).to_equal(true)
expect(g_vfs_write_file_text("/sys/apps/hello_world", "first")).to_equal(true)
expect(g_vfs_write_file_text("/sys/apps/hello_world", "second")).to_equal(true)
expect(g_vfs_file_size("/sys/apps/hello_world").unwrap().to_i64()).to_equal(6)
expect(g_vfs_read_file_text("/sys/apps/hello_world")).to_equal("second")
```

</details>

#### DBFS executable reads fall back to the mounted rootfs

1.  clear vfs rootfs for test
   - Expected: _mount_hosted_rootfs_for_test(_dbfs_root()) is true
   - Expected: g_vfs_write_file_text("/home/RUNME.ELF", "ELFAA") is true
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `69u8`
   - Expected: bytes[4] equals `65u8`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_dbfs_root())).to_equal(true)
expect(g_vfs_write_file_text("/home/RUNME.ELF", "ELFAA")).to_equal(true)
val bytes = g_vfs_read_executable_bytes("/home/RUNME.ELF")
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(69u8)
expect(bytes[4]).to_equal(65u8)
```

</details>

#### DBFS rootfs resolves executable bytes and parses ELF image

1.  clear vfs rootfs for test

2.  clear synthetic initramfs for test

3.  clear synthetic vfs for test
   - Expected: _mount_hosted_rootfs_for_test(_dbfs_root()) is true
   - Expected: g_vfs_write_file_bytes("/dbfs-init.elf", elf) is true
   - Expected: direct.len() equals `4100`
   - Expected: direct[0] equals `0x7Fu8`
   - Expected: direct[4] equals `2u8`
   - Expected: direct[18] equals `0xF3u8`
   - Expected: resolved.is_ok() is true
   - Expected: bytes.len() equals `4100`
   - Expected: bytes[0] equals `0x7Fu8`
   - Expected: bytes[4] equals `2u8`
   - Expected: bytes[18] equals `0xF3u8`
   - Expected: image.is_ok() is true
   - Expected: image.unwrap().entry > 0 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
expect(_mount_hosted_rootfs_for_test(_dbfs_root())).to_equal(true)
val elf = _make_elf64_rv64()
expect(g_vfs_write_file_bytes("/dbfs-init.elf", elf)).to_equal(true)
val direct = g_vfs_read_file_bytes("/dbfs-init.elf")
expect(direct.len()).to_equal(4100)
expect(direct[0]).to_equal(0x7Fu8)
expect(direct[4]).to_equal(2u8)
expect(direct[18]).to_equal(0xF3u8)
val resolved = resolve_executable_bytes("/dbfs-init.elf", Architecture.Riscv64)
expect(resolved.is_ok()).to_equal(true)
val bytes = resolved.unwrap()
expect(bytes.len()).to_equal(4100)
expect(bytes[0]).to_equal(0x7Fu8)
expect(bytes[4]).to_equal(2u8)
expect(bytes[18]).to_equal(0xF3u8)
val image = load_user_executable(bytes, Architecture.Riscv64)
expect(image.is_ok()).to_equal(true)
expect(image.unwrap().entry > 0).to_equal(true)
```

</details>

#### NvfsPosix executable reads fall back to the mounted rootfs

1.  clear vfs rootfs for test
   - Expected: _mount_hosted_rootfs_for_test(_nvfs_posix_root()) is true
   - Expected: g_vfs_write_file_text("/home/RUNME.ELF", "ELFAA") is true
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `69u8`
   - Expected: bytes[4] equals `65u8`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_nvfs_posix_root())).to_equal(true)
expect(g_vfs_write_file_text("/home/RUNME.ELF", "ELFAA")).to_equal(true)
val bytes = g_vfs_read_executable_bytes("/home/RUNME.ELF")
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(69u8)
expect(bytes[4]).to_equal(65u8)
```

</details>

#### AC-4: DbFsDriver open_on_device stores and round-trips ELF bytes via block device

1.  clear vfs rootfs for test

2.  clear synthetic initramfs for test

3.  clear synthetic vfs for test
   - Expected: mount_r.is_ok() is true
   - Expected: resolved.is_ok() is true
   - Expected: rbytes.len() equals `4100`
   - Expected: rbytes[0] equals `0x7Fu8`
   - Expected: rbytes[18] equals `0xF3u8`
   - Expected: image.is_ok() is true
   - Expected: entry > 0 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange: create a MemBlockDevice with 2048 sectors of 512 bytes each
val dev = MemBlockDevice.new(2048u64, 512u32)
# Open DbFsDriver with arena starting at LBA 4 (size_sectors - 4 arena blocks)
val driver_r = DbFsDriver.open_on_device(dev, 4i64, 2044i64)
expect(driver_r.is_ok()).to_equal(true)
val driver = driver_r.unwrap()
# Write ELF bytes via the same handle API used by the VFS dispatcher.
val elf = _make_elf64_rv64()
val open_r = driver.open_path(Path(raw: "sbin/init"), OpenFlags.create_write())
expect(open_r.is_ok()).to_equal(true)
val write_r = driver.write_bytes_handle(open_r.unwrap(), elf)
expect(write_r.is_ok()).to_equal(true)
val close_r = driver.close_handle(open_r.unwrap())
expect(close_r.is_ok()).to_equal(true)
# Mount the driver via vfs_mount_rootfs (new production API — AC-1 prerequisite)
_clear_vfs_rootfs_for_test()
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val mount_r = vfs_mount_rootfs(DriverInstance.DbFs(driver))
expect(mount_r.is_ok()).to_equal(true)
# Resolve via VFS → executable_source → elf_loader
val resolved = resolve_executable_bytes("/sbin/init", Architecture.Riscv64)
expect(resolved.is_ok()).to_equal(true)
val rbytes = resolved.unwrap()
expect(rbytes.len()).to_equal(4100)
expect(rbytes[0]).to_equal(0x7Fu8)
expect(rbytes[18]).to_equal(0xF3u8)
val image = load_user_executable(rbytes, Architecture.Riscv64)
expect(image.is_ok()).to_equal(true)
val entry = elf_image_entry(image.unwrap())
expect(entry > 0).to_equal(true)
```

</details>

#### AC-4: vfs_mount_rootfs registers driver at VFS root (file accessible after mount)

1.  clear vfs rootfs for test
   - Expected: mount_r.is_ok() is true
   - Expected: g_vfs_write_file_text("/etc/vfs_mount_test.txt", "mounted") is true
   - Expected: g_vfs_file_exists("/etc/vfs_mount_test.txt") is true
   - Expected: g_vfs_read_file_text("/etc/vfs_mount_test.txt") equals `mounted`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange: hosted DBFS driver (simpler path to verify vfs_mount_rootfs itself)
_clear_vfs_rootfs_for_test()
val mount_r = vfs_mount_rootfs(DriverInstance.DbFs(DbFsDriver.new_hosted()))
expect(mount_r.is_ok()).to_equal(true)
# Writing a file after mount confirms VFS root is live
expect(g_vfs_write_file_text("/etc/vfs_mount_test.txt", "mounted")).to_equal(true)
expect(g_vfs_file_exists("/etc/vfs_mount_test.txt")).to_equal(true)
expect(g_vfs_read_file_text("/etc/vfs_mount_test.txt")).to_equal("mounted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/vfs_rootfs_porting_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS rootfs helpers — DBFS and NVFS porting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
