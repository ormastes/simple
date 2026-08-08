# Kernel Mvp Specification

> <details>

<!-- sdn-diagram:id=kernel_mvp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kernel_mvp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kernel_mvp_spec -> std
kernel_mvp_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kernel_mvp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Mvp Specification

## Scenarios

### x86_64_ring3_smoke

#### selects the user selectors and aligned stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = X86ContextSwitch.create(0x401000, X86_64_USER_STACK_TOP, true)
expect(ctx.cs).to_equal((GDT_USER_CS as u64) | 3)
expect(ctx.ss).to_equal((GDT_USER_DS as u64) | 3)
expect(ctx.rsp % 16).to_equal(0)
```

</details>

### x86_64_fat32_exec

#### prepares canonical app bytes for the filesystem-backed path

-  clear vfs rootfs for test
-  clear synthetic vfs for test
-  set synthetic vfs file for test
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[1] equals `0x45.to_u8()`
-  clear synthetic vfs for test
-  clear vfs rootfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_vfs_rootfs_for_test()
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test("/sys/apps/hello_world", _make_x86_64_exec())
val bytes = _make_x86_64_exec()
expect(bytes.len()).to_be_greater_than(0)
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[1]).to_equal(0x45.to_u8())
_clear_synthetic_vfs_for_test()
_clear_vfs_rootfs_for_test()
```

</details>

### x86_64_hosted_rootfs

#### reads and writes through a DBFS-backed rootfs

-  clear synthetic vfs for test
-  clear vfs rootfs for test
   - Expected: _mount_hosted_rootfs_for_test(_dbfs_root()) is true
   - Expected: g_vfs_write_file_text("/sys/config/boot_mode", "dbfs\n") is true
   - Expected: g_vfs_file_exists("/sys/config/boot_mode") is true
   - Expected: g_vfs_file_size("/sys/config/boot_mode").unwrap().to_i64() equals `5`
   - Expected: g_vfs_read_file_text("/sys/config/boot_mode") equals `dbfs\n`
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `100u8`
-  clear vfs rootfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_dbfs_root())).to_equal(true)
expect(g_vfs_write_file_text("/sys/config/boot_mode", "dbfs\n")).to_equal(true)
expect(g_vfs_file_exists("/sys/config/boot_mode")).to_equal(true)
expect(g_vfs_file_size("/sys/config/boot_mode").unwrap().to_i64()).to_equal(5)
expect(g_vfs_read_file_text("/sys/config/boot_mode")).to_equal("dbfs\n")
val bytes = g_vfs_read_file_bytes("/sys/config/boot_mode")
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(100u8)
_clear_vfs_rootfs_for_test()
```

</details>

#### reads and writes through an NVFS-backed rootfs

-  clear synthetic vfs for test
-  clear vfs rootfs for test
   - Expected: _mount_hosted_rootfs_for_test(_nvfs_posix_root()) is true
   - Expected: g_vfs_write_file_text("/sys/config/boot_mode", "nvfs\n") is true
   - Expected: g_vfs_file_exists("/sys/config/boot_mode") is true
   - Expected: g_vfs_file_size("/sys/config/boot_mode").unwrap().to_i64() equals `5`
   - Expected: g_vfs_read_file_text("/sys/config/boot_mode") equals `nvfs\n`
   - Expected: bytes.len() equals `5`
   - Expected: bytes[0] equals `110u8`
-  clear vfs rootfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
_clear_vfs_rootfs_for_test()
expect(_mount_hosted_rootfs_for_test(_nvfs_posix_root())).to_equal(true)
expect(g_vfs_write_file_text("/sys/config/boot_mode", "nvfs\n")).to_equal(true)
expect(g_vfs_file_exists("/sys/config/boot_mode")).to_equal(true)
expect(g_vfs_file_size("/sys/config/boot_mode").unwrap().to_i64()).to_equal(5)
expect(g_vfs_read_file_text("/sys/config/boot_mode")).to_equal("nvfs\n")
val bytes = g_vfs_read_file_bytes("/sys/config/boot_mode")
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(110u8)
_clear_vfs_rootfs_for_test()
```

</details>

### x86_64_shell_smoke

#### shows dmesg in shell help output

- shell execute
   - Expected: shell.last_exit_code equals `0`
   - Expected: _has_line(shell.output_lines, "dmesg [N]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
shell.output_lines = []
shell.execute("help")
expect(shell.last_exit_code).to_equal(0)
expect(_has_line(shell.output_lines, "dmesg [N]")).to_equal(true)
```

</details>

### x86_64_fault_smoke

#### does not crash on an unknown syscall id

- log write
   - Expected: entries.len() equals `1`
   - Expected: entries[0].message equals `fault smoke`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = KernelLog.new(4)
log.write(3, 0, 0, "fault smoke")
val entries = log.read(0, 0, 4)
expect(entries.len()).to_equal(1)
expect(entries[0].message).to_equal("fault smoke")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/kernel_mvp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64_ring3_smoke
- x86_64_fat32_exec
- x86_64_hosted_rootfs
- x86_64_shell_smoke
- x86_64_fault_smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
