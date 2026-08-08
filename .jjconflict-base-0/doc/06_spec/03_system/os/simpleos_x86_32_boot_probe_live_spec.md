# Simpleos X86 32 Boot Probe Live Specification

> _Live x86_32 validation, disabled unless SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1._

<!-- sdn-diagram:id=simpleos_x86_32_boot_probe_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_x86_32_boot_probe_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_x86_32_boot_probe_live_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_x86_32_boot_probe_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos X86 32 Boot Probe Live Specification

## Scenarios

### SimpleOS x86_32 boot-probe live QEMU lane
_Live x86_32 validation, disabled unless SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1._

#### boots the x86_32 browser probe to spl_start

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_browser_probe.elf"
    val build = _build_probe(output_path)
    if not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe(output_path)
        val serial = result[0]
        if not serial.contains(PROBE_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] qemu exit={result[1]}"
            print serial
        expect(serial.contains(PROBE_MARKER)).to_equal(true)
```

</details>

#### routes a live int 0x80 trap through the i386 IDT gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_int80_probe.elf"
    val build = _build_int80_probe(output_path)
    if not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe(output_path)
        val serial = result[0]
        if not serial.contains(INT80_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] int80 qemu exit={result[1]}"
            print serial
        expect(serial.contains(INT80_MARKER)).to_equal(true)
```

</details>

#### routes live int 0x80 through the installed Simple syscall runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_int80_syscall_probe.elf"
    val build = _build_int80_syscall_probe(output_path)
    if not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe(output_path)
        val serial = result[0]
        if not serial.contains(INT80_SYSCALL_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] int80 syscall qemu exit={result[1]}"
            print serial
        expect(serial.contains(INT80_SYSCALL_MARKER)).to_equal(true)
```

</details>

#### routes live x86_32 process and shell smoke through the installed runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_int80_process_shell_probe.elf"
    val build = _build_int80_process_shell_probe(output_path)
    if not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe(output_path)
        val serial = result[0]
        if not serial.contains(PROCESS_SHELL_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] int80 process shell qemu exit={result[1]}"
            print serial
        expect(serial.contains(PROCESS_CREATE_MARKER)).to_equal(true)
        expect(serial.contains(PROCESS_BRK_MARKER)).to_equal(true)
        expect(serial.contains(PROCESS_REBOOT_MARKER)).to_equal(true)
        expect(serial.contains(PROCESS_DIAGNOSTICS_MARKER)).to_equal(true)
        expect(serial.contains(SHELL_SMOKE_MARKER)).to_equal(true)
        expect(serial.contains(PROCESS_SHELL_MARKER)).to_equal(true)
```

</details>

#### executes x86_32 filesystem-backed app payloads from a FAT32 initrd image

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _enabled():
    expect(_enabled()).to_equal(false)
elif not _qemu_available():
    expect(_qemu_available()).to_equal(false)
else:
    val output_path = "build/os/simpleos_x86_32_initrd_fs_exec_probe.elf"
    val image_path = "build/os/simpleos_x86_32_fs_exec.img"
    val image = _ensure_x86_32_fs_exec_image(image_path)
    val build = _build_initrd_fs_exec_probe(output_path)
    if not image[0]:
        expect(false).to_equal(true)
    elif not build[0]:
        expect(_build_prerequisite_missing(build[1])).to_equal(true)
    else:
        val result = _run_probe_with_initrd(output_path, image_path)
        val serial = result[0]
        if not serial.contains(FS_EXEC_MARKER):
            print "[simpleos_x86_32_boot_probe_live_spec] initrd fs-exec qemu exit={result[1]}"
            print serial
        expect(serial.contains(FS_INITRD_MARKER)).to_equal(true)
        expect(serial.contains(FS_HELLO_MARKER)).to_equal(true)
        expect(serial.contains(FS_BROWSER_MARKER)).to_equal(true)
        expect(serial.contains(FS_ARCH_MARKER)).to_equal(true)
        expect(serial.contains(FS_EXEC_MARKER)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_x86_32_boot_probe_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS x86_32 boot-probe live QEMU lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
