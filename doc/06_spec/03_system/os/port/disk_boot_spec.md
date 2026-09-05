# Disk Boot Specification

> _Env-gated checks for booting SimpleOS from a FAT32 disk image under QEMU._

<!-- sdn-diagram:id=disk_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=disk_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

disk_boot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=disk_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Disk Boot Specification

## Scenarios

### SimpleOS QEMU FAT32 disk-boot smoke
_Env-gated checks for booting SimpleOS from a FAT32 disk image under QEMU._

#### skips when DISK_IMAGE unset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
return "ok: DISK_IMAGE is set"
```

</details>

#### disk image exists and is > 10 MB

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
fs.exists(img).to_equal(true)
val info = fs.stat(img)
val ten_mb = 10485760
info.size.to_be_greater_than(ten_mb)
```

</details>

#### image has FAT32 magic at offset 0x36

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
val (out, err, code) = process.run("dd", [
    "if={img}",
    "bs=1",
    "skip=54",
    "count=8",
    "status=none",
])
code.to_equal(0)
out.contains("FAT32").to_equal(true)
```

</details>

#### image carries the expected runtime rootfs backend marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
val expected = expected_rootfs_backend()
val (out, err, code) = process.run("grep", [
    "-a",
    "rootfs_backend={expected}",
    img,
])
code.to_equal(0)
out.contains("rootfs_backend={expected}").to_equal(true)
```

</details>

#### QEMU boot with -drive smoke produces [BOOT] marker within 30s

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
val qemu = qemu_binary()
val qemu_exists = fs.exists(qemu)
if qemu_exists == false:
    val (which_out, which_err, which_code) = process.run("which", [qemu])
    if which_code != 0:
        return "skip: qemu binary not found"
val (out, err, code) = process.run(qemu, [
    "-display",
    "none",
    "-serial",
    "stdio",
    "-drive",
    "format=raw,file={img}",
    "-m",
    "128M",
    "-no-reboot",
])
out.contains("[BOOT]").to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/disk_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS QEMU FAT32 disk-boot smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
