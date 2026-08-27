# Alt Rootfs Disk Boot Specification

> <details>

<!-- sdn-diagram:id=alt_rootfs_disk_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=alt_rootfs_disk_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

alt_rootfs_disk_boot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=alt_rootfs_disk_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Alt Rootfs Disk Boot Specification

## Scenarios

### SimpleOS FAT32-carried alternate-rootfs boot smoke

#### skips when SIMPLEOS_ALT_ROOTFS_BOOT is not enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not boot_gate():
    return "skip: SIMPLEOS_ALT_ROOTFS_BOOT not set"
return "ok: gate enabled"
```

</details>

### SimpleOS NVFS-marked FAT32 carrier image

#### builds an NVFS-marked image carrying the rootfs marker

1. reset backend root
   - Expected: stage_rootfs_seed() is true
   - Expected: build[2] equals `0`
   - Expected: rt_file_exists(img) is true
   - Expected: marker[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not boot_gate():
    return "skip: SIMPLEOS_ALT_ROOTFS_BOOT not set"
reset_backend_root()
expect(stage_rootfs_seed()).to_equal(true)
val build = build_image()
expect(build[2]).to_equal(0)
val img = image_path()
expect(rt_file_exists(img)).to_equal(true)
val marker = rt_process_run("grep", ["-a", "rootfs_backend=nvfs", img])
expect(marker[2]).to_equal(0)
```

</details>

#### boots the NVFS-marked image under QEMU and prints [BOOT]

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not boot_gate():
    return "skip: SIMPLEOS_ALT_ROOTFS_BOOT not set"
if not qemu_available():
    return "skip: qemu-system-x86_64 not found"
val img = image_path()
if not rt_file_exists(img):
    return "skip: nvfs image not built"
val boot = boot_image()
val serial = boot[0] + boot[1]
expect(serial.contains("[BOOT]")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/alt_rootfs_disk_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS FAT32-carried alternate-rootfs boot smoke
- SimpleOS NVFS-marked FAT32 carrier image

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
