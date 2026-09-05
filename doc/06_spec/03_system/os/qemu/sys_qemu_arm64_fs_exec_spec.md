# sys_qemu_arm64_fs_exec_spec

> QEMU System Test — arm64 FS-Exec Boot.

<!-- sdn-diagram:id=sys_qemu_arm64_fs_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_qemu_arm64_fs_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_qemu_arm64_fs_exec_spec -> std
sys_qemu_arm64_fs_exec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_qemu_arm64_fs_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sys_qemu_arm64_fs_exec_spec

QEMU System Test — arm64 FS-Exec Boot.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QEMU-SYSTEST-MULTIARCH-AC2 |
| Category | OS system test |
| Status | Active |
| Source | `test/03_system/os/qemu/sys_qemu_arm64_fs_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU System Test — arm64 FS-Exec Boot.

Boots a real QEMU aarch64-virt instance via loader-device (force-raw=on)
and validates serial output markers.
Kernel: build/os/simpleos_arm64_fs_exec.elf
Image:  build/os/fat32-arm64.img

A missing kernel is a diagnosed RED failure. Never uses skip().

## Scenarios

### qemu system test — arm64 fs-exec boot

#### arm64 kernel and image presence is diagnosed

- print "[sys qemu arm64] MISSING KERNEL
- print "[sys qemu arm64] MISSING IMAGE: " + arm64 image path
   - Expected: image_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel_present = rt_file_exists(arm64_kernel_path())
val image_present = rt_file_exists(arm64_image_path())
if not kernel_present:
    print "[sys_qemu_arm64] MISSING KERNEL (expected RED): " + arm64_kernel_path()
if not image_present:
    print "[sys_qemu_arm64] MISSING IMAGE: " + arm64_image_path()
expect(image_present).to_equal(true)
```

</details>

#### arm64 boots and all fs-exec acceptance markers appear in serial

- arm64 kernel path
- arm64 image path
- arm64 qemu bin
- arm64 qemu args
- arm64 markers
- arm64 timeout ms
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val classification = run_qemu_systest(
    "arm64",
    arm64_kernel_path(),
    arm64_image_path(),
    arm64_qemu_bin(),
    arm64_qemu_args(),
    arm64_markers(),
    arm64_timeout_ms()
)
if classification != SYSTEST_PASS:
    print "[sys_qemu_arm64] CLASSIFIED: " + classification
expect(classification).to_equal(SYSTEST_PASS)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
