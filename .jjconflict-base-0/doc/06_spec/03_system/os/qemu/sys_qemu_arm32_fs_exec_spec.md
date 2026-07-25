# sys_qemu_arm32_fs_exec_spec

> QEMU System Test — arm32 FS-Exec Boot.

<!-- sdn-diagram:id=sys_qemu_arm32_fs_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_qemu_arm32_fs_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_qemu_arm32_fs_exec_spec -> std
sys_qemu_arm32_fs_exec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_qemu_arm32_fs_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sys_qemu_arm32_fs_exec_spec

QEMU System Test — arm32 FS-Exec Boot.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QEMU-SYSTEST-MULTIARCH-AC2 |
| Category | OS system test |
| Status | Active |
| Source | `test/03_system/os/qemu/sys_qemu_arm32_fs_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU System Test — arm32 FS-Exec Boot.

Boots a real QEMU arm-virt instance via loader-device (no force-raw)
and validates serial output markers.
Kernel: build/os/simpleos_arm32_fs_exec.elf
Image:  build/os/fat32-arm32.img

A missing kernel is a diagnosed RED failure. Never uses skip().

## Scenarios

### qemu system test — arm32 fs-exec boot

#### arm32 kernel and image presence is diagnosed

- print "[sys qemu arm32] MISSING KERNEL
- print "[sys qemu arm32] MISSING IMAGE: " + arm32 image path
   - Expected: image_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel_present = rt_file_exists(arm32_kernel_path())
val image_present = rt_file_exists(arm32_image_path())
if not kernel_present:
    print "[sys_qemu_arm32] MISSING KERNEL (expected RED): " + arm32_kernel_path()
if not image_present:
    print "[sys_qemu_arm32] MISSING IMAGE: " + arm32_image_path()
expect(image_present).to_equal(true)
```

</details>

#### arm32 boots and all fs-exec acceptance markers appear in serial

- arm32 kernel path
- arm32 image path
- arm32 qemu bin
- arm32 qemu args
- arm32 markers
- arm32 timeout ms
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val classification = run_qemu_systest(
    "arm32",
    arm32_kernel_path(),
    arm32_image_path(),
    arm32_qemu_bin(),
    arm32_qemu_args(),
    arm32_markers(),
    arm32_timeout_ms()
)
if classification != SYSTEST_PASS:
    print "[sys_qemu_arm32] CLASSIFIED: " + classification
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
