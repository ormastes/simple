# sys_qemu_x86_32_fs_exec_spec

> QEMU System Test — x86_32 FS-Exec Boot.

<!-- sdn-diagram:id=sys_qemu_x86_32_fs_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_qemu_x86_32_fs_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_qemu_x86_32_fs_exec_spec -> std
sys_qemu_x86_32_fs_exec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_qemu_x86_32_fs_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sys_qemu_x86_32_fs_exec_spec

QEMU System Test — x86_32 FS-Exec Boot.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QEMU-SYSTEST-MULTIARCH-AC2 |
| Category | OS system test |
| Status | Active |
| Source | `test/03_system/os/qemu/sys_qemu_x86_32_fs_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU System Test — x86_32 FS-Exec Boot.

Boots a real QEMU x86_32-pc instance (via qemu-system-x86_64, which handles
PVH correctly) and validates serial output markers.
Kernel: build/os/simpleos_x86_32_initrd_fs_exec_probe.elf
Image:  build/os/fat32-x86_32.img (passed as initrd)

A missing kernel is a diagnosed RED failure. Never uses skip().

## Scenarios

### qemu system test — x86_32 fs-exec boot

#### x86_32 kernel and image are present (media check)

- print "[sys qemu x86 32] MISSING KERNEL: " + x86 32 kernel path
   - Expected: kernel_present is true
- print "[sys qemu x86 32] MISSING IMAGE: " + x86 32 image path
   - Expected: image_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel_present = rt_file_exists(x86_32_kernel_path())
if not kernel_present:
    print "[sys_qemu_x86_32] MISSING KERNEL: " + x86_32_kernel_path()
expect(kernel_present).to_equal(true)
val image_present = rt_file_exists(x86_32_image_path())
if not image_present:
    print "[sys_qemu_x86_32] MISSING IMAGE: " + x86_32_image_path()
expect(image_present).to_equal(true)
```

</details>

#### x86_32 boots and all fs-exec acceptance markers appear in serial

- x86 32 kernel path
- x86 32 image path
- x86 32 qemu bin
- x86 32 qemu args
- x86 32 markers
- x86 32 timeout ms
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val classification = run_qemu_systest(
    "x86_32",
    x86_32_kernel_path(),
    x86_32_image_path(),
    x86_32_qemu_bin(),
    x86_32_qemu_args(),
    x86_32_markers(),
    x86_32_timeout_ms()
)
if classification != SYSTEST_PASS:
    print "[sys_qemu_x86_32] FAILED: " + classification
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
