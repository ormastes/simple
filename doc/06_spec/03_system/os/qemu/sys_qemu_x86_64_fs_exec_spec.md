# sys_qemu_x86_64_fs_exec_spec

> QEMU System Test — x86_64 FS-Exec Boot.

<!-- sdn-diagram:id=sys_qemu_x86_64_fs_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_qemu_x86_64_fs_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_qemu_x86_64_fs_exec_spec -> std
sys_qemu_x86_64_fs_exec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_qemu_x86_64_fs_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sys_qemu_x86_64_fs_exec_spec

QEMU System Test — x86_64 FS-Exec Boot.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QEMU-SYSTEST-MULTIARCH-AC2 |
| Category | OS system test |
| Status | Active |
| Source | `test/03_system/os/qemu/sys_qemu_x86_64_fs_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU System Test — x86_64 FS-Exec Boot.

Boots a real QEMU x86_64-q35 instance and validates serial output markers.
Kernel: build/os/simpleos_x86_64_fs_exec.elf
Image:  build/os/fat32-x86_64.img

A missing kernel is a diagnosed RED failure. Never uses skip().

## Scenarios

### qemu system test — x86_64 fs-exec boot

#### x86_64 kernel and image presence is diagnosed

- print "[sys qemu x86 64] MISSING KERNEL
- print "[sys qemu x86 64] MISSING IMAGE: " + x86 64 image path
   - Expected: image_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel_present = rt_file_exists(x86_64_kernel_path())
val image_present = rt_file_exists(x86_64_image_path())
if not kernel_present:
    print "[sys_qemu_x86_64] MISSING KERNEL (expected RED): " + x86_64_kernel_path()
if not image_present:
    print "[sys_qemu_x86_64] MISSING IMAGE: " + x86_64_image_path()
expect(image_present).to_equal(true)
```

</details>

#### x86_64 boots and all fs-exec acceptance markers appear in serial

- x86 64 kernel path
- x86 64 image path
- x86 64 qemu bin
- x86 64 qemu args
- x86 64 markers
- x86 64 timeout ms
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val classification = run_qemu_systest(
    "x86_64",
    x86_64_kernel_path(),
    x86_64_image_path(),
    x86_64_qemu_bin(),
    x86_64_qemu_args(),
    x86_64_markers(),
    x86_64_timeout_ms()
)
if classification != SYSTEST_PASS:
    print "[sys_qemu_x86_64] CLASSIFIED: " + classification
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
