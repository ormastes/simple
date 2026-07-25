# sys_qemu_riscv64_fs_exec_spec

> QEMU System Test — riscv64 FS-Exec Boot.

<!-- sdn-diagram:id=sys_qemu_riscv64_fs_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_qemu_riscv64_fs_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_qemu_riscv64_fs_exec_spec -> std
sys_qemu_riscv64_fs_exec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_qemu_riscv64_fs_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sys_qemu_riscv64_fs_exec_spec

QEMU System Test — riscv64 FS-Exec Boot.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QEMU-SYSTEST-MULTIARCH-AC2 |
| Category | OS system test |
| Status | Active |
| Source | `test/03_system/os/qemu/sys_qemu_riscv64_fs_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU System Test — riscv64 FS-Exec Boot.

Boots a real QEMU riscv64-virt instance and validates serial output markers.
Kernel: build/os/simpleos_riscv64_smf_fs.elf (must be present — RED if absent).
Image:  build/os/fat32-riscv64.img

A missing kernel is a diagnosed RED failure. Never use skip().

## Scenarios

### qemu system test — riscv64 fs-exec boot

#### riscv64 kernel and image are present (media check)

- print "[sys qemu riscv64] MISSING KERNEL: " + riscv64 kernel path
   - Expected: kernel_present is true
- print "[sys qemu riscv64] MISSING IMAGE: " + riscv64 image path
   - Expected: image_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel_present = rt_file_exists(riscv64_kernel_path())
if not kernel_present:
    print "[sys_qemu_riscv64] MISSING KERNEL: " + riscv64_kernel_path()
expect(kernel_present).to_equal(true)
val image_present = rt_file_exists(riscv64_image_path())
if not image_present:
    print "[sys_qemu_riscv64] MISSING IMAGE: " + riscv64_image_path()
expect(image_present).to_equal(true)
```

</details>

#### riscv64 boots and all fs-exec acceptance markers appear in serial

- riscv64 kernel path
- riscv64 image path
- riscv64 qemu bin
- riscv64 qemu args
- riscv64 markers
- riscv64 timeout ms
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val classification = run_qemu_systest(
    "riscv64",
    riscv64_kernel_path(),
    riscv64_image_path(),
    riscv64_qemu_bin(),
    riscv64_qemu_args(),
    riscv64_markers(),
    riscv64_timeout_ms()
)
if classification != SYSTEST_PASS:
    print "[sys_qemu_riscv64] FAILED: " + classification
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
