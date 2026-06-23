# sys_qemu_riscv32_fs_exec_spec

> QEMU System Test — riscv32 FS-Exec Boot.

<!-- sdn-diagram:id=sys_qemu_riscv32_fs_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sys_qemu_riscv32_fs_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sys_qemu_riscv32_fs_exec_spec -> std
sys_qemu_riscv32_fs_exec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sys_qemu_riscv32_fs_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sys_qemu_riscv32_fs_exec_spec

QEMU System Test — riscv32 FS-Exec Boot.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #QEMU-SYSTEST-MULTIARCH-AC2 |
| Category | OS system test |
| Status | Active |
| Source | `test/03_system/os/qemu/sys_qemu_riscv32_fs_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

QEMU System Test — riscv32 FS-Exec Boot.

Boots a real QEMU riscv32-virt instance and validates serial output markers.
Kernel: build/os/simpleos_riscv32_smf_fs.elf
Image:  build/os/fat32-riscv32.img

A missing kernel is a diagnosed RED failure. The classifier returns
'missing-media:<path>' which this spec surfaces as a hard failure — never
uses skip().

## Scenarios

### qemu system test — riscv32 fs-exec boot

#### riscv32 kernel and image presence is diagnosed

- print "[sys qemu riscv32] MISSING KERNEL
- print "[sys qemu riscv32] MISSING IMAGE: " + riscv32 image path
   - Expected: image_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel_present = rt_file_exists(riscv32_kernel_path())
val image_present = rt_file_exists(riscv32_image_path())
if not kernel_present:
    print "[sys_qemu_riscv32] MISSING KERNEL (expected RED): " + riscv32_kernel_path()
if not image_present:
    print "[sys_qemu_riscv32] MISSING IMAGE: " + riscv32_image_path()
# Report presence status — actual pass/fail is in the run test below
expect(image_present).to_equal(true)
```

</details>

#### riscv32 boots and all fs-exec acceptance markers appear in serial

- riscv32 kernel path
- riscv32 image path
- riscv32 qemu bin
- riscv32 qemu args
- riscv32 markers
- riscv32 timeout ms
   - Expected: classification equals `SYSTEST_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val classification = run_qemu_systest(
    "riscv32",
    riscv32_kernel_path(),
    riscv32_image_path(),
    riscv32_qemu_bin(),
    riscv32_qemu_args(),
    riscv32_markers(),
    riscv32_timeout_ms()
)
if classification != SYSTEST_PASS:
    print "[sys_qemu_riscv32] CLASSIFIED: " + classification
# A missing-media result is a RED diagnosed failure — not a pass.
# The spec must fail when kernel is absent.
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
