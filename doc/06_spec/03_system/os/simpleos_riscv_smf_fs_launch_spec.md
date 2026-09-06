# Simpleos Riscv Smf Fs Launch Specification

> <details>

<!-- sdn-diagram:id=simpleos_riscv_smf_fs_launch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_riscv_smf_fs_launch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_riscv_smf_fs_launch_spec -> std
simpleos_riscv_smf_fs_launch_spec -> os
simpleos_riscv_smf_fs_launch_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_riscv_smf_fs_launch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Riscv Smf Fs Launch Specification

## Scenarios

### SimpleOS RISC-V SMF filesystem live launch

#### builds the RV64 SMF filesystem scenario target when prerequisites are available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_riscv64_virtio_fat32_smf()
val target = scenario_target(scenario)
if not _live_riscv_smf_enabled():
    print "[simpleos_riscv_smf_fs_launch_spec] live RV64 build disabled; set SIMPLEOS_QEMU_RISCV_SMF_LIVE=1"
    expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl")
else:
    expect(build_scenario(scenario)).to_equal(true)
    expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots the RV64 SMF filesystem scenario when live QEMU is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_riscv64_virtio_fat32_smf()
val target = scenario_target(scenario)
if not _live_riscv_smf_enabled():
    print "[simpleos_riscv_smf_fs_launch_spec] live RV64 QEMU disabled; set SIMPLEOS_QEMU_RISCV_SMF_LIVE=1"
    expect(target.qemu_system).to_equal("qemu-system-riscv64")
elif not can_run_target(target):
    print "[simpleos_riscv_smf_fs_launch_spec] qemu-system-riscv64 unavailable, skipping live boot"
    expect(target.qemu_system).to_equal("qemu-system-riscv64")
else:
    expect(build_scenario(scenario)).to_equal(true)
    expect(test_scenario(scenario, scenario_test_timeout_ms(scenario))).to_equal(true)
```

</details>

#### keeps RV32 wired to the SMF filesystem scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_riscv32_virtio_fat32_smf()
val target = scenario_target(scenario)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl")
expect(target.output).to_equal("build/os/simpleos_riscv32_smf_fs.elf")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_riscv_smf_fs_launch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS RISC-V SMF filesystem live launch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
