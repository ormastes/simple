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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Riscv Smf Fs Launch Specification

## Scenarios

### SimpleOS RISC-V SMF filesystem launch

### REQ-RISCV-SMF-005: QEMU scenarios

#### registers the RV64 filesystem SMF scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_riscv64_virtio_fat32_smf()
expect(scenario.name).to_equal("riscv64-virtio-fat32-smf")
expect(scenario.arch).to_equal(Architecture.Riscv64)
expect(scenario.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(scenario_test_timeout_ms(scenario)).to_equal(60000)
```

</details>

#### boots RV64 through the explicit OpenSBI provider without an interactive monitor

- boots RV64 through the explicit OpenSBI provider without an interactive monitor

#### registers the RV32 filesystem SMF scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots RV64 through the explicit OpenSBI provider without an interactive monitor")
val scenario = scenario_riscv64_virtio_fat32_smf()
val command = build_scenario_command(scenario, "build/os/simpleos_riscv64_smf_fs.elf")
expect(command).to_contain("qemu-system-riscv64")
expect(command).to_contain("-bios")
expect(command).to_contain("default")
expect(command).to_contain("-no-user-config")
expect(command).to_contain("-monitor")
expect(command).to_contain("none")
```

</details>

#### registers the RV32 filesystem SMF scenario

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_riscv32_virtio_fat32_smf()
expect(scenario.name).to_equal("riscv32-virtio-fat32-smf")
expect(scenario.arch).to_equal(Architecture.Riscv32)
expect(scenario.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(scenario_test_timeout_ms(scenario)).to_equal(60000)
```

</details>

#### resolves scenarios by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(get_scenario("riscv64-virtio-fat32-smf").unwrap().name).to_equal("riscv64-virtio-fat32-smf")
expect(get_scenario("riscv32-virtio-fat32-smf").unwrap().name).to_equal("riscv32-virtio-fat32-smf")
```

</details>

#### binds scenarios to RISC-V smoke entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(scenario_target(scenario_riscv64_virtio_fat32_smf()).entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl")
expect(scenario_target(scenario_riscv32_virtio_fat32_smf()).entry).to_equal("examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl")
```

</details>

#### requires the hosted RV64 entry to execute and collect filesystem processes

- requires the hosted RV64 entry to execute and collect filesystem processes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires the hosted RV64 entry to execute and collect filesystem processes")
val source = file_read("examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl")
expect(source).to_contain("riscv64_fs_exec_spawn_capture(app_path, [app_path], [])")
expect(source).to_contain("if result.exit_code != 0:")
expect(source).to_contain("stdout_bytes={result.bytes.len()}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS RISC-V SMF filesystem launch
- REQ-RISCV-SMF-005: QEMU scenarios

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
