# Machine Profile Specification

> <details>

<!-- sdn-diagram:id=machine_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=machine_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

machine_profile_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=machine_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Machine Profile Specification

## Scenarios

### Machine Profiles

#### exports the canonical simulator machine ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profiles = get_riscv_machine_profiles()
expect(profiles.len()).to_equal(2)
expect(profiles[0].name).to_equal("simple-rv64")
expect(profiles[1].name).to_equal("simple-rv32")
```

</details>

#### maps simple-rv64 to the RV64 Linux-capable profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = get_riscv_machine_profile("simple-rv64")
val rv64 = profile.unwrap()
expect(rv64.name).to_equal("simple-rv64")
expect(rv64.arch).to_equal(Architecture.Riscv64)
expect(rv64.boot_protocol).to_equal("opensbi")
expect(rv64.target_triple).to_equal("riscv64-unknown-none")
expect(rv64.qemu_system).to_equal("qemu-system-riscv64")
```

</details>

#### maps riscv32 alias to the canonical RV32 profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = get_riscv_machine_profile("riscv32")
val rv32 = profile.unwrap()
expect(rv32.name).to_equal("simple-rv32")
expect(rv32.arch).to_equal(Architecture.Riscv32)
expect(rv32.target_triple).to_equal("riscv32-unknown-none")
expect(rv32.boot_protocol).to_equal("dtb")
expect(rv32.qemu_bios).to_equal("none")
```

</details>

#### derives RISC-V profile QEMU fields from the platform catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = get_riscv_machine_profile("riscv64").unwrap()
expect(rv64.entry).to_equal("src/os/kernel/arch/riscv64/boot.spl")
expect(rv64.linker_script).to_equal("src/os/kernel/arch/riscv64/linker.ld")
expect(rv64.output).to_equal("build/os/simpleos_riscv64.elf")
expect(rv64.qemu_memory).to_equal("128M")
expect(rv64.qemu_bios).to_equal("default")
expect(rv64.qemu_extra.len()).to_equal(0)
expect(rv64.qemu_machine).to_equal("virt")
expect(rv64.qemu_cpu).to_equal("rv64")

val rv32 = get_riscv_machine_profile("simple-rv32").unwrap()
expect(rv32.entry).to_equal("src/os/kernel/arch/riscv32/boot.spl")
expect(rv32.linker_script).to_equal("src/os/kernel/arch/riscv32/linker.ld")
expect(rv32.output).to_equal("build/os/simpleos_riscv32.elf")
expect(rv32.qemu_memory).to_equal("128M")
expect(rv32.qemu_bios).to_equal("none")
expect(rv32.qemu_extra.len()).to_equal(0)
expect(rv32.qemu_cpu).to_equal("rv32")
```

</details>

#### exports the canonical ARM machine ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profiles = get_arm_machine_profiles()
expect(profiles.len()).to_equal(2)
expect(profiles[0].name).to_equal("simple-arm64")
expect(profiles[1].name).to_equal("simple-arm32")
```

</details>

#### derives ARM profile QEMU fields from the platform catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64 = get_arm_machine_profile("arm64").unwrap()
expect(arm64.arch).to_equal(Architecture.Arm64)
expect(arm64.entry).to_equal("src/os/kernel/arch/arm64/boot.spl")
expect(arm64.linker_script).to_equal("src/os/kernel/arch/arm64/linker.ld")
expect(arm64.target_triple).to_equal("aarch64-unknown-none")
expect(arm64.output).to_equal("build/os/simpleos_aarch64.elf")
expect(arm64.qemu_system).to_equal("qemu-system-aarch64")
expect(arm64.qemu_cpu).to_equal("cortex-a72")
expect(arm64.qemu_memory).to_equal("128M")
expect(arm64.qemu_bios).to_equal("")
expect(arm64.qemu_extra.len()).to_equal(0)
expect(arm64.boot_protocol).to_equal("raw-loader")

val arm32 = get_arm_machine_profile("simple-arm32").unwrap()
expect(arm32.arch).to_equal(Architecture.Arm32)
expect(arm32.entry).to_equal("src/os/kernel/arch/arm32/boot.spl")
expect(arm32.linker_script).to_equal("src/os/kernel/arch/arm32/linker.ld")
expect(arm32.target_triple).to_equal("armv7-unknown-none-eabihf")
expect(arm32.output).to_equal("build/os/simpleos_arm32.elf")
expect(arm32.qemu_system).to_equal("qemu-system-arm")
expect(arm32.qemu_cpu).to_equal("cortex-a15")
expect(arm32.qemu_memory).to_equal("128M")
expect(arm32.qemu_bios).to_equal("")
expect(arm32.qemu_extra.len()).to_equal(0)
expect(arm32.boot_protocol).to_equal("raw-loader")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/machine_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Machine Profiles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
