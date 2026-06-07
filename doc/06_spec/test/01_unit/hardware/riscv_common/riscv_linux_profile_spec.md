# Riscv Linux Profile Specification

> <details>

<!-- sdn-diagram:id=riscv_linux_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_linux_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_linux_profile_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_linux_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Linux Profile Specification

## Scenarios

### RISC-V Linux shared profiles

#### defines RV64 QEMU virt as LP64D Sv39 with OpenSBI handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linux = RiscvLinuxProfile.rv64_qemu_virt_linux()
val platform = RiscvPlatformProfile.qemu_virt_rv64()
expect(linux.abi).to_equal(RiscvTargetAbi.LP64D)
expect(linux.mmu_mode.to_text()).to_equal("sv39")
expect(linux.opensbi_required).to_equal(true)
expect(platform.name).to_equal("qemu_virt_rv64")
expect(platform.hartid_register).to_equal("a0")
expect(platform.dtb_register).to_equal("a1")
expect(platform.required_soc_blocks()).to_contain("opensbi-handoff")
```

</details>

#### defines RV32 QEMU virt as ILP32D Sv32 with OpenSBI handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linux = RiscvLinuxProfile.rv32_qemu_virt_linux()
val platform = RiscvPlatformProfile.qemu_virt_rv32()
expect(linux.abi).to_equal(RiscvTargetAbi.ILP32D)
expect(linux.mmu_mode.to_text()).to_equal("sv32")
expect(linux.opensbi_required).to_equal(true)
expect(platform.linux.abi).to_equal(RiscvTargetAbi.ILP32D)
expect(platform.name).to_equal("qemu_virt_rv32")
expect(platform.required_soc_blocks()).to_contain("rv32gc-core")
```

</details>

### RV64 Linux boot artifacts

#### rejects missing dtb and firmware for RV64 Linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifacts = Rv64LinuxBootArtifacts.empty()
val errors = artifacts.validate_for(RiscvLinuxProfile.rv64_qemu_virt_linux())
expect(errors).to_contain("kernel_image is required")
expect(errors).to_contain("initrd_rootfs is required")
expect(errors).to_contain("dtb is required")
expect(errors).to_contain("OpenSBI or U-Boot firmware is required")
```

</details>

### RV32 Linux boot artifacts

#### rejects missing dtb and firmware for RV32 Linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifacts = Rv32LinuxBootArtifacts.empty()
val errors = artifacts.validate_for(RiscvLinuxProfile.rv32_qemu_virt_linux())
expect(errors).to_contain("kernel_image is required")
expect(errors).to_contain("initrd_rootfs is required")
expect(errors).to_contain("dtb is required")
expect(errors).to_contain("OpenSBI or U-Boot firmware is required")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/riscv_common/riscv_linux_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V Linux shared profiles
- RV64 Linux boot artifacts
- RV32 Linux boot artifacts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
