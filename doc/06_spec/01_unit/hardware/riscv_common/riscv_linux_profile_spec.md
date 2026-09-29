# Riscv Linux Profile Specification

> Tests covering RISC-V Linux shared profiles, RV64 Linux boot artifacts, RV32 Linux boot artifacts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Linux Profile Specification

## Scenarios

### RISC-V Linux shared profiles

#### defines RV64 QEMU virt as LP64D Sv39 with OpenSBI handoff

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines RV64 QEMU virt as LP64D Sv39 with OpenSBI handoff
   - Expected: linux.abi equals `RiscvTargetAbi.LP64D`
   - Expected: linux.mmu_mode.to_text() equals `sv39`
   - Expected: linux.opensbi_required is true
   - Expected: platform.name equals `qemu_virt_rv64`
   - Expected: platform.hartid_register equals `a0`
   - Expected: platform.dtb_register equals `a1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines RV64 QEMU virt as LP64D Sv39 with OpenSBI handoff")
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

- defines RV32 QEMU virt as ILP32D Sv32 with OpenSBI handoff
   - Expected: linux.abi equals `RiscvTargetAbi.ILP32D`
   - Expected: linux.mmu_mode.to_text() equals `sv32`
   - Expected: linux.opensbi_required is true
   - Expected: platform.linux.abi equals `RiscvTargetAbi.ILP32D`
   - Expected: platform.name equals `qemu_virt_rv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines RV32 QEMU virt as ILP32D Sv32 with OpenSBI handoff")
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

- rejects missing dtb and firmware for RV64 Linux


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing dtb and firmware for RV64 Linux")
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

- rejects missing dtb and firmware for RV32 Linux


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing dtb and firmware for RV32 Linux")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V Linux shared profiles, RV64 Linux boot artifacts, RV32 Linux boot artifacts.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c16ebb695a611eba087eb1932926b911c26df0424634ca6f333565db83095623`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c16ebb695a611eba087eb1932926b911c26df0424634ca6f333565db83095623`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c16ebb695a611eba087eb1932926b911c26df0424634ca6f333565db83095623`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/hardware/riscv_common/riscv_linux_profile_spec.spl
mirror: doc/06_spec/01_unit/hardware/riscv_common/riscv_linux_profile_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/riscv_common/riscv_linux_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/riscv_common/riscv_linux_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/riscv_common/riscv_linux_profile_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RV64 QEMU virt as LP64D Sv39 with OpenSBI handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/riscv_common/riscv_linux_profile_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RV32 QEMU virt as ILP32D Sv32 with OpenSBI handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/riscv_common/riscv_linux_profile_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing dtb and firmware for RV64 Linux' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
