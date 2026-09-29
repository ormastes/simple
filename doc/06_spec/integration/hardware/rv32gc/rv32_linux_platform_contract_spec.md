# Rv32 Linux Platform Contract Specification

> Tests covering RV32 Linux platform contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv32 Linux Platform Contract Specification

## Scenarios

### RV32 Linux platform contract

#### uses the QEMU virt memory map and Linux entry registers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the QEMU virt memory map and Linux entry registers
   - Expected: platform.dram_base equals `0x80000000`
   - Expected: platform.uart_base equals `0x10000000`
   - Expected: platform.clint_base equals `0x02000000`
   - Expected: platform.plic_base equals `0x0C000000`
   - Expected: platform.hartid_register equals `a0`
   - Expected: platform.dtb_register equals `a1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the QEMU virt memory map and Linux entry registers")
val platform = RiscvPlatformProfile.qemu_virt_rv32()
expect(platform.dram_base).to_equal(0x80000000)
expect(platform.uart_base).to_equal(0x10000000)
expect(platform.clint_base).to_equal(0x02000000)
expect(platform.plic_base).to_equal(0x0C000000)
expect(platform.hartid_register).to_equal("a0")
expect(platform.dtb_register).to_equal("a1")
```

</details>

#### uses ILP32D Sv32 for the first Linux milestone

- uses ILP32D Sv32 for the first Linux milestone
   - Expected: linux.abi.to_text() equals `ilp32d`
   - Expected: linux.mmu_mode.to_text() equals `sv32`
   - Expected: linux.kernel_alignment equals `0x200000`
   - Expected: linux.opensbi_required is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses ILP32D Sv32 for the first Linux milestone")
val linux = RiscvLinuxProfile.rv32_qemu_virt_linux()
expect(linux.abi.to_text()).to_equal("ilp32d")
expect(linux.mmu_mode.to_text()).to_equal("sv32")
expect(linux.kernel_alignment).to_equal(0x200000)
expect(linux.opensbi_required).to_equal(true)
```

</details>

#### programs the Linux handoff registers with satp disabled

- programs the Linux handoff registers with satp disabled
   - Expected: soc.regs.read(10) equals `0`
   - Expected: soc.regs.read(11) equals `0x88000000`
   - Expected: soc.csr.read_satp() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("programs the Linux handoff registers with satp disabled")
val platform = RiscvPlatformProfile.qemu_virt_rv32()
var soc = rv32_soc_create(1, 0x1000, platform.reset_vector)
soc.set_linux_handoff(0, 0x88000000)
expect(soc.regs.read(10)).to_equal(0)
expect(soc.regs.read(11)).to_equal(0x88000000)
expect(soc.csr.read_satp()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32 Linux platform contract.
- RV32 Linux platform contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe2422671497307f33c2764ab813b7ee5de46dc0b5443adc799ea3934fbb6668`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe2422671497307f33c2764ab813b7ee5de46dc0b5443adc799ea3934fbb6668`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe2422671497307f33c2764ab813b7ee5de46dc0b5443adc799ea3934fbb6668`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl
mirror: doc/06_spec/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the QEMU virt memory map and Linux entry registers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses ILP32D Sv32 for the first Linux milestone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/hardware/rv32gc/rv32_linux_platform_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'programs the Linux handoff registers with satp disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
