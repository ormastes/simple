# Riscv32 Boot Specification

> Tests covering rv32 boot bootstrap trap runtime.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Boot Specification

## Scenarios

### rv32 boot bootstrap trap runtime

#### records boot arguments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records boot arguments
   - Expected: boot.hart_id() equals `7`
   - Expected: boot.dtb_addr() equals `0x88001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records boot arguments")
val boot = Rv32Boot(direct_boot: true)
boot.save_boot_params(7, 0x88001000)
expect(boot.hart_id()).to_equal(7)
expect(boot.dtb_addr()).to_equal(0x88001000)
```

</details>

#### keeps the fixed kernel load address

- keeps the fixed kernel load address
   - Expected: boot.kernel_load_addr() equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the fixed kernel load address")
val boot = Rv32Boot(direct_boot: true)
expect(boot.kernel_load_addr()).to_equal(0x80000000)
```

</details>

#### builds an RV32 boot output with direct-boot defaults

- builds an RV32 boot output with direct-boot defaults
   - Expected: boot_output.arch equals `Architecture.Riscv32`
   - Expected: boot_output.serial_base equals `0x10000000`
   - Expected: boot_output.kernel_phys_base.addr equals `0x80000000`
   - Expected: boot_output.memory_map.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds an RV32 boot output with direct-boot defaults")
val boot = Rv32Boot(direct_boot: true)
boot.save_boot_params(0, 0)
val boot_output = boot.build_boot_output()
expect(boot_output.arch).to_equal(Architecture.Riscv32)
expect(boot_output.serial_base).to_equal(0x10000000)
expect(boot_output.kernel_phys_base.addr).to_equal(0x80000000)
expect(boot_output.memory_map.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/riscv32_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rv32 boot bootstrap trap runtime.
- rv32 boot bootstrap trap runtime

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92e215fde44efbf31dbfe28b58816850e5153934f84f49162f7b161e0646bc75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92e215fde44efbf31dbfe28b58816850e5153934f84f49162f7b161e0646bc75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92e215fde44efbf31dbfe28b58816850e5153934f84f49162f7b161e0646bc75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/arch/riscv32_boot_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/riscv32_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/riscv32_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/riscv32_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/riscv32_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/arch/riscv32_boot_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records boot arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv32_boot_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the fixed kernel load address' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv32_boot_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds an RV32 boot output with direct-boot defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
