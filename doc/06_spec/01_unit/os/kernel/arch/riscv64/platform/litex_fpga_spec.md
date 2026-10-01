# LiteX FPGA Platform Specification

> Verifies AC-6: the litex_fpga platform capsule composes LitexFpgaMemoryMap correctly. Tests that the platform init and UART/timer API exist with the right types and that the composed memory map returns expected constants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LiteX FPGA Platform Specification

Verifies AC-6: the litex_fpga platform capsule composes LitexFpgaMemoryMap correctly. Tests that the platform init and UART/timer API exist with the right types and that the composed memory map returns expected constants.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-6 |
| Source | `test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-6: the litex_fpga platform capsule composes LitexFpgaMemoryMap
correctly. Tests that the platform init and UART/timer API exist with the
right types and that the composed memory map returns expected constants.

Covers:
- AC-6 (Minimal host services: console I/O, timer init, idle loop parameterization)

## Scenarios

### LiteX FPGA Platform

#### AC-6: platform name is non-empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-6: platform name is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: platform name is non-empty")
val name = litex_fpga_platform_name()
val len = name.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-6: platform name contains litex or de10nano

- AC-6: platform name contains litex or de10nano


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: platform name contains litex or de10nano")
val name = litex_fpga_platform_name()
expect(name).to_contain("litex")
```

</details>

### LiteX FPGA Memory Map Composition

#### AC-6: LitexFpgaMemoryMap uart_base is 0xf0001000

- AC-6: LitexFpgaMemoryMap uart_base is 0xf0001000
   - Expected: m.uart_base() equals `4026535936`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: LitexFpgaMemoryMap uart_base is 0xf0001000")
val m = make_litex_map()
expect(m.uart_base()).to_equal(4026535936)
```

</details>

#### AC-6: LitexFpgaMemoryMap ram_base is 0x40000000

- AC-6: LitexFpgaMemoryMap ram_base is 0x40000000
   - Expected: m.ram_base() equals `1073741824`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: LitexFpgaMemoryMap ram_base is 0x40000000")
val m = make_litex_map()
expect(m.ram_base()).to_equal(1073741824)
```

</details>

#### AC-6: LitexFpgaMemoryMap clint_base is 0xf0010000

- AC-6: LitexFpgaMemoryMap clint_base is 0xf0010000
   - Expected: m.clint_base() equals `4026597376`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-6: LitexFpgaMemoryMap clint_base is 0xf0010000")
val m = make_litex_map()
expect(m.clint_base()).to_equal(4026597376)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-6](REQ-6)


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-6`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b072ad9d15995c3b2a06a5c4181c93f804327c433fe5cf4622a27319e4cd4ba6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b072ad9d15995c3b2a06a5c4181c93f804327c433fe5cf4622a27319e4cd4ba6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b072ad9d15995c3b2a06a5c4181c93f804327c433fe5cf4622a27319e4cd4ba6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: platform name is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: platform name contains litex or de10nano' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/riscv64/platform/litex_fpga_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: LitexFpgaMemoryMap uart_base is 0xf0001000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
