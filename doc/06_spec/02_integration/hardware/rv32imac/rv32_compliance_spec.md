# RV32IMAC Compliance Test Harness

> Harness for running riscv-arch-test compliance suite. Compiles test programs, loads into simulation ROM, and compares signatures.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32IMAC Compliance Test Harness

Harness for running riscv-arch-test compliance suite. Compiles test programs, loads into simulation ROM, and compares signatures.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-COMPLIANCE-001 |
| Category | Hardware |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/02_integration/hardware/rv32imac/rv32_compliance_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# RV32IMAC Compliance Test Harness

**Feature IDs:** #RV32-COMPLIANCE-001
**Category:** Hardware
**Difficulty:** 4/5
**Status:** In Progress

## Overview

Harness for running riscv-arch-test compliance suite.
Compiles test programs, loads into simulation ROM, and compares signatures.

## Scenarios

### RV32I Compliance

#### ADD: rd = rs1 + rs2

- Verify: ADD: rd = rs1 + rs2
   - Expected: alu_execute(AluOp.Add, 100, 200) equals `300)  # oracle: pinned constant asserted by this scenario`
   - Expected: alu_execute(AluOp.Add, 0xFFFFFFFF, 1) equals `0)  # Overflow wraps  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: ADD: rd = rs1 + rs2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.Add, 100, 200)).to_equal(300)  # oracle: pinned constant asserted by this scenario
expect(alu_execute(AluOp.Add, 0xFFFFFFFF, 1)).to_equal(0)  # Overflow wraps  # oracle: pinned constant asserted by this scenario
```

</details>

#### SUB: rd = rs1 - rs2

- Verify: SUB: rd = rs1 - rs2
   - Expected: alu_execute(AluOp.Sub, 200, 100) equals `100)  # oracle: pinned constant asserted by this scenario`
   - Expected: alu_execute(AluOp.Sub, 0, 1) equals `0xFFFFFFFF)  # Underflow wraps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: SUB: rd = rs1 - rs2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.Sub, 200, 100)).to_equal(100)  # oracle: pinned constant asserted by this scenario
expect(alu_execute(AluOp.Sub, 0, 1)).to_equal(0xFFFFFFFF)  # Underflow wraps
```

</details>

#### AND/OR/XOR: bitwise operations

- Verify: AND/OR/XOR: bitwise operations
   - Expected: alu_execute(AluOp.And, 0xF0F0, 0xFF00) equals `0xF000`
   - Expected: alu_execute(AluOp.Or, 0xF0F0, 0x0F0F) equals `0xFFFF`
   - Expected: alu_execute(AluOp.Xor, 0xFFFF, 0xF0F0) equals `0x0F0F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: AND/OR/XOR: bitwise operations")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.And, 0xF0F0, 0xFF00)).to_equal(0xF000)
expect(alu_execute(AluOp.Or, 0xF0F0, 0x0F0F)).to_equal(0xFFFF)
expect(alu_execute(AluOp.Xor, 0xFFFF, 0xF0F0)).to_equal(0x0F0F)
```

</details>

#### SLL/SRL/SRA: shift operations

- Verify: SLL/SRL/SRA: shift operations
   - Expected: alu_execute(AluOp.Sll, 1, 10) equals `1024)  # oracle: pinned constant asserted by this scenario`
   - Expected: alu_execute(AluOp.Srl, 1024, 10) equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: SLL/SRL/SRA: shift operations")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.Sll, 1, 10)).to_equal(1024)  # oracle: pinned constant asserted by this scenario
expect(alu_execute(AluOp.Srl, 1024, 10)).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### SLT/SLTU: comparison operations

- Verify: SLT/SLTU: comparison operations
   - Expected: alu_execute(AluOp.Slt, 0xFFFFFFFF, 0) equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: alu_execute(AluOp.Sltu, 0xFFFFFFFF, 0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: SLT/SLTU: comparison operations")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Signed: -1 < 0
expect(alu_execute(AluOp.Slt, 0xFFFFFFFF, 0)).to_equal(1)  # oracle: pinned constant asserted by this scenario
# Unsigned: 0xFFFFFFFF > 0
expect(alu_execute(AluOp.Sltu, 0xFFFFFFFF, 0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### RV32M Compliance

#### MUL: rd = (rs1 * rs2)[31:0]

- Verify: MUL: rd = (rs1 * rs2)[31:0]
   - Expected: muldiv_execute(MulDivOp.Mul, 7, 6) equals `42)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: MUL: rd = (rs1 * rs2)[31:0]")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(muldiv_execute(MulDivOp.Mul, 7, 6)).to_equal(42)  # oracle: pinned constant asserted by this scenario
```

</details>

#### MUL: handles overflow

- Verify: MUL: handles overflow
   - Expected: muldiv_execute(MulDivOp.Mul, 0x80000000, 2) and 0xFFFFFFFF equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: MUL: handles overflow")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(muldiv_execute(MulDivOp.Mul, 0x80000000, 2) and 0xFFFFFFFF).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### DIV: rd = rs1 / rs2 (signed)

- Verify: DIV: rd = rs1 / rs2 (signed)
   - Expected: muldiv_execute(MulDivOp.Div, 20, 3) equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: DIV: rd = rs1 / rs2 (signed)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(muldiv_execute(MulDivOp.Div, 20, 3)).to_equal(6)  # oracle: pinned constant asserted by this scenario
```

</details>

#### DIV: division by zero returns all ones

- Verify: DIV: division by zero returns all ones
   - Expected: muldiv_execute(MulDivOp.Div, 42, zero) and 0xFFFFFFFF equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: DIV: division by zero returns all ones")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Use var to prevent const-evaluator from folding 42/0
var zero = 0
expect(muldiv_execute(MulDivOp.Div, 42, zero) and 0xFFFFFFFF).to_equal(0xFFFFFFFF)
```

</details>

#### DIVU: unsigned division

- Verify: DIVU: unsigned division
   - Expected: muldiv_execute(MulDivOp.Divu, 20, 3) equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: DIVU: unsigned division")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(muldiv_execute(MulDivOp.Divu, 20, 3)).to_equal(6)  # oracle: pinned constant asserted by this scenario
```

</details>

#### REM: remainder

- Verify: REM: remainder
   - Expected: muldiv_execute(MulDivOp.Rem, 20, 3) equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: REM: remainder")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(muldiv_execute(MulDivOp.Rem, 20, 3)).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### REMU: unsigned remainder

- Verify: REMU: unsigned remainder
   - Expected: muldiv_execute(MulDivOp.Remu, 20, 3) equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: REMU: unsigned remainder")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(muldiv_execute(MulDivOp.Remu, 20, 3)).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

### RV32A Compliance

#### LR/SC succeeds on uncontested reservation

- Verify: LR/SC succeeds on uncontested reservation
   - Expected: success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: LR/SC succeeds on uncontested reservation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Fresh reservation set
**When:** LR then SC to same address
**Then:** SC succeeds (returns true)
"""
var rs = ReservationSet64.create()
rs.reserve(0x80000100)
val success = rs.check_and_clear(0x80000100)
expect(success).to_equal(true)
```

</details>

#### SC fails after intervening store

- Verify: SC fails after intervening store
   - Expected: success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: SC fails after intervening store")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Active reservation
**When:** Intervening store to same address, then SC
**Then:** SC fails (returns false)
"""
var rs = ReservationSet64.create()
rs.reserve(0x80000100)
rs.invalidate()
val success = rs.check_and_clear(0x80000100)
expect(success).to_equal(false)
```

</details>

#### AMOADD computes correctly

- Verify: AMOADD computes correctly
   - Expected: amo_execute(AmoOp.Add, 100, 50).new_value equals `150)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: AMOADD computes correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(amo_execute(AmoOp.Add, 100, 50).new_value).to_equal(150)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AMOSWAP returns rs2

- Verify: AMOSWAP returns rs2
   - Expected: amo_execute(AmoOp.Swap, 100, 200).new_value equals `200)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: AMOSWAP returns rs2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(amo_execute(AmoOp.Swap, 100, 200).new_value).to_equal(200)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AMOAND computes correctly

- Verify: AMOAND computes correctly
   - Expected: amo_execute(AmoOp.And, 0xFF00, 0x0FF0).new_value equals `0x0F00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: AMOAND computes correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(amo_execute(AmoOp.And, 0xFF00, 0x0FF0).new_value).to_equal(0x0F00)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5acc96b3bee8eabd98280b527cbe7a1b34cf90dbb8fa778539751aca17f4f5c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5acc96b3bee8eabd98280b527cbe7a1b34cf90dbb8fa778539751aca17f4f5c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5acc96b3bee8eabd98280b527cbe7a1b34cf90dbb8fa778539751aca17f4f5c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/hardware/rv32imac/rv32_compliance_spec.spl
mirror: doc/06_spec/02_integration/hardware/rv32imac/rv32_compliance_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/hardware/rv32imac/rv32_compliance_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/hardware/rv32imac/rv32_compliance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/hardware/rv32imac/rv32_compliance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
