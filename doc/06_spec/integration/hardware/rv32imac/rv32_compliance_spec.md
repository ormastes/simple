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
| Source | `test/integration/hardware/rv32imac/rv32_compliance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Harness for running riscv-arch-test compliance suite.
Compiles test programs, loads into simulation ROM, and compares signatures.

## Scenarios

### RV32I Compliance

#### ADD: rd = rs1 + rs2

- ADD: rd = rs1 + rs2
   - Expected: alu_execute(AluOp.Add, 100, 200) equals `300`
   - Expected: alu_execute(AluOp.Add, 0xFFFFFFFF, 1) equals `0)  # Overflow wraps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ADD: rd = rs1 + rs2")
expect(alu_execute(AluOp.Add, 100, 200)).to_equal(300)
expect(alu_execute(AluOp.Add, 0xFFFFFFFF, 1)).to_equal(0)  # Overflow wraps
```

</details>

#### SUB: rd = rs1 - rs2

- SUB: rd = rs1 - rs2
   - Expected: alu_execute(AluOp.Sub, 200, 100) equals `100`
   - Expected: alu_execute(AluOp.Sub, 0, 1) equals `0xFFFFFFFF)  # Underflow wraps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SUB: rd = rs1 - rs2")
expect(alu_execute(AluOp.Sub, 200, 100)).to_equal(100)
expect(alu_execute(AluOp.Sub, 0, 1)).to_equal(0xFFFFFFFF)  # Underflow wraps
```

</details>

#### AND/OR/XOR: bitwise operations

- AND/OR/XOR: bitwise operations
   - Expected: alu_execute(AluOp.And, 0xF0F0, 0xFF00) equals `0xF000`
   - Expected: alu_execute(AluOp.Or, 0xF0F0, 0x0F0F) equals `0xFFFF`
   - Expected: alu_execute(AluOp.Xor, 0xFFFF, 0xF0F0) equals `0x0F0F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AND/OR/XOR: bitwise operations")
expect(alu_execute(AluOp.And, 0xF0F0, 0xFF00)).to_equal(0xF000)
expect(alu_execute(AluOp.Or, 0xF0F0, 0x0F0F)).to_equal(0xFFFF)
expect(alu_execute(AluOp.Xor, 0xFFFF, 0xF0F0)).to_equal(0x0F0F)
```

</details>

#### SLL/SRL/SRA: shift operations

- SLL/SRL/SRA: shift operations
   - Expected: alu_execute(AluOp.Sll, 1, 10) equals `1024`
   - Expected: alu_execute(AluOp.Srl, 1024, 10) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SLL/SRL/SRA: shift operations")
expect(alu_execute(AluOp.Sll, 1, 10)).to_equal(1024)
expect(alu_execute(AluOp.Srl, 1024, 10)).to_equal(1)
```

</details>

#### SLT/SLTU: comparison operations

- SLT/SLTU: comparison operations
   - Expected: alu_execute(AluOp.Slt, 0xFFFFFFFF, 0) equals `1`
   - Expected: alu_execute(AluOp.Sltu, 0xFFFFFFFF, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SLT/SLTU: comparison operations")
# Signed: -1 < 0
expect(alu_execute(AluOp.Slt, 0xFFFFFFFF, 0)).to_equal(1)
# Unsigned: 0xFFFFFFFF > 0
expect(alu_execute(AluOp.Sltu, 0xFFFFFFFF, 0)).to_equal(0)
```

</details>

### RV32M Compliance

#### MUL: rd = (rs1 * rs2)[31:0]

- MUL: rd = (rs1 * rs2)[31:0]
   - Expected: muldiv_execute(MulDivOp.Mul, 7, 6) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("MUL: rd = (rs1 * rs2)[31:0]")
expect(muldiv_execute(MulDivOp.Mul, 7, 6)).to_equal(42)
```

</details>

#### MUL: handles overflow

- MUL: handles overflow
   - Expected: muldiv_execute(MulDivOp.Mul, 0x80000000, 2) and 0xFFFFFFFF equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("MUL: handles overflow")
expect(muldiv_execute(MulDivOp.Mul, 0x80000000, 2) and 0xFFFFFFFF).to_equal(0)
```

</details>

#### DIV: rd = rs1 / rs2 (signed)

- DIV: rd = rs1 / rs2 (signed)
   - Expected: muldiv_execute(MulDivOp.Div, 20, 3) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DIV: rd = rs1 / rs2 (signed)")
expect(muldiv_execute(MulDivOp.Div, 20, 3)).to_equal(6)
```

</details>

#### DIV: division by zero returns all ones

- DIV: division by zero returns all ones
   - Expected: muldiv_execute(MulDivOp.Div, 42, zero) and 0xFFFFFFFF equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DIV: division by zero returns all ones")
# Use var to prevent const-evaluator from folding 42/0
var zero = 0
expect(muldiv_execute(MulDivOp.Div, 42, zero) and 0xFFFFFFFF).to_equal(0xFFFFFFFF)
```

</details>

#### DIVU: unsigned division

- DIVU: unsigned division
   - Expected: muldiv_execute(MulDivOp.Divu, 20, 3) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DIVU: unsigned division")
expect(muldiv_execute(MulDivOp.Divu, 20, 3)).to_equal(6)
```

</details>

#### REM: remainder

- REM: remainder
   - Expected: muldiv_execute(MulDivOp.Rem, 20, 3) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("REM: remainder")
expect(muldiv_execute(MulDivOp.Rem, 20, 3)).to_equal(2)
```

</details>

#### REMU: unsigned remainder

- REMU: unsigned remainder
   - Expected: muldiv_execute(MulDivOp.Remu, 20, 3) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("REMU: unsigned remainder")
expect(muldiv_execute(MulDivOp.Remu, 20, 3)).to_equal(2)
```

</details>

### RV32A Compliance

#### LR/SC succeeds on uncontested reservation

- LR/SC succeeds on uncontested reservation
   - Expected: success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("LR/SC succeeds on uncontested reservation")
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

- SC fails after intervening store
   - Expected: success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SC fails after intervening store")
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

- AMOADD computes correctly
   - Expected: amo_execute(AmoOp.Add, 100, 50).new_value equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AMOADD computes correctly")
expect(amo_execute(AmoOp.Add, 100, 50).new_value).to_equal(150)
```

</details>

#### AMOSWAP returns rs2

- AMOSWAP returns rs2
   - Expected: amo_execute(AmoOp.Swap, 100, 200).new_value equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AMOSWAP returns rs2")
expect(amo_execute(AmoOp.Swap, 100, 200).new_value).to_equal(200)
```

</details>

#### AMOAND computes correctly

- AMOAND computes correctly
   - Expected: amo_execute(AmoOp.And, 0xFF00, 0x0FF0).new_value equals `0x0F00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AMOAND computes correctly")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-RV32IMAC`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b9a9f51b24c92060e89f0df955d96206dc9f4b4ac962a278beb651af1d28469`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b9a9f51b24c92060e89f0df955d96206dc9f4b4ac962a278beb651af1d28469`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b9a9f51b24c92060e89f0df955d96206dc9f4b4ac962a278beb651af1d28469`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/hardware/rv32imac/rv32_compliance_spec.spl
mirror: doc/06_spec/integration/hardware/rv32imac/rv32_compliance_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/hardware/rv32imac/rv32_compliance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/hardware/rv32imac/rv32_compliance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/hardware/rv32imac/rv32_compliance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/hardware/rv32imac/rv32_compliance_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/hardware/rv32imac/rv32_compliance_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ADD: rd = rs1 + rs2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/hardware/rv32imac/rv32_compliance_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SUB: rd = rs1 - rs2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/hardware/rv32imac/rv32_compliance_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AND/OR/XOR: bitwise operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
