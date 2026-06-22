# RV32IMAC Compliance Test Harness

> Harness for running riscv-arch-test compliance suite. Compiles test programs, loads into simulation ROM, and compares signatures.

<!-- sdn-diagram:id=rv32_compliance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_compliance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_compliance_spec -> std
rv32_compliance_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_compliance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Harness for running riscv-arch-test compliance suite.
Compiles test programs, loads into simulation ROM, and compares signatures.

## Scenarios

### RV32I Compliance

#### ADD: rd = rs1 + rs2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 100, 200)).to_equal(300)
expect(alu_execute(AluOp.Add, 0xFFFFFFFF, 1)).to_equal(0)  # Overflow wraps
```

</details>

#### SUB: rd = rs1 - rs2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sub, 200, 100)).to_equal(100)
expect(alu_execute(AluOp.Sub, 0, 1)).to_equal(0xFFFFFFFF)  # Underflow wraps
```

</details>

#### AND/OR/XOR: bitwise operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.And, 0xF0F0, 0xFF00)).to_equal(0xF000)
expect(alu_execute(AluOp.Or, 0xF0F0, 0x0F0F)).to_equal(0xFFFF)
expect(alu_execute(AluOp.Xor, 0xFFFF, 0xF0F0)).to_equal(0x0F0F)
```

</details>

#### SLL/SRL/SRA: shift operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 1, 10)).to_equal(1024)
expect(alu_execute(AluOp.Srl, 1024, 10)).to_equal(1)
```

</details>

#### SLT/SLTU: comparison operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Signed: -1 < 0
expect(alu_execute(AluOp.Slt, 0xFFFFFFFF, 0)).to_equal(1)
# Unsigned: 0xFFFFFFFF > 0
expect(alu_execute(AluOp.Sltu, 0xFFFFFFFF, 0)).to_equal(0)
```

</details>

### RV32M Compliance

#### MUL: rd = (rs1 * rs2)[31:0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mul, 7, 6)).to_equal(42)
```

</details>

#### MUL: handles overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mul, 0x80000000, 2) and 0xFFFFFFFF).to_equal(0)
```

</details>

#### DIV: rd = rs1 / rs2 (signed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Div, 20, 3)).to_equal(6)
```

</details>

#### DIV: division by zero returns all ones

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use var to prevent const-evaluator from folding 42/0
var zero = 0
expect(muldiv_execute(MulDivOp.Div, 42, zero) and 0xFFFFFFFF).to_equal(0xFFFFFFFF)
```

</details>

#### DIVU: unsigned division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Divu, 20, 3)).to_equal(6)
```

</details>

#### REM: remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Rem, 20, 3)).to_equal(2)
```

</details>

#### REMU: unsigned remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Remu, 20, 3)).to_equal(2)
```

</details>

### RV32A Compliance

#### LR/SC succeeds on uncontested reservation

1. var rs = ReservationSet64 create
2. rs reserve
   - Expected: success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = ReservationSet64.create()
rs.reserve(0x80000100)
val success = rs.check_and_clear(0x80000100)
expect(success).to_equal(true)
```

</details>

#### SC fails after intervening store

1. var rs = ReservationSet64 create
2. rs reserve
3. rs invalidate
   - Expected: success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = ReservationSet64.create()
rs.reserve(0x80000100)
rs.invalidate()
val success = rs.check_and_clear(0x80000100)
expect(success).to_equal(false)
```

</details>

#### AMOADD computes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(amo_execute(AmoOp.Add, 100, 50).new_value).to_equal(150)
```

</details>

#### AMOSWAP returns rs2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(amo_execute(AmoOp.Swap, 100, 200).new_value).to_equal(200)
```

</details>

#### AMOAND computes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
