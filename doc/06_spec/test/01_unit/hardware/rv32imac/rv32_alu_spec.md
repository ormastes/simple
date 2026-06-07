# RV32 ALU Unit Tests

> Unit tests for ALU operations with edge cases.

<!-- sdn-diagram:id=rv32_alu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_alu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_alu_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_alu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 ALU Unit Tests

Unit tests for ALU operations with edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-ALU-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/hardware/rv32imac/rv32_alu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for ALU operations with edge cases.

## Scenarios

### ALU Arithmetic

#### ADD: 0 + 0 = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 0, 0)).to_equal(0)
```

</details>

#### ADD: max + 1 wraps to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 0xFFFFFFFF, 1)).to_equal(0)
```

</details>

#### SUB: 0 - 1 = 0xFFFFFFFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sub, 0, 1)).to_equal(0xFFFFFFFF)
```

</details>

#### PASS_B returns second operand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.PassB, 42, 99)).to_equal(99)
```

</details>

### ALU Logic

#### AND with all ones

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.And, 0xDEADBEEF, 0xFFFFFFFF)).to_equal(0xDEADBEEF)
```

</details>

#### OR with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Or, 0xDEADBEEF, 0)).to_equal(0xDEADBEEF)
```

</details>

#### XOR with self

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Xor, 0xDEADBEEF, 0xDEADBEEF)).to_equal(0)
```

</details>

### ALU Shifts

#### SLL by 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 42, 0)).to_equal(42)
```

</details>

#### SLL by 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 1, 31)).to_equal(0x80000000)
```

</details>

#### SRL by 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Srl, 42, 0)).to_equal(42)
```

</details>

#### SRL uses only lower 5 bits of shamt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Srl, 0x80000000, 32)).to_equal(0x80000000)
```

</details>

### ALU Comparisons

#### SLT: equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 5, 5)).to_equal(0)
```

</details>

#### SLT: negative < positive (signed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 0x80000000, 0)).to_equal(1)
```

</details>

#### SLTU: 0 < 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 0, 1)).to_equal(1)
```

</details>

#### SLTU: max unsigned > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 0xFFFFFFFF, 0)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
