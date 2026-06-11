# RV64 ALU Unit Tests

> Unit tests for 64-bit ALU operations with edge cases.

<!-- sdn-diagram:id=rv64_alu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_alu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_alu_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_alu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 ALU Unit Tests

Unit tests for 64-bit ALU operations with edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-ALU-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_alu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for 64-bit ALU operations with edge cases.

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

#### ADD: basic addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 10, 20)).to_equal(30)
```

</details>

#### ADD: max + 1 wraps to min (signed overflow)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 0x7FFFFFFFFFFFFFFF, 1)).to_equal(0x8000000000000000)
```

</details>

#### ADD: unsigned max + 1 wraps to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 0xFFFFFFFFFFFFFFFF, 1)).to_equal(0)
```

</details>

#### SUB: 0 - 1 = -1 (all bits set)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sub, 0, 1)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### SUB: basic subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sub, 50, 20)).to_equal(30)
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
expect(alu_execute(AluOp.And, 0xDEADBEEFCAFEBABE, 0xFFFFFFFFFFFFFFFF)).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### AND masks upper 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.And, 0xFFFFFFFF00000000, 0x00000000FFFFFFFF)).to_equal(0)
```

</details>

#### OR with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Or, 0xDEADBEEFCAFEBABE, 0)).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### OR combines upper and lower halves

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Or, 0xFFFF000000000000, 0x000000000000FFFF)).to_equal(0xFFFF00000000FFFF)
```

</details>

#### XOR with self is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Xor, 0xDEADBEEFCAFEBABE, 0xDEADBEEFCAFEBABE)).to_equal(0)
```

</details>

#### XOR flips all bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Xor, 0xAAAAAAAAAAAAAAAA, 0xFFFFFFFFFFFFFFFF)).to_equal(0x5555555555555555)
```

</details>

### ALU Shifts (64-bit)

#### SLL by 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 42, 0)).to_equal(42)
```

</details>

#### SLL by 32 shifts into upper half

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 1, 32)).to_equal(0x100000000)
```

</details>

#### SLL by 63

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 1, 63)).to_equal(0x8000000000000000)
```

</details>

#### SLL uses only lower 6 bits of shamt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 1, 64)).to_equal(1)
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

#### SRL by 32 shifts from upper half

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Srl, 0x100000000, 32)).to_equal(1)
```

</details>

#### SRL does not sign-extend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Srl, 0x8000000000000000, 63)).to_equal(1)
```

</details>

#### SRA preserves sign bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sra, 0x8000000000000000, 63)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### SRA positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sra, 0x7FFFFFFFFFFFFFFF, 1)).to_equal(0x3FFFFFFFFFFFFFFF)
```

</details>

### ALU Comparisons (64-bit)

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
expect(alu_execute(AluOp.Slt, 0x8000000000000000, 0)).to_equal(1)
```

</details>

#### SLT: positive < negative is false (signed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 0, 0x8000000000000000)).to_equal(0)
```

</details>

#### SLT: -1 < 0 (signed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 0xFFFFFFFFFFFFFFFF, 0)).to_equal(1)
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

#### SLTU: 0x8000000000000000 > 0 (unsigned)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 0, 0x8000000000000000)).to_equal(1)
```

</details>

#### SLTU: max unsigned > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 0, 0xFFFFFFFFFFFFFFFF)).to_equal(1)
```

</details>

#### SLTU: equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 42, 42)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
