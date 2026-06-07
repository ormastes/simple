# RV64 W-Variant ALU Unit Tests

> Unit tests for RV64I W-suffix ALU operations (ADDW, SUBW, SLLW, SRLW, SRAW). These operate on the lower 32 bits and sign-extend the 32-bit result to 64 bits.

<!-- sdn-diagram:id=rv64_alu_word_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_alu_word_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_alu_word_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_alu_word_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 W-Variant ALU Unit Tests

Unit tests for RV64I W-suffix ALU operations (ADDW, SUBW, SLLW, SRLW, SRAW). These operate on the lower 32 bits and sign-extend the 32-bit result to 64 bits.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-ALU-WORD-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_alu_word_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for RV64I W-suffix ALU operations (ADDW, SUBW, SLLW, SRLW, SRAW).
These operate on the lower 32 bits and sign-extend the 32-bit result to 64 bits.

## Scenarios

### ADDW Operations

#### ADDW: basic addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Addw, 10, 20)).to_equal(30)
```

</details>

#### ADDW: wraps at 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Addw, 0xFFFFFFFF, 1)).to_equal(0)
```

</details>

#### ADDW: sign-extends negative 32-bit result to 64 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x7FFFFFFF + 1 = 0x80000000 in 32-bit, sign-extends to 0xFFFFFFFF80000000
val result = alu_execute_word(AluOp.Addw, 0x7FFFFFFF, 1)
expect(result).to_equal(0xFFFFFFFF80000000)
```

</details>

#### ADDW: ignores upper 32 bits of inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Addw, 0x10000000A, 0x20000000B)
expect(result).to_equal(0x15)
```

</details>

#### ADDW: -1 + -1 = -2 (sign-extended)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Addw, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)
expect(result).to_equal(0xFFFFFFFFFFFFFFFE)
```

</details>

### SUBW Operations

#### SUBW: basic subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Subw, 50, 20)).to_equal(30)
```

</details>

#### SUBW: underflow wraps and sign-extends

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Subw, 0, 1)
expect(result).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### SUBW: ignores upper 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Subw, 0x10000000A, 0x200000005)
expect(result).to_equal(5)
```

</details>

### SLLW Operations

#### SLLW: shift by 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Sllw, 42, 0)).to_equal(42)
```

</details>

#### SLLW: shift into sign bit and sign-extend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Sllw, 1, 31)
expect(result).to_equal(0xFFFFFFFF80000000)
```

</details>

#### SLLW: uses only lower 5 bits of shift amount

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Sllw, 1, 32)).to_equal(1)
```

</details>

#### SLLW: shift 0xFF by 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Sllw, 0xFF, 8)
expect(result).to_equal(0xFF00)
```

</details>

### SRLW Operations

#### SRLW: shift by 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Srlw, 42, 0)).to_equal(42)
```

</details>

#### SRLW: shift right does not sign-extend within 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x80000000 >> 31 = 1, then sign-extend 32->64: 1
val result = alu_execute_word(AluOp.Srlw, 0x80000000, 31)
expect(result).to_equal(1)
```

</details>

#### SRLW: uses only lower 5 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Srlw, 0x80000000, 32)).to_equal(0xFFFFFFFF80000000)
```

</details>

#### SRLW: ignores upper 32 bits of source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Srlw, 0xFFFFFFFF00000042, 0)
expect(result).to_equal(0x42)
```

</details>

### SRAW Operations

#### SRAW: positive value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Sraw, 0x7FFFFFFF, 1)
expect(result).to_equal(0x3FFFFFFF)
```

</details>

#### SRAW: negative value preserves sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x80000000 >> 1 (arithmetic) = 0xC0000000, sign-ext to 0xFFFFFFFFC0000000
val result = alu_execute_word(AluOp.Sraw, 0x80000000, 1)
expect(result).to_equal(0xFFFFFFFFC0000000)
```

</details>

#### SRAW: shift all the way fills with sign bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Sraw, 0x80000000, 31)
expect(result).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### SRAW: uses only lower 5 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Sraw, 0x80000000, 32)
expect(result).to_equal(0xFFFFFFFF80000000)
```

</details>

### ADDIW Operations

#### ADDIW: positive immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Addw, 0, 100)).to_equal(100)
```

</details>

#### ADDIW: negative immediate sign-extends

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Addw, 0, 0xFFFFFFFFFFFFFFFF)
expect(result).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### ADDIW: result wraps at 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute_word(AluOp.Addw, 0x7FFFFFFF, 1)
expect(result).to_equal(0xFFFFFFFF80000000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
