# RV64 W-Variant Multiply/Divide Unit Tests

> Unit tests for W-suffix multiply/divide (MULW, DIVW, DIVUW, REMW, REMUW). 32-bit operations with sign-extension to 64 bits.

<!-- sdn-diagram:id=rv64_muldiv_word_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_muldiv_word_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_muldiv_word_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_muldiv_word_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 W-Variant Multiply/Divide Unit Tests

Unit tests for W-suffix multiply/divide (MULW, DIVW, DIVUW, REMW, REMUW). 32-bit operations with sign-extension to 64 bits.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-MULDIV-WORD-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_muldiv_word_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for W-suffix multiply/divide (MULW, DIVW, DIVUW, REMW, REMUW).
32-bit operations with sign-extension to 64 bits.

## Scenarios

### MULW

#### MULW: 3 * 4 = 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Mulw, 3, 4)).to_equal(12)
```

</details>

#### MULW: wraps at 32 bits and sign-extends

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = muldiv_execute_word(MulDivOp.Mulw, 0x40000000, 2)
expect(result).to_equal(0xFFFFFFFF80000000)
```

</details>

#### MULW: ignores upper 32 bits of inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = muldiv_execute_word(MulDivOp.Mulw, 0x100000003, 0x200000004)
expect(result).to_equal(12)
```

</details>

### DIVW

#### DIVW: 20 / 4 = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Divw, 20, 4)).to_equal(5)
```

</details>

#### DIVW: divide by zero returns -1 (sign-extended)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Divw, 20, 0)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### DIVW: overflow 0x80000000 / -1 = 0x80000000 (sign-extended)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = muldiv_execute_word(MulDivOp.Divw, 0x80000000, 0xFFFFFFFF)
expect(result).to_equal(0xFFFFFFFF80000000)
```

</details>

### DIVUW

#### DIVUW: 20 / 4 = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Divuw, 20, 4)).to_equal(5)
```

</details>

#### DIVUW: divide by zero returns 0xFFFFFFFF (sign-extended)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Divuw, 20, 0)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### DIVUW: treats operands as unsigned 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = muldiv_execute_word(MulDivOp.Divuw, 0xFFFFFFFF, 2)
expect(result).to_equal(0x7FFFFFFF)
```

</details>

### REMW

#### REMW: 20 % 3 = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Remw, 20, 3)).to_equal(2)
```

</details>

#### REMW: negative remainder sign-extends

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = muldiv_execute_word(MulDivOp.Remw, -20, 3)
expect(result).to_equal(0xFFFFFFFFFFFFFFFE)
```

</details>

#### REMW: divide by zero returns dividend (32-bit sign-ext)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Remw, 20, 0)).to_equal(20)
```

</details>

### REMUW

#### REMUW: 20 % 3 = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Remuw, 20, 3)).to_equal(2)
```

</details>

#### REMUW: unsigned semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = muldiv_execute_word(MulDivOp.Remuw, 0xFFFFFFFF, 0x10000000)
expect(result).to_equal(0x0FFFFFFF)
```

</details>

#### REMUW: divide by zero returns dividend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Remuw, 20, 0)).to_equal(20)
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
