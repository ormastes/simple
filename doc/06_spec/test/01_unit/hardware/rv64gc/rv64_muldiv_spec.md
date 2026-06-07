# RV64 Multiply/Divide Unit Tests

> Unit tests for 64-bit multiply and divide operations (RV64M extension).

<!-- sdn-diagram:id=rv64_muldiv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_muldiv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_muldiv_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_muldiv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Multiply/Divide Unit Tests

Unit tests for 64-bit multiply and divide operations (RV64M extension).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-MULDIV-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_muldiv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for 64-bit multiply and divide operations (RV64M extension).

## Scenarios

### MUL (64-bit)

#### MUL: 3 * 4 = 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mul, 3, 4)).to_equal(12)
```

</details>

#### MUL: large values (lower 64 bits)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mul, 0x100000000, 2)).to_equal(0x200000000)
```

</details>

#### MUL: negative * positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mul, -3, 4)).to_equal(-12)
```

</details>

#### MUL: negative * negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mul, -3, -4)).to_equal(12)
```

</details>

### MULH (signed upper 64 bits)

#### MULH: small values produce 0 upper bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mulh, 3, 4)).to_equal(0)
```

</details>

#### MULH: large positive * positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mulh, 0x7FFFFFFFFFFFFFFF, 2)).to_equal(0)
```

</details>

#### MULH: -1 * -1 = upper bits 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mulh, -1, -1)).to_equal(0)
```

</details>

### MULHSU (signed * unsigned upper bits)

#### MULHSU: positive * positive same as MULHU

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mulhsu, 3, 4)).to_equal(0)
```

</details>

#### MULHSU: negative * unsigned

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = muldiv_execute(MulDivOp.Mulhsu, -1, 1)
expect(result).to_equal(-1)
```

</details>

### MULHU (unsigned upper 64 bits)

#### MULHU: small values produce 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mulhu, 3, 4)).to_equal(0)
```

</details>

#### MULHU: max * 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = muldiv_execute(MulDivOp.Mulhu, 0xFFFFFFFFFFFFFFFF, 2)
expect(result).to_equal(1)
```

</details>

### DIV (signed)

#### DIV: 20 / 4 = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Div, 20, 4)).to_equal(5)
```

</details>

#### DIV: -20 / 4 = -5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Div, -20, 4)).to_equal(-5)
```

</details>

#### DIV: divide by zero returns -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Div, 20, 0)).to_equal(-1)
```

</details>

#### DIV: overflow MIN_I64 / -1 = MIN_I64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Div, 0x8000000000000000, -1)).to_equal(0x8000000000000000)
```

</details>

### DIVU (unsigned)

#### DIVU: 20 / 4 = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Divu, 20, 4)).to_equal(5)
```

</details>

#### DIVU: divide by zero returns MAX_U64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Divu, 20, 0)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### DIVU: large unsigned values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Divu, 0xFFFFFFFFFFFFFFFF, 2)).to_equal(0x7FFFFFFFFFFFFFFF)
```

</details>

### REM (signed)

#### REM: 20 % 3 = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Rem, 20, 3)).to_equal(2)
```

</details>

#### REM: -20 % 3 = -2 (sign follows dividend)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Rem, -20, 3)).to_equal(-2)
```

</details>

#### REM: divide by zero returns dividend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Rem, 20, 0)).to_equal(20)
```

</details>

### REMU (unsigned)

#### REMU: 20 % 3 = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Remu, 20, 3)).to_equal(2)
```

</details>

#### REMU: divide by zero returns dividend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Remu, 20, 0)).to_equal(20)
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
