# RV32 M Extension Unit Tests

> Unit tests for multiply and divide operations.

<!-- sdn-diagram:id=rv32_muldiv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_muldiv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_muldiv_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_muldiv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 M Extension Unit Tests

Unit tests for multiply and divide operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-MEXT-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/hardware/rv32imac/rv32_muldiv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for multiply and divide operations.

## Scenarios

### MUL Operations

#### basic multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Mul, 6, 7)).to_equal(42)
```

</details>

#### multiply by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Mul, 12345, 0)).to_equal(0)
```

</details>

#### multiply by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Mul, 12345, 1)).to_equal(12345)
```

</details>

#### overflow wraps to lower 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Mul, 0x10000, 0x10000)).to_equal(0)
```

</details>

### DIV Operations

#### basic division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Div, 42, 6)).to_equal(7)
```

</details>

#### truncates toward zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Div, 7, 2)).to_equal(3)
```

</details>

### DIVU Operations

#### basic unsigned division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Divu, 100, 10)).to_equal(10)
```

</details>

### REM Operations

#### basic remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Rem, 10, 3)).to_equal(1)
```

</details>

#### remainder of exact division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Rem, 12, 4)).to_equal(0)
```

</details>

### REMU Operations

#### basic unsigned remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(AluOp.Remu, 10, 3)).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
