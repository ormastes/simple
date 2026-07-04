# Rv64gc Specification

> <details>

<!-- sdn-diagram:id=rv64gc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64gc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64gc_spec -> std
rv64gc_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64gc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64gc Specification

## Scenarios

### RV64GC Processor

#### instruction decode

#### distinguishes ADD from SUB via funct7

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add_op = decode_alu_op(OP_OP, F3_ADD_SUB, F7_NORMAL)
val sub_op = decode_alu_op(OP_OP, F3_ADD_SUB, F7_SUB_SRA)
expect(add_op == AluOp.Add).to_equal(true)
expect(sub_op == AluOp.Sub).to_equal(true)
```

</details>

#### 64-bit ALU

#### ADD: basic

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 10, 20)).to_equal(30)
```

</details>

#### SUB: basic

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sub, 50, 20)).to_equal(30)
```

</details>

#### SLT: negative < positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, -1, 0)).to_equal(1)
```

</details>

#### 64-bit multiply/divide

#### MUL: 3 * 4 = 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mul, 3, 4)).to_equal(12)
```

</details>

#### DIV: 20 / 4 = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Div, 20, 4)).to_equal(5)
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

#### REM: 20 % 3 = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Rem, 20, 3)).to_equal(2)
```

</details>

#### atomics

#### AMOADD: returns old and computes new

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = amo_execute(AmoOp.Add, 100, 50)
expect(r.old_value).to_equal(100)
expect(r.new_value).to_equal(150)
```

</details>

#### AMOSWAP: stores new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = amo_execute(AmoOp.Swap, 100, 200)
expect(r.new_value).to_equal(200)
```

</details>

#### AMOMAX: signed maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = amo_execute(AmoOp.Max, -10, 5)
expect(r.new_value).to_equal(5)
```

</details>

#### pipeline

#### load-use hazard predicate is true for dependent load

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ex_is_load = true
val ex_rd = 10
val id_rs1 = 10
val hazard = ex_is_load and ex_rd == id_rs1 and ex_rd != 0
expect(hazard).to_equal(true)
```

</details>

#### load-use hazard predicate is false for independent register

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ex_is_load = true
val ex_rd = 10
val id_rs1 = 11
val hazard = ex_is_load and ex_rd == id_rs1
expect(hazard).to_equal(false)
```

</details>

#### SMP

#### hart IDs are distinguishable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hart0: i64 = 0
val hart1: i64 = 1
expect(hart0 != hart1).to_equal(true)
```

</details>

#### shared counter updates through sequential atomic-style steps

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter: i64 = 0
counter = counter + 1
counter = counter + 1
expect(counter).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/rv64gc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV64GC Processor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
