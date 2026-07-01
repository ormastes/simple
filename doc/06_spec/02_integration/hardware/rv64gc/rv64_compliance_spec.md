# RV64 ISA Compliance Integration Tests

> Validates each RV64GC extension against the RISC-V ISA specification.

<!-- sdn-diagram:id=rv64_compliance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_compliance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_compliance_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_compliance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 ISA Compliance Integration Tests

Validates each RV64GC extension against the RISC-V ISA specification.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-COMPLIANCE-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/02_integration/hardware/rv64gc/rv64_compliance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates each RV64GC extension against the RISC-V ISA specification.

## Scenarios

### RV64I Compliance

#### ADD wraps at 64 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 0xFFFFFFFFFFFFFFFF, 1)).to_equal(0)
```

</details>

#### ADDW sign-extends 32-bit result

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Addw, 0x7FFFFFFF, 1)).to_equal(0xFFFFFFFF80000000)
```

</details>

#### SLL uses lower 6 bits only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 1, 64)).to_equal(1)
```

</details>

#### SRA fills with sign bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sra, 0x8000000000000000, 1)).to_equal(0xC000000000000000)
```

</details>

#### SLT: MIN_I64 < 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 0x8000000000000000, 0)).to_equal(1)
```

</details>

#### SLTU: MAX_U64 > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 0, 0xFFFFFFFFFFFFFFFF)).to_equal(1)
```

</details>

#### SRLW uses lower 5 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Srlw, 0x80000000, 32)).to_equal(0xFFFFFFFF80000000)
```

</details>

#### SRAW fills with 32-bit sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Sraw, 0x80000000, 31)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### RV64M Compliance

#### MUL: lower 64 bits of product

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Mul, 0x100000000, 0x100000000)).to_equal(0)
```

</details>

#### DIV: divide by zero = -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Div, 42, 0)).to_equal(-1)
```

</details>

#### DIVU: divide by zero = MAX_U64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Divu, 42, 0)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### DIV: overflow MIN/-1 = MIN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Div, 0x8000000000000000, -1)).to_equal(0x8000000000000000)
```

</details>

#### REM: divide by zero = dividend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute(MulDivOp.Rem, 42, 0)).to_equal(42)
```

</details>

#### MULW: sign-extends 32-bit product

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Mulw, 0x40000000, 2)).to_equal(0xFFFFFFFF80000000)
```

</details>

#### DIVW: divide by zero = -1 (sign-ext)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(muldiv_execute_word(MulDivOp.Divw, 42, 0)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### RV64A Compliance

#### AMOADD returns old and computes new

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

#### AMOSWAP stores new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = amo_execute(AmoOp.Swap, 100, 200)
expect(r.new_value).to_equal(200)
```

</details>

#### AMOMAX signed comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = amo_execute(AmoOp.Max, -10, 5)
expect(r.new_value).to_equal(5)
```

</details>

#### AMOMINU unsigned comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = amo_execute(AmoOp.Minu, 0xFFFFFFFFFFFFFFFF, 5)
expect(r.new_value).to_equal(5)
```

</details>

#### AMOAND bitwise

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = amo_execute(AmoOp.And, 0xFF, 0x0F)
expect(r.new_value).to_equal(0x0F)
```

</details>

### RV64F Compliance

#### F extension presence check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# misa bit 5 (F) should be set
val misa = 0x800000000014112D
expect((misa >> 5) and 1).to_equal(1)
```

</details>

### RV64D Compliance

#### D extension presence check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# misa bit 3 (D) should be set
val misa = 0x800000000014112D
expect((misa >> 3) and 1).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
