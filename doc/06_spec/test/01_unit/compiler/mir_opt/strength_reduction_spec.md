# Strength Reduction Specification

> <details>

<!-- sdn-diagram:id=strength_reduction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=strength_reduction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

strength_reduction_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=strength_reduction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Strength Reduction Specification

## Scenarios

### MIR strength reduction

#### declares a reusable built-in MIR pipeline optimization provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider = strength_reduction_provider()
expect(provider.name).to_equal("simple.opt.math.strength_reduce")
expect(provider.kind).to_equal(OptimizerProviderKind.Mir)
expect(provider.lookup_kind).to_equal(OptimizerRuleLookupKind.PipelinePass)
expect(optimization_rule_provider_is_pipeline_pass(provider)).to_equal(true)
expect(optimization_rule_provider_has_required_fact(provider, "integer_widths")).to_equal(true)
expect(optimization_rule_provider_has_required_fact(provider, "non_negative_or_unsigned_operands")).to_equal(true)
expect(provider.produced_facts[0]).to_equal("canonical_integer_arithmetic")
```

</details>

#### lowers net-driver style modulo by 128 to bitmask

-  sr reduce one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_sr_expect_bitand_mask(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Rem, _sr_copy(1), _sr_int(128)), span: nil)),
    127
)
```

</details>

#### lowers 64-bit power-of-two modulo constants to bitmask

-  sr reduce one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_sr_expect_bitand_mask(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Rem, _sr_copy(1), _sr_int(1099511627776)), span: nil)),
    1099511627775
)
```

</details>

#### removes bit-or zero identity

-  sr reduce one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_sr_expect_copy_from(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.BitOr, _sr_copy(1), _sr_int(0)), span: nil)),
    1
)
```

</details>

#### removes bit-xor zero identity

-  sr reduce one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_sr_expect_copy_from(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.BitXor, _sr_int(0), _sr_copy(1)), span: nil)),
    1
)
```

</details>

#### folds bit-and zero annihilator

-  sr reduce one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_sr_expect_int_const(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.BitAnd, _sr_copy(1), _sr_int(0)), span: nil)),
    0
)
```

</details>

#### removes zero left shift

-  sr reduce one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_sr_expect_copy_from(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Shl, _sr_copy(1), _sr_int(0)), span: nil)),
    1
)
```

</details>

#### removes zero right shift

-  sr reduce one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_sr_expect_copy_from(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Shr, _sr_copy(1), _sr_int(0)), span: nil)),
    1
)
```

</details>

#### decomposes multiply by 6 into two shifts and add

- expect kinds len
-  sr expect shift amount
-  sr expect shift amount
-  sr expect binop kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_copy(1), _sr_int(6)), span: nil))
expect kinds.len() == 3
_sr_expect_shift_amount(kinds[0], 2)
_sr_expect_shift_amount(kinds[1], 1)
_sr_expect_binop_kind(kinds[2], MirBinOp.Add)
```

</details>

#### decomposes multiply by 14 into two shifts and subtract

- expect kinds len
-  sr expect shift amount
-  sr expect shift amount
-  sr expect binop kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_int(14), _sr_copy(1)), span: nil))
expect kinds.len() == 3
_sr_expect_shift_amount(kinds[0], 4)
_sr_expect_shift_amount(kinds[1], 1)
_sr_expect_binop_kind(kinds[2], MirBinOp.Sub)
```

</details>

#### decomposes multiply by 11 into two shifts plus source add

- expect kinds len
-  sr expect shift amount
-  sr expect shift amount
-  sr expect binop kind
-  sr expect binop kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_copy(1), _sr_int(11)), span: nil))
expect kinds.len() == 4
_sr_expect_shift_amount(kinds[0], 3)
_sr_expect_shift_amount(kinds[1], 1)
_sr_expect_binop_kind(kinds[2], MirBinOp.Add)
_sr_expect_binop_kind(kinds[3], MirBinOp.Add)
```

</details>

#### decomposes multiply by 13 into two shifts plus source add

- expect kinds len
-  sr expect shift amount
-  sr expect shift amount
-  sr expect binop kind
-  sr expect binop kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_int(13), _sr_copy(1)), span: nil))
expect kinds.len() == 4
_sr_expect_shift_amount(kinds[0], 3)
_sr_expect_shift_amount(kinds[1], 2)
_sr_expect_binop_kind(kinds[2], MirBinOp.Add)
_sr_expect_binop_kind(kinds[3], MirBinOp.Add)
```

</details>

#### decomposes multiply by 17 into shift and add

- expect kinds len
-  sr expect shift amount
-  sr expect binop kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_copy(1), _sr_int(17)), span: nil))
expect kinds.len() == 2
_sr_expect_shift_amount(kinds[0], 4)
_sr_expect_binop_kind(kinds[1], MirBinOp.Add)
```

</details>

#### decomposes multiply by 31 into shift and subtract

- expect kinds len
-  sr expect shift amount
-  sr expect binop kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_int(31), _sr_copy(1)), span: nil))
expect kinds.len() == 2
_sr_expect_shift_amount(kinds[0], 5)
_sr_expect_binop_kind(kinds[1], MirBinOp.Sub)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/strength_reduction_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR strength reduction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
