# Constant Folding Specification

> <details>

<!-- sdn-diagram:id=constant_folding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=constant_folding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

constant_folding_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=constant_folding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Constant Folding Specification

## Scenarios

### MIR Constant Folding

#### runs after inlining and before final cleanup in optimized pipelines

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val speed_passes = optimizationpipeline_passes_for_level(OptLevel.Speed)
val aggressive_passes = optimizationpipeline_passes_for_level(OptLevel.Aggressive)
val speed_inline_idx = speed_passes.index_of("inline_functions")
val speed_post_inline_cf_idx = _cf_index_after(speed_passes, "constant_folding", speed_inline_idx)
val aggressive_strength_idx = aggressive_passes.index_of("strength_reduction")
val aggressive_final_cf_idx = _cf_index_after(aggressive_passes, "constant_folding", aggressive_strength_idx)
val aggressive_final_dce_idx = _cf_index_after(aggressive_passes, "dead_code_elimination", aggressive_strength_idx)

expect(speed_inline_idx < speed_post_inline_cf_idx).to_equal(true)
expect(speed_post_inline_cf_idx < speed_passes.index_of("body_outlining")).to_equal(true)
expect(aggressive_strength_idx < aggressive_final_cf_idx).to_equal(true)
expect(aggressive_final_cf_idx < aggressive_final_dce_idx).to_equal(true)
```

</details>

#### simplifies commutative left-hand integer identities

1.  cf fold one

2.  cf fold one

3.  cf fold one

4.  cf fold one


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_cf_expect_copy(
    _cf_fold_one(MirInst(kind: MirInstKind.BinOp(_cf_lid(2), MirBinOp.Add, _cf_int(0), _cf_copy(1)), span: nil)),
    1
)
_cf_expect_copy(
    _cf_fold_one(MirInst(kind: MirInstKind.BinOp(_cf_lid(3), MirBinOp.Mul, _cf_int(1), _cf_copy(1)), span: nil)),
    1
)
_cf_expect_copy(
    _cf_fold_one(MirInst(kind: MirInstKind.BinOp(_cf_lid(4), MirBinOp.BitOr, _cf_int(0), _cf_copy(1)), span: nil)),
    1
)
_cf_expect_copy(
    _cf_fold_one(MirInst(kind: MirInstKind.BinOp(_cf_lid(5), MirBinOp.BitXor, _cf_int(0), _cf_copy(1)), span: nil)),
    1
)
```

</details>

#### simplifies integer annihilators and shift-by-zero

1.  cf fold one

2.  cf fold one

3.  cf fold one


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_cf_expect_int(
    _cf_fold_one(MirInst(kind: MirInstKind.BinOp(_cf_lid(2), MirBinOp.Mul, _cf_int(0), _cf_copy(1)), span: nil)),
    0
)
_cf_expect_int(
    _cf_fold_one(MirInst(kind: MirInstKind.BinOp(_cf_lid(3), MirBinOp.BitAnd, _cf_copy(1), _cf_int(0)), span: nil)),
    0
)
_cf_expect_copy(
    _cf_fold_one(MirInst(kind: MirInstKind.BinOp(_cf_lid(4), MirBinOp.Shl, _cf_copy(1), _cf_int(0)), span: nil)),
    1
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/constant_folding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR Constant Folding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
