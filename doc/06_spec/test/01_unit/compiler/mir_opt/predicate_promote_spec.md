# Predicate Promote Specification

> <details>

<!-- sdn-diagram:id=predicate_promote_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=predicate_promote_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

predicate_promote_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=predicate_promote_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Predicate Promote Specification

## Scenarios

### predicate_promote — MaskFromCmp+MaskedAdd fuses to PredicatedAdd

#### two-instruction block yields one instruction after fusion

- make mask from cmp inst
- make masked add inst
   - Expected: result.instructions.len() equals `1`
   - Expected: inst_is_predicated_add(result.instructions[0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insts = [
    make_mask_from_cmp_inst(10, 1, 2),
    make_masked_add_inst(20, 10, 3, 4)
]
val blk = make_test_block(1, insts)
val result = promote_block_predicate(blk)
expect(result.instructions.len()).to_equal(1)
expect(inst_is_predicated_add(result.instructions[0])).to_equal(true)
```

</details>

### predicate_promote — MaskFromCmp+MaskedMul fuses to PredicatedMul

#### two-instruction block yields one PredicatedMul

- make mask from cmp inst
- make masked mul inst
   - Expected: result.instructions.len() equals `1`
   - Expected: inst_is_predicated_mul(result.instructions[0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insts = [
    make_mask_from_cmp_inst(10, 1, 2),
    make_masked_mul_inst(20, 10, 3, 4)
]
val blk = make_test_block(1, insts)
val result = promote_block_predicate(blk)
expect(result.instructions.len()).to_equal(1)
expect(inst_is_predicated_mul(result.instructions[0])).to_equal(true)
```

</details>

### predicate_promote — MaskFromCmp+MaskedFma fuses to PredicatedFma

#### two-instruction block yields one PredicatedFma

- make mask from cmp inst
- make masked fma inst
   - Expected: result.instructions.len() equals `1`
   - Expected: inst_is_predicated_fma(result.instructions[0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insts = [
    make_mask_from_cmp_inst(10, 1, 2),
    make_masked_fma_inst(20, 10, 3, 4, 5)
]
val blk = make_test_block(1, insts)
val result = promote_block_predicate(blk)
expect(result.instructions.len()).to_equal(1)
expect(inst_is_predicated_fma(result.instructions[0])).to_equal(true)
```

</details>

### predicate_promote — fuses second pair in block independently

#### block with two MaskFromCmp+MaskedAdd pairs yields two PredicatedAdd instructions

- make mask from cmp inst
- make masked add inst
- make mask from cmp inst
- make masked add inst
   - Expected: result.instructions.len() equals `2`
   - Expected: inst_is_predicated_add(result.instructions[0]) is true
   - Expected: inst_is_predicated_add(result.instructions[1]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insts = [
    make_mask_from_cmp_inst(10, 1, 2),
    make_masked_add_inst(20, 10, 3, 4),
    make_mask_from_cmp_inst(11, 5, 6),
    make_masked_add_inst(21, 11, 7, 8)
]
val blk = make_test_block(1, insts)
val result = promote_block_predicate(blk)
expect(result.instructions.len()).to_equal(2)
expect(inst_is_predicated_add(result.instructions[0])).to_equal(true)
expect(inst_is_predicated_add(result.instructions[1])).to_equal(true)
```

</details>

### predicate_promote — operand_is_local utility

#### Copy operand matching local id returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = make_copy_op(42)
val id = make_local(42)
expect(operand_is_local(op, id)).to_equal(true)
```

</details>

#### Copy operand with different id returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = make_copy_op(42)
val id = make_local(99)
expect(operand_is_local(op, id)).to_equal(false)
```

</details>

### predicate_promote — wrong mask local: both instructions preserved

#### MaskedAdd referencing a different local yields 2 instructions

- make mask from cmp inst
- make masked add inst
   - Expected: result.instructions.len() equals `2`
   - Expected: inst_is_mask_from_cmp(result.instructions[0]) is true
   - Expected: inst_is_masked_add(result.instructions[1]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MaskFromCmp produces %10, MaskedAdd consumes %11 (mismatch)
val insts = [
    make_mask_from_cmp_inst(10, 1, 2),
    make_masked_add_inst(20, 11, 3, 4)
]
val blk = make_test_block(1, insts)
val result = promote_block_predicate(blk)
expect(result.instructions.len()).to_equal(2)
expect(inst_is_mask_from_cmp(result.instructions[0])).to_equal(true)
expect(inst_is_masked_add(result.instructions[1])).to_equal(true)
```

</details>

### predicate_promote — non-adjacent: intervening instruction blocks fusion

#### MaskFromCmp, BinOp, MaskedAdd yields 3 instructions unchanged

- make mask from cmp inst
- make binop inst
- make masked add inst
   - Expected: result.instructions.len() equals `3`
   - Expected: inst_is_mask_from_cmp(result.instructions[0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insts = [
    make_mask_from_cmp_inst(10, 1, 2),
    make_binop_inst(99),
    make_masked_add_inst(20, 10, 3, 4)
]
val blk = make_test_block(1, insts)
val result = promote_block_predicate(blk)
expect(result.instructions.len()).to_equal(3)
expect(inst_is_mask_from_cmp(result.instructions[0])).to_equal(true)
```

</details>

### predicate_promote — standalone MaskedAdd without prior MaskFromCmp

#### single MaskedAdd in block is passed through unchanged

- make masked add inst
   - Expected: result.instructions.len() equals `1`
   - Expected: inst_is_masked_add(result.instructions[0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insts = [
    make_masked_add_inst(20, 10, 3, 4)
]
val blk = make_test_block(1, insts)
val result = promote_block_predicate(blk)
expect(result.instructions.len()).to_equal(1)
expect(inst_is_masked_add(result.instructions[0])).to_equal(true)
```

</details>

### predicate_promote — empty module passes through unchanged

#### run_predicate_promote on empty module returns 0 functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_predicate_promote(MirModule(name: "empty", functions: {}, statics: {}, constants: {}, types: {}))
expect(result.functions.len()).to_equal(0)
```

</details>

### predicate_promote — trailing MaskFromCmp with no following Masked* is preserved

#### lone MaskFromCmp at end of block is kept

- make mask from cmp inst
   - Expected: result.instructions.len() equals `1`
   - Expected: inst_is_mask_from_cmp(result.instructions[0]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val insts = [
    make_mask_from_cmp_inst(10, 1, 2)
]
val blk = make_test_block(1, insts)
val result = promote_block_predicate(blk)
expect(result.instructions.len()).to_equal(1)
expect(inst_is_mask_from_cmp(result.instructions[0])).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/predicate_promote_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- predicate_promote — MaskFromCmp+MaskedAdd fuses to PredicatedAdd
- predicate_promote — MaskFromCmp+MaskedMul fuses to PredicatedMul
- predicate_promote — MaskFromCmp+MaskedFma fuses to PredicatedFma
- predicate_promote — fuses second pair in block independently
- predicate_promote — operand_is_local utility
- predicate_promote — wrong mask local: both instructions preserved
- predicate_promote — non-adjacent: intervening instruction blocks fusion
- predicate_promote — standalone MaskedAdd without prior MaskFromCmp
- predicate_promote — empty module passes through unchanged
- predicate_promote — trailing MaskFromCmp with no following Masked* is preserved

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
