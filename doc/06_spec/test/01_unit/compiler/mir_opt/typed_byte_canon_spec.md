# MIR Transforms Specification (Bounds-Check Extension + Typed-Byte Canonicalization)

> Validates both MIR optimization transforms from AC-4: 1. Bounds-check elimination extension with explicit-range and constant-index proofs 2. TypedByteCanon pass for typed-byte load/store canonicalization (width widening, alignment)

<!-- sdn-diagram:id=typed_byte_canon_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=typed_byte_canon_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

typed_byte_canon_spec -> std
typed_byte_canon_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=typed_byte_canon_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR Transforms Specification (Bounds-Check Extension + Typed-Byte Canonicalization)

Validates both MIR optimization transforms from AC-4: 1. Bounds-check elimination extension with explicit-range and constant-index proofs 2. TypedByteCanon pass for typed-byte load/store canonicalization (width widening, alignment)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #hw-access-optimization-infra |
| Category | Infrastructure |
| Difficulty | 4/5 |
| Status | Draft |
| Plan | doc/03_plan/pure_simple_lib_standalone_hw_plan.md |
| Source | `test/01_unit/compiler/mir_opt/typed_byte_canon_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates both MIR optimization transforms from AC-4:
1. Bounds-check elimination extension with explicit-range and constant-index proofs
2. TypedByteCanon pass for typed-byte load/store canonicalization (width widening, alignment)

## Behavior

- BoundsCheckElimination extended with ExplicitRangeProof and ConstantIndexProof
- TypedByteCanon implements MirPass trait
- TypedByteCanon depends on bounds_check_elimination
- Canonicalization widens narrow byte loads/stores when safe

## Scenarios

### BoundsCheckElimination Extended

### ExplicitRangeProof

#### AC-4: proof struct holds var_id, lower_bound, upper_bound

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proof = ExplicitRangeProof(var_id: 1, lower_bound: 0, upper_bound: 10, proof_key: "range_1")

expect(proof.var_id).to_equal(1)
expect(proof.lower_bound).to_equal(0)
expect(proof.upper_bound).to_equal(10)
```

</details>

#### AC-4: proof_key is a non-empty text

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proof = ExplicitRangeProof(var_id: 1, lower_bound: 0, upper_bound: 10, proof_key: "range_guard_x")

val key_len = proof.proof_key.len()
expect(key_len).to_be_greater_than(0)
```

</details>

### ConstantIndexProof

#### AC-4: proof struct holds index_const and arr_local_id

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proof = ConstantIndexProof(index_const: 3, arr_local_id: 42, proof_key: "const_idx_3")

expect(proof.index_const).to_equal(3)
expect(proof.arr_local_id).to_equal(42)
```

</details>

#### AC-4: constant index proof can eliminate known-safe access

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proof = ConstantIndexProof(index_const: 0, arr_local_id: 10, proof_key: "first_elem")

# Index 0 on any non-empty array is always safe
val is_zero_idx = proof.index_const == 0
expect(is_zero_idx).to_equal(true)
```

</details>

### TypedByteCanon

### create_typed_byte_canon_pass

#### AC-4: creates pass with zero initial counters

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_obj = create_typed_byte_canon_pass()

expect(pass_obj.rewrites).to_equal(0)
expect(pass_obj.widened_loads).to_equal(0)
expect(pass_obj.widened_stores).to_equal(0)
```

</details>

### MirPass trait

#### AC-4: name returns typed_byte_canon

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_obj = create_typed_byte_canon_pass()
val pass_name = pass_obj.name()

expect(pass_name).to_equal("typed_byte_canon")
```

</details>

#### AC-4: description is non-empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_obj = create_typed_byte_canon_pass()
val desc = pass_obj.description()

val desc_len = desc.len()
expect(desc_len).to_be_greater_than(0)
```

</details>

#### AC-4: is_analysis_pass returns false

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_obj = create_typed_byte_canon_pass()
val is_analysis = pass_obj.is_analysis_pass()

expect(is_analysis).to_equal(false)
```

</details>

#### AC-4: dependencies includes bounds_check_elimination

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pass_obj = create_typed_byte_canon_pass()
val deps = pass_obj.dependencies()

expect(deps).to_contain("bounds_check_elimination")
```

</details>

### PassKind enum

#### AC-4: PassKind has TypedByteCanon variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = PassKind.TypedByteCanon

val is_tbc = kind == PassKind.TypedByteCanon
expect(is_tbc).to_equal(true)
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


## Related Documentation

- **Plan:** [doc/03_plan/pure_simple_lib_standalone_hw_plan.md](doc/03_plan/pure_simple_lib_standalone_hw_plan.md)


</details>
