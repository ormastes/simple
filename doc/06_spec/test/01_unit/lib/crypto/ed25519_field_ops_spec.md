# Ed25519 Field Ops Specification

> <details>

<!-- sdn-diagram:id=ed25519_field_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ed25519_field_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ed25519_field_ops_spec -> std
ed25519_field_ops_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ed25519_field_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed25519 Field Ops Specification

## Scenarios

### Ed25519 field and base-point primitives

#### encodes the field identity as canonical little-endian one

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fe_to_bytes(fe_one())).to_equal(_one_bytes())
```

</details>

#### squares across the 64-bit boundary without collapsing to zero

1. var x = fe add

2. x = fe sq
   - Expected: fe_to_bytes(x) equals `_two_pow_64_bytes()`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = fe_add(fe_one(), fe_one())
var i: u64 = 0
while i < 6:
    x = fe_sq(x)
    i = i + 1
expect(fe_to_bytes(x)).to_equal(_two_pow_64_bytes())
```

</details>

#### inverts two so two times inverse two is one

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val two = fe_add(fe_one(), fe_one())
expect(fe_to_bytes(fe_mul(two, fe_invert(two)))).to_equal(_one_bytes())
```

</details>

#### adds the Ed25519 identity point without changing the base point

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = _ed25519_base_point()
val sum = ed_point_add(ed_point_identity(), base)
expect(ed_point_encode(sum)).to_equal(ed_point_encode(base))
```

</details>

#### scalar-multiplies the base point by one

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = _ed25519_base_point()
val one = _one_bytes()
expect(ed_point_encode(ed_scalar_mul(one, base))).to_equal(ed_point_encode(base))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/ed25519_field_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ed25519 field and base-point primitives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
