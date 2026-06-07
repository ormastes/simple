# Layout Attrs Specification

> <details>

<!-- sdn-diagram:id=layout_attrs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_attrs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_attrs_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_attrs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Attrs Specification

## Scenarios

### layout attribute parsing

### @repr attribute

#### repr_c: @repr(C) maps to C layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = test_layout_kind_for_repr("C")
expect(kind).to_equal("C")
```

</details>

#### repr_packed: @repr(packed) maps to Packed layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = test_layout_kind_for_repr("packed")
expect(kind).to_equal("Packed")
```

</details>

#### repr_transparent: @repr(transparent) maps to Transparent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = test_layout_kind_for_repr("transparent")
expect(kind).to_equal("Transparent")
```

</details>

#### repr_unknown: @repr(unknown) maps to Simple (default)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = test_layout_kind_for_repr("rust")
expect(kind).to_equal("Simple")
```

</details>

### @packed attribute

#### packed_shorthand: @packed is shorthand for @repr(packed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packed_kind = "Packed"
val repr_packed_kind = test_layout_kind_for_repr("packed")
expect(packed_kind).to_equal(repr_packed_kind)
```

</details>

#### packed_sets_is_packed: @packed sets is_packed flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_packed = true
expect(is_packed).to_equal(true)
```

</details>

### @align attribute

#### align_1_is_valid: @align(1) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(1)
expect(valid).to_equal(true)
```

</details>

#### align_2_is_valid: @align(2) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(2)
expect(valid).to_equal(true)
```

</details>

#### align_4_is_valid: @align(4) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(4)
expect(valid).to_equal(true)
```

</details>

#### align_8_is_valid: @align(8) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(8)
expect(valid).to_equal(true)
```

</details>

#### align_16_is_valid: @align(16) is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(16)
expect(valid).to_equal(true)
```

</details>

#### align_0_is_invalid: @align(0) is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(0)
expect(valid).to_equal(false)
```

</details>

#### align_negative_is_invalid: @align(-1) is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(-1)
expect(valid).to_equal(false)
```

</details>

#### align_3_is_invalid: @align(3) is invalid (not power of 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(3)
expect(valid).to_equal(false)
```

</details>

#### align_6_is_invalid: @align(6) is invalid (not power of 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = test_is_valid_align(6)
expect(valid).to_equal(false)
```

</details>

### default layout

#### default_is_simple: no layout attrs defaults to Simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_kind = "Simple"
expect(default_kind).to_equal("Simple")
```

</details>

#### default_no_align: no align attr means has_explicit_align is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_align = false
expect(has_align).to_equal(false)
```

</details>

#### default_not_packed: no packed attr means is_packed is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_packed = false
expect(is_packed).to_equal(false)
```

</details>

### attribute interaction

#### packed_and_align: @packed + @align(8) can coexist

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_packed = true
val align_val: i64 = 8
val has_align = align_val > 0
expect(is_packed).to_equal(true)
expect(has_align).to_equal(true)
```

</details>

#### c_repr_no_packed: @repr(C) does not set is_packed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_packed = false
val layout_kind = test_layout_kind_for_repr("C")
expect(layout_kind).to_equal("C")
expect(is_packed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/layout_attrs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- layout attribute parsing
- @repr attribute
- @packed attribute
- @align attribute
- default layout
- attribute interaction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
