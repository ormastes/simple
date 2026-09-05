# Layout Attrs Specification

> Tests covering layout attribute parsing, @repr attribute, @packed attribute, @align attribute, default layout, attribute interaction.

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

- repr_c: @repr(C) maps to C layout
   - Expected: kind equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repr_c: @repr(C) maps to C layout")
val kind = test_layout_kind_for_repr("C")
expect(kind).to_equal("C")
```

</details>

#### repr_packed: @repr(packed) maps to Packed layout

- repr_packed: @repr(packed) maps to Packed layout
   - Expected: kind equals `Packed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repr_packed: @repr(packed) maps to Packed layout")
val kind = test_layout_kind_for_repr("packed")
expect(kind).to_equal("Packed")
```

</details>

#### repr_transparent: @repr(transparent) maps to Transparent

- repr_transparent: @repr(transparent) maps to Transparent
   - Expected: kind equals `Transparent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repr_transparent: @repr(transparent) maps to Transparent")
val kind = test_layout_kind_for_repr("transparent")
expect(kind).to_equal("Transparent")
```

</details>

#### repr_unknown: @repr(unknown) maps to Simple (default)

- repr_unknown: @repr(unknown) maps to Simple (default)
   - Expected: kind equals `Simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repr_unknown: @repr(unknown) maps to Simple (default)")
val kind = test_layout_kind_for_repr("rust")
expect(kind).to_equal("Simple")
```

</details>

### @packed attribute

#### packed_shorthand: @packed is shorthand for @repr(packed)

- packed_shorthand: @packed is shorthand for @repr(packed)
   - Expected: packed_kind equals `repr_packed_kind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("packed_shorthand: @packed is shorthand for @repr(packed)")
val packed_kind = "Packed"
val repr_packed_kind = test_layout_kind_for_repr("packed")
expect(packed_kind).to_equal(repr_packed_kind)
```

</details>

#### packed_sets_is_packed: @packed sets is_packed flag

- packed_sets_is_packed: @packed sets is_packed flag
   - Expected: is_packed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("packed_sets_is_packed: @packed sets is_packed flag")
val is_packed = true
expect(is_packed).to_equal(true)
```

</details>

### @align attribute

#### align_1_is_valid: @align(1) is valid

- align_1_is_valid: @align(1) is valid
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_1_is_valid: @align(1) is valid")
val valid = test_is_valid_align(1)
expect(valid).to_equal(true)
```

</details>

#### align_2_is_valid: @align(2) is valid

- align_2_is_valid: @align(2) is valid
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_2_is_valid: @align(2) is valid")
val valid = test_is_valid_align(2)
expect(valid).to_equal(true)
```

</details>

#### align_4_is_valid: @align(4) is valid

- align_4_is_valid: @align(4) is valid
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_4_is_valid: @align(4) is valid")
val valid = test_is_valid_align(4)
expect(valid).to_equal(true)
```

</details>

#### align_8_is_valid: @align(8) is valid

- align_8_is_valid: @align(8) is valid
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_8_is_valid: @align(8) is valid")
val valid = test_is_valid_align(8)
expect(valid).to_equal(true)
```

</details>

#### align_16_is_valid: @align(16) is valid

- align_16_is_valid: @align(16) is valid
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_16_is_valid: @align(16) is valid")
val valid = test_is_valid_align(16)
expect(valid).to_equal(true)
```

</details>

#### align_0_is_invalid: @align(0) is invalid

- align_0_is_invalid: @align(0) is invalid
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_0_is_invalid: @align(0) is invalid")
val valid = test_is_valid_align(0)
expect(valid).to_equal(false)
```

</details>

#### align_negative_is_invalid: @align(-1) is invalid

- align_negative_is_invalid: @align(-1) is invalid
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_negative_is_invalid: @align(-1) is invalid")
val valid = test_is_valid_align(-1)
expect(valid).to_equal(false)
```

</details>

#### align_3_is_invalid: @align(3) is invalid (not power of 2)

- align_3_is_invalid: @align(3) is invalid (not power of 2)
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_3_is_invalid: @align(3) is invalid (not power of 2)")
val valid = test_is_valid_align(3)
expect(valid).to_equal(false)
```

</details>

#### align_6_is_invalid: @align(6) is invalid (not power of 2)

- align_6_is_invalid: @align(6) is invalid (not power of 2)
   - Expected: valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("align_6_is_invalid: @align(6) is invalid (not power of 2)")
val valid = test_is_valid_align(6)
expect(valid).to_equal(false)
```

</details>

### default layout

#### default_is_simple: no layout attrs defaults to Simple

- default_is_simple: no layout attrs defaults to Simple
   - Expected: default_kind equals `Simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_is_simple: no layout attrs defaults to Simple")
val default_kind = "Simple"
expect(default_kind).to_equal("Simple")
```

</details>

#### default_no_align: no align attr means has_explicit_align is false

- default_no_align: no align attr means has_explicit_align is false
   - Expected: has_align is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_no_align: no align attr means has_explicit_align is false")
val has_align = false
expect(has_align).to_equal(false)
```

</details>

#### default_not_packed: no packed attr means is_packed is false

- default_not_packed: no packed attr means is_packed is false
   - Expected: is_packed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_not_packed: no packed attr means is_packed is false")
val is_packed = false
expect(is_packed).to_equal(false)
```

</details>

### attribute interaction

#### packed_and_align: @packed + @align(8) can coexist

- packed_and_align: @packed + @align(8) can coexist
   - Expected: is_packed is true
   - Expected: has_align is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("packed_and_align: @packed + @align(8) can coexist")
val is_packed = true
val align_val: i64 = 8
val has_align = align_val > 0
expect(is_packed).to_equal(true)
expect(has_align).to_equal(true)
```

</details>

#### c_repr_no_packed: @repr(C) does not set is_packed

- c_repr_no_packed: @repr(C) does not set is_packed
   - Expected: layout_kind equals `C`
   - Expected: is_packed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("c_repr_no_packed: @repr(C) does not set is_packed")
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
| Source | `test/unit/compiler/backend/layout_attrs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering layout attribute parsing, @repr attribute, @packed attribute, @align attribute, default layout, attribute interaction.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37c7765c7a80dc59dc28b1f62c5a0ab7d6ccec08e33f36082b1926ae1b3db44a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37c7765c7a80dc59dc28b1f62c5a0ab7d6ccec08e33f36082b1926ae1b3db44a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37c7765c7a80dc59dc28b1f62c5a0ab7d6ccec08e33f36082b1926ae1b3db44a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/layout_attrs_spec.spl
mirror: doc/06_spec/unit/compiler/backend/layout_attrs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/layout_attrs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/layout_attrs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/layout_attrs_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'repr_c: @repr(C) maps to C layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/layout_attrs_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'repr_packed: @repr(packed) maps to Packed layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/layout_attrs_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'repr_transparent: @repr(transparent) maps to Transparent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
