# Layer Eq Checker Specification

> Tests covering layer_eq checker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Eq Checker Specification

## Scenarios

### layer_eq checker

#### accepts a same-name implicit view

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a same-name implicit view
   - Expected: v.diagnostic equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a same-name implicit view")
val view = LayerEqType(name: "gui.GuiDeviceRect", total_size: 16, align: 4, fields: [
    f("x", "i32", 0, 4), f("y", "i32", 4, 4),
    f("width", "i32", 8, 4), f("height", "i32", 12, 4)],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, device_rect())
assert_true(v.ok)
expect(v.diagnostic).to_equal("")
```

</details>

#### accepts a fully @layer_field-tagged rename view

- accepts a fully @layer_field-tagged rename view


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a fully @layer_field-tagged rename view")
val view = LayerEqType(name: "gui.GuiBounds", total_size: 16, align: 4, fields: [
    ftag("left", "i32", 0, 4, "x"), ftag("top", "i32", 4, 4, "y"),
    ftag("extent_x", "i32", 8, 4, "width"), ftag("extent_y", "i32", 12, 4, "height")],
    is_enum: false, discriminants: [])
assert_true(check_layer_eq(view, device_rect()).ok)
```

</details>

#### rejects a size mismatch

- rejects a size mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a size mismatch")
val view = LayerEqType(name: "gui.WideRect", total_size: 32, align: 8, fields: [
    f("x", "i64", 0, 8), f("y", "i64", 8, 8),
    f("width", "i64", 16, 8), f("height", "i64", 24, 8)],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, device_rect())
expect_not(v.ok)
assert_true(v.diagnostic.contains("error[layer_eq]"))
```

</details>

#### rejects a field-type mismatch

- rejects a field-type mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a field-type mismatch")
val view = LayerEqType(name: "gui.FloatRect", total_size: 16, align: 4, fields: [
    f("x", "f32", 0, 4), f("y", "i32", 4, 4),
    f("width", "i32", 8, 4), f("height", "i32", 12, 4)],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, device_rect())
expect_not(v.ok)
assert_true(v.diagnostic.contains("f32"))
```

</details>

#### rejects a partial @layer_field tag set

- rejects a partial @layer_field tag set


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a partial @layer_field tag set")
val view = LayerEqType(name: "gui.HalfTagged", total_size: 16, align: 4, fields: [
    ftag("left", "i32", 0, 4, "x"), f("y", "i32", 4, 4),
    f("width", "i32", 8, 4), f("height", "i32", 12, 4)],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, device_rect())
expect_not(v.ok)
assert_true(v.diagnostic.contains("tag all fields or none"))
```

</details>

#### rejects a field-count mismatch

- rejects a field-count mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a field-count mismatch")
val view = LayerEqType(name: "gui.Point", total_size: 8, align: 4, fields: [
    f("x", "i32", 0, 4), f("y", "i32", 4, 4)],
    is_enum: false, discriminants: [])
expect_not(check_layer_eq(view, device_rect()).ok)
```

</details>

#### rejects a mapping to a nonexistent target field

- rejects a mapping to a nonexistent target field


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a mapping to a nonexistent target field")
val view = LayerEqType(name: "gui.BadMap", total_size: 16, align: 4, fields: [
    ftag("left", "i32", 0, 4, "x"), ftag("top", "i32", 4, 4, "y"),
    ftag("extent_x", "i32", 8, 4, "width"), ftag("extent_y", "i32", 12, 4, "depth")],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, device_rect())
expect_not(v.ok)
assert_true(v.diagnostic.contains("depth"))
```

</details>

#### accepts matching enum discriminants in the same positions

- accepts matching enum discriminants in the same positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts matching enum discriminants in the same positions")
val view = LayerEqType(name: "gui.GuiTag", total_size: 4, align: 4, fields: [
    f("none", "unit", 0, 0), f("solid", "unit", 0, 0), f("gradient", "unit", 0, 0)],
    is_enum: true, discriminants: [0, 1, 2])
assert_true(check_layer_eq(view, enum_target()).ok)
```

</details>

#### rejects an is_enum view whose discriminants array doesn't cover every field (fails closed, never silently skips)

- rejects an is_enum view whose discriminants array doesn't cover every field (fails closed, never silently skips)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an is_enum view whose discriminants array doesn't cover every field (fails closed, never silently skips)")
val view = LayerEqType(name: "gui.GuiTagShort", total_size: 4, align: 4, fields: [
    f("none", "unit", 0, 0), f("solid", "unit", 0, 0), f("gradient", "unit", 0, 0)],
    is_enum: true, discriminants: [0, 1])
val v = check_layer_eq(view, enum_target())
expect_not(v.ok)
assert_true(v.diagnostic.contains("discriminants"))
```

</details>

#### SABOTAGE: rejects an enum view whose discriminant values diverge (reordered tags)

- SABOTAGE: rejects an enum view whose discriminant values diverge (reordered tags)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE: rejects an enum view whose discriminant values diverge (reordered tags)")
val view = LayerEqType(name: "gui.GuiTagSwapped", total_size: 4, align: 4, fields: [
    f("none", "unit", 0, 0), f("solid", "unit", 0, 0), f("gradient", "unit", 0, 0)],
    is_enum: true, discriminants: [0, 2, 1])
val v = check_layer_eq(view, enum_target())
expect_not(v.ok)
assert_true(v.diagnostic.contains("discriminant"))
```

</details>

#### accepts matching owned+mutable fields on both sides

- accepts matching owned+mutable fields on both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts matching owned+mutable fields on both sides")
val view = LayerEqType(name: "gui.OwnedView", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.OwnedTarget", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
assert_true(check_layer_eq(view, target).ok)
```

</details>

#### SABOTAGE: rejects a borrowed view over an owned target

- SABOTAGE: rejects a borrowed view over an owned target


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE: rejects a borrowed view over an owned target")
val view = LayerEqType(name: "gui.BorrowedView", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "borrowed", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.OwnedTarget", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("ownership"))
```

</details>

#### SABOTAGE: rejects an immutable view over a mutable target

- SABOTAGE: rejects an immutable view over a mutable target


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE: rejects an immutable view over a mutable target")
val view = LayerEqType(name: "gui.ImmutView", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", false, "", "", "", "", "")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.MutTarget", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("mutable"))
```

</details>

#### accepts matching default (host/stack) address spaces on both sides

- accepts matching default (host/stack) address spaces on both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts matching default (host/stack) address spaces on both sides")
val view = LayerEqType(name: "gui.HostView", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.HostTarget", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
assert_true(check_layer_eq(view, target).ok)
```

</details>

#### SABOTAGE: rejects a device-address-space view over a host target

- SABOTAGE: rejects a device-address-space view over a host target


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE: rejects a device-address-space view over a host target")
val view = LayerEqType(name: "gpu.DeviceView", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "device", "", "", "", "")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.HostTarget", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("address_space"))
```

</details>

#### accepts matching @unit/@space tags on both sides (DevicePixelRect self-eq)

- accepts matching @unit/@space tags on both sides (DevicePixelRect self-eq)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts matching @unit/@space tags on both sides (DevicePixelRect self-eq)")
val view = LayerEqType(name: "gui.DevicePixelView", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "device_px", "document", "", "")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.DevicePixelTarget", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "device_px", "document", "", "")],
    is_enum: false, discriminants: [])
assert_true(check_layer_eq(view, target).ok)
```

</details>

#### SABOTAGE: rejects CssLogicalRect (@unit css_px) over DevicePixelRect (@unit device_px) — never equivalent

- SABOTAGE: rejects CssLogicalRect (@unit css_px) over DevicePixelRect (@unit device_px) — never equivalent


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE: rejects CssLogicalRect (@unit css_px) over DevicePixelRect (@unit device_px) — never equivalent")
val view = LayerEqType(name: "css.CssLogicalRectView", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "css_px", "document", "", "")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.DevicePixelRect", total_size: 4, align: 4, fields: [
    ftagged("x", "i32", 0, 4, "owned", true, "", "device_px", "document", "", "")],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("@unit"))
```

</details>

#### SABOTAGE: absent tag is NOT equivalent to a present tag (@color srgb8 vs untagged)

- SABOTAGE: absent tag is NOT equivalent to a present tag (@color srgb8 vs untagged)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE: absent tag is NOT equivalent to a present tag (@color srgb8 vs untagged)")
val view = LayerEqType(name: "gui.UntaggedColorView", total_size: 4, align: 4, fields: [
    ftagged("c", "i32", 0, 4, "owned", true, "", "", "", "", "")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.Srgb8ColorTarget", total_size: 4, align: 4, fields: [
    ftagged("c", "i32", 0, 4, "owned", true, "", "", "", "srgb8", "")],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("@color"))
```

</details>

#### SABOTAGE: rejects straight vs premultiplied @alpha (never silently coerced)

- SABOTAGE: rejects straight vs premultiplied @alpha (never silently coerced)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE: rejects straight vs premultiplied @alpha (never silently coerced)")
val view = LayerEqType(name: "gui.StraightAlphaView", total_size: 4, align: 4, fields: [
    ftagged("c", "i32", 0, 4, "owned", true, "", "", "", "srgb8", "straight")],
    is_enum: false, discriminants: [])
val target = LayerEqType(name: "draw.PremultipliedAlphaTarget", total_size: 4, align: 4, fields: [
    ftagged("c", "i32", 0, 4, "owned", true, "", "", "", "srgb8", "premultiplied")],
    is_enum: false, discriminants: [])
val v = check_layer_eq(view, target)
expect_not(v.ok)
assert_true(v.diagnostic.contains("@alpha"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/layer_eq_checker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering layer_eq checker.
- layer_eq checker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `f2fbdde7f505ba93f078de609e38dc08f1407256b72d6e9abe6aa23f7557edcc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2fbdde7f505ba93f078de609e38dc08f1407256b72d6e9abe6aa23f7557edcc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2fbdde7f505ba93f078de609e38dc08f1407256b72d6e9abe6aa23f7557edcc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/layer_eq_checker_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/layer_eq_checker_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/layer_eq_checker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/layer_eq_checker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/layer_eq_checker_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a same-name implicit view' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/layer_eq_checker_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a fully @layer_field-tagged rename view' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/layer_eq_checker_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a size mismatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
