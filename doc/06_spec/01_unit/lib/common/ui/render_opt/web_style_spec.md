# Web Style Specification

> Tests covering PropertyNames.create pre-registers the built-in property table, ValueInterner parses values -> typed ids ONCE, apply_declarations is O(k): it touches exactly the declared properties, never PROPERTY_COUNT, DeclarationList.clear resets to empty, StyleInterner intern immutable computed styles: dedup equal, distinguish different, StyleInvalidation records per-node per-property pending changes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Style Specification

## Scenarios

### PropertyNames.create pre-registers the built-in property table

#### the eight built-in names resolve to the fixed PropertyIds and nothing else grows the table

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the eight built-in names resolve to the fixed PropertyIds and nothing else grows the table


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the eight built-in names resolve to the fixed PropertyIds and nothing else grows the table")
val names = PropertyNames.create()
assert_true(names.id_for("display") == PROP_DISPLAY)
assert_true(names.id_for("position") == PROP_POSITION)
assert_true(names.id_for("width") == PROP_WIDTH)
assert_true(names.id_for("height") == PROP_HEIGHT)
assert_true(names.count() == PROPERTY_COUNT)
```

</details>

#### registering an already-known name is idempotent (parse names -> id ONCE)

- registering an already-known name is idempotent (parse names -> id ONCE)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registering an already-known name is idempotent (parse names -> id ONCE)")
val names = PropertyNames.create()
val before = names.count()
val id1 = names.register("color")
val id2 = names.register("color")
assert_true(id1 == id2)
assert_true(id1 == PROP_COLOR)
assert_true(names.count() == before)
```

</details>

#### an unknown name grows the table exactly once no matter how many times it's registered

- an unknown name grows the table exactly once no matter how many times it's registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unknown name grows the table exactly once no matter how many times it's registered")
val names = PropertyNames.create()
val before = names.count()
val a = names.register("--custom-prop")
val b = names.register("--custom-prop")
val c = names.register("--custom-prop")
assert_true(a == b)
assert_true(b == c)
assert_true(names.count() == before + 1)
```

</details>

#### an unregistered name reports -1, not a stale/garbage id

- an unregistered name reports -1, not a stale/garbage id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unregistered name reports -1, not a stale/garbage id")
val names = PropertyNames.create()
assert_true(names.id_for("--never-seen") == -1)
```

</details>

### ValueInterner parses values -> typed ids ONCE

#### interning the same text twice returns the same id and does not grow the table

- interning the same text twice returns the same id and does not grow the table


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interning the same text twice returns the same id and does not grow the table")
val v = ValueInterner.create()
val id1 = v.intern("16px")
val id2 = v.intern("16px")
assert_true(id1 == id2)
assert_true(v.count() == 1)
```

</details>

#### distinct values get distinct ids, and text_for round-trips

- distinct values get distinct ids, and text_for round-trips


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinct values get distinct ids, and text_for round-trips")
val v = ValueInterner.create()
val a = v.intern("red")
val b = v.intern("blue")
assert_true(a != b)
assert_true(v.text_for(a) == "red")
assert_true(v.text_for(b) == "blue")
```

</details>

#### text_for on an out-of-range id returns empty rather than garbage

- text_for on an out-of-range id returns empty rather than garbage


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text_for on an out-of-range id returns empty rather than garbage")
val v = ValueInterner.create()
assert_true(v.text_for(999) == "")
assert_true(v.text_for(-1) == "")
```

</details>

### apply_declarations is O(k): it touches exactly the declared properties, never PROPERTY_COUNT

#### a two-declaration list only writes those two fields; every other field stays at its -1/0 default

- a two-declaration list only writes those two fields; every other field stays at its -1/0 default


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a two-declaration list only writes those two fields; every other field stays at its -1/0 default")
val decls = DeclarationList.create()
val v = ValueInterner.create()
assert_true(decls.add(PROP_WIDTH, v.intern("200px"), 0) == WS_OK)
assert_true(decls.add(PROP_COLOR, v.intern("red"), 0) == WS_OK)
val style = ComputedStyleHot.create()
val applied = apply_declarations(style, decls)
assert_true(applied == 2)
# declared fields are set
assert_true(style.width_id == v.intern("200px"))
assert_true(style.color_id == v.intern("red"))
# everything else is untouched (still the create() default)
assert_true(style.display == -1)
assert_true(style.position == -1)
assert_true(style.visibility == -1)
assert_true(style.opacity == -1)
assert_true(style.background_id == -1)
assert_true(style.height_id == -1)
# the sabotage-detection counter: touched exactly 2 times, never
# PROPERTY_COUNT (8) times -- a "wide property probing" regression
# that loops 0..PROPERTY_COUNT checking presence would make this 8.
assert_true(style.touched_count == 2)
assert_true(style.touched_count != PROPERTY_COUNT)
```

</details>

#### layout-bucket and paint-bucket properties set only their own flag bit

- layout-bucket and paint-bucket properties set only their own flag bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("layout-bucket and paint-bucket properties set only their own flag bit")
val decls = DeclarationList.create()
assert_true(decls.add(PROP_WIDTH, 0, 0) == WS_OK)
val style = ComputedStyleHot.create()
apply_declarations(style, decls)
assert_true((style.layout_flags & WS_LAYOUT_FLAG) == WS_LAYOUT_FLAG)
assert_true((style.paint_flags & WS_PAINT_FLAG) == 0)

val decls2 = DeclarationList.create()
assert_true(decls2.add(PROP_OPACITY, 0, 0) == WS_OK)
val style2 = ComputedStyleHot.create()
apply_declarations(style2, decls2)
assert_true((style2.paint_flags & WS_PAINT_FLAG) == WS_PAINT_FLAG)
assert_true((style2.layout_flags & WS_LAYOUT_FLAG) == 0)
```

</details>

#### an empty declaration list touches nothing and returns zero

- an empty declaration list touches nothing and returns zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an empty declaration list touches nothing and returns zero")
val decls = DeclarationList.create()
val style = ComputedStyleHot.create()
val applied = apply_declarations(style, decls)
assert_true(applied == 0)
assert_true(style.touched_count == 0)
assert_true(style.display == -1)
```

</details>

#### touched_count accumulates across repeated applications rather than resetting

- touched_count accumulates across repeated applications rather than resetting


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("touched_count accumulates across repeated applications rather than resetting")
val decls = DeclarationList.create()
assert_true(decls.add(PROP_DISPLAY, 1, 0) == WS_OK)
val style = ComputedStyleHot.create()
apply_declarations(style, decls)
apply_declarations(style, decls)
assert_true(style.touched_count == 2)
```

</details>

### DeclarationList.clear resets to empty

#### count returns to zero and a fresh add starts at index 0 again

- count returns to zero and a fresh add starts at index 0 again


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count returns to zero and a fresh add starts at index 0 again")
val decls = DeclarationList.create()
decls.add(PROP_COLOR, 5, 0)
decls.add(PROP_OPACITY, 6, 0)
assert_true(decls.count == 2)
decls.clear()
assert_true(decls.count == 0)
```

</details>

### StyleInterner intern immutable computed styles: dedup equal, distinguish different

#### two independently-built styles with identical hot fields collapse to the same id

- two independently-built styles with identical hot fields collapse to the same id


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two independently-built styles with identical hot fields collapse to the same id")
val interner = StyleInterner.create()
val a = ComputedStyleHot.create()
a.display = 1
a.color_id = 7
val b = ComputedStyleHot.create()
b.display = 1
b.color_id = 7
val id_a = interner.intern(a)
val id_b = interner.intern(b)
assert_true(id_a == id_b)
assert_true(interner.count() == 1)
assert_true(interner.reuse_count == 1)
```

</details>

#### a style differing in exactly one hot field gets a distinct id

- a style differing in exactly one hot field gets a distinct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a style differing in exactly one hot field gets a distinct id")
val interner = StyleInterner.create()
val a = ComputedStyleHot.create()
a.display = 1
val b = ComputedStyleHot.create()
b.display = 2
val id_a = interner.intern(a)
val id_b = interner.intern(b)
assert_true(id_a != id_b)
assert_true(interner.count() == 2)
assert_true(interner.reuse_count == 0)
```

</details>

#### interned field values round-trip through the column store

- interned field values round-trip through the column store


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interned field values round-trip through the column store")
val interner = StyleInterner.create()
val a = ComputedStyleHot.create()
a.width_id = 42
a.height_id = 99
val id = interner.intern(a)
assert_true(interner.width_id[id] == 42)
assert_true(interner.height_id[id] == 99)
```

</details>

### StyleInvalidation records per-node per-property pending changes

#### mark accumulates entries and count_for_property counts only that property

- mark accumulates entries and count_for_property counts only that property


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mark accumulates entries and count_for_property counts only that property")
val inv = StyleInvalidation.create()
assert_true(inv.mark(1, PROP_COLOR) == WS_OK)
assert_true(inv.mark(2, PROP_COLOR) == WS_OK)
assert_true(inv.mark(1, PROP_WIDTH) == WS_OK)
assert_true(inv.len == 3)
assert_true(inv.count_for_property(PROP_COLOR) == 2)
assert_true(inv.count_for_property(PROP_WIDTH) == 1)
assert_true(inv.count_for_property(PROP_HEIGHT) == 0)
```

</details>

#### has_layout_change is true only when a layout-bucket property is pending

- has_layout_change is true only when a layout-bucket property is pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_layout_change is true only when a layout-bucket property is pending")
val paint_only = StyleInvalidation.create()
paint_only.mark(1, PROP_COLOR)
paint_only.mark(2, PROP_OPACITY)
assert_true(paint_only.has_layout_change() == false)

val mixed = StyleInvalidation.create()
mixed.mark(1, PROP_COLOR)
mixed.mark(2, PROP_WIDTH)
assert_true(mixed.has_layout_change() == true)
```

</details>

#### clear resets len and forgets all prior entries

- clear resets len and forgets all prior entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear resets len and forgets all prior entries")
val inv = StyleInvalidation.create()
inv.mark(1, PROP_DISPLAY)
inv.mark(2, PROP_POSITION)
assert_true(inv.len == 2)
inv.clear()
assert_true(inv.len == 0)
assert_true(inv.count_for_property(PROP_DISPLAY) == 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/render_opt/web_style_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PropertyNames.create pre-registers the built-in property table, ValueInterner parses values -> typed ids ONCE, apply_declarations is O(k): it touches exactly the declared properties, never PROPERTY_COUNT, DeclarationList.clear resets to empty, StyleInterner intern immutable computed styles: dedup equal, distinguish different, StyleInvalidation records per-node per-property pending changes.
- PropertyNames.create pre-registers the built-in property table
- ValueInterner parses values -> typed ids ONCE
- apply_declarations is O(k): it touches exactly the declared properties, never PROPERTY_COUNT
- DeclarationList.clear resets to empty
- StyleInterner intern immutable computed styles: dedup equal, distinguish different
- StyleInvalidation records per-node per-property pending changes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `0316f1440cb546a2ebad6817cd6cfd48bc516aac7e8f345934c3f3a4d02de3f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0316f1440cb546a2ebad6817cd6cfd48bc516aac7e8f345934c3f3a4d02de3f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0316f1440cb546a2ebad6817cd6cfd48bc516aac7e8f345934c3f3a4d02de3f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/render_opt/web_style_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/render_opt/web_style_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/render_opt/web_style_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/render_opt/web_style_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/render_opt/web_style_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the eight built-in names resolve to the fixed PropertyIds and nothing else grows the table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/web_style_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registering an already-known name is idempotent (parse names -> id ONCE)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/web_style_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an unknown name grows the table exactly once no matter how many times it's registered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
