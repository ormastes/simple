# Blink Flex Layout Specification

> Tests for the CSS Flexbox Level 1 subset layout engine. Covers item construction defaults, row/column sizing, flex-grow distribution, flex-shrink absorption, justify-content variants, and align-items variants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Flex Layout Specification

Tests for the CSS Flexbox Level 1 subset layout engine. Covers item construction defaults, row/column sizing, flex-grow distribution, flex-shrink absorption, justify-content variants, and align-items variants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Layout |
| Status | Active |
| Source | `test/01_unit/lib/blink/flex_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the CSS Flexbox Level 1 subset layout engine.
Covers item construction defaults, row/column sizing, flex-grow distribution,
flex-shrink absorption, justify-content variants, and align-items variants.

## Scenarios

### flex_item_new

#### grow 0, shrink 1 by default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- grow 0, shrink 1 by default
   - Expected: approx_eq(item.flex_grow, 0.0) is true
   - Expected: approx_eq(item.flex_shrink, 1.0) is true
   - Expected: approx_eq(item.intrinsic_main_size, 100.0) is true
   - Expected: approx_eq(item.intrinsic_cross_size, 50.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grow 0, shrink 1 by default")
val item = flex_item_new(100.0, 50.0)
expect(approx_eq(item.flex_grow, 0.0)).to_equal(true)
expect(approx_eq(item.flex_shrink, 1.0)).to_equal(true)
expect(approx_eq(item.intrinsic_main_size, 100.0)).to_equal(true)
expect(approx_eq(item.intrinsic_cross_size, 50.0)).to_equal(true)
```

</details>

### layout_flex Row fixed sizes

#### Row with 3 fixed-size items: main_pos increments by prev.main_size

- Row with 3 fixed-size items: main_pos increments by prev.main_size
   - Expected: approx_eq(out[0].main_pos, 0.0) is true
   - Expected: approx_eq(out[1].main_pos, 100.0) is true
   - Expected: approx_eq(out[2].main_pos, 250.0) is true
   - Expected: approx_eq(out[0].main_size, 100.0) is true
   - Expected: approx_eq(out[1].main_size, 150.0) is true
   - Expected: approx_eq(out[2].main_size, 200.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Row with 3 fixed-size items: main_pos increments by prev.main_size")
val c = flex_container_row(600.0, 200.0)
val items: [FlexItem] = []
items.push(flex_item_new(100.0, 50.0))
items.push(flex_item_new(150.0, 60.0))
items.push(flex_item_new(200.0, 40.0))
val out = layout_flex(c, items)
# item 0 starts at 0
expect(approx_eq(out[0].main_pos, 0.0)).to_equal(true)
# item 1 starts at 100
expect(approx_eq(out[1].main_pos, 100.0)).to_equal(true)
# item 2 starts at 250
expect(approx_eq(out[2].main_pos, 250.0)).to_equal(true)
# sizes unchanged
expect(approx_eq(out[0].main_size, 100.0)).to_equal(true)
expect(approx_eq(out[1].main_size, 150.0)).to_equal(true)
expect(approx_eq(out[2].main_size, 200.0)).to_equal(true)
```

</details>

### layout_flex flex-grow

#### items with flex_grow distribute free space

- items with flex_grow distribute free space
   - Expected: approx_eq(out[0].main_size, 200.0) is true
   - Expected: approx_eq(out[1].main_size, 300.0) is true
   - Expected: approx_eq(total, 500.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("items with flex_grow distribute free space")
val c = flex_container_row(500.0, 100.0)
val items: [FlexItem] = []
val a = flex_item_new(100.0, 50.0)
a.flex_grow = 1.0
val b = flex_item_new(100.0, 50.0)
b.flex_grow = 2.0
items.push(a)
items.push(b)
val out = layout_flex(c, items)
# free = 500 - 200 = 300; a gets 100, b gets 200
expect(approx_eq(out[0].main_size, 200.0)).to_equal(true)
expect(approx_eq(out[1].main_size, 300.0)).to_equal(true)
# total must equal container
val total = out[0].main_size + out[1].main_size
expect(approx_eq(total, 500.0)).to_equal(true)
```

</details>

### layout_flex flex-shrink

#### items with flex_shrink absorb overflow

- items with flex_shrink absorb overflow
   - Expected: approx_eq(out[0].main_size, 150.0) is true
   - Expected: approx_eq(out[1].main_size, 150.0) is true
   - Expected: approx_eq(total, 300.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("items with flex_shrink absorb overflow")
val c = flex_container_row(300.0, 100.0)
val items: [FlexItem] = []
val a = flex_item_new(200.0, 50.0)
a.flex_shrink = 1.0
val b = flex_item_new(200.0, 50.0)
b.flex_shrink = 1.0
items.push(a)
items.push(b)
val out = layout_flex(c, items)
# overflow = 100; each shrinks by 50
expect(approx_eq(out[0].main_size, 150.0)).to_equal(true)
expect(approx_eq(out[1].main_size, 150.0)).to_equal(true)
val total = out[0].main_size + out[1].main_size
expect(approx_eq(total, 300.0)).to_equal(true)
```

</details>

### layout_flex JustifyContent.Center

#### Center shifts items toward middle

- Center shifts items toward middle
   - Expected: approx_eq(out[0].main_pos, 200.0) is true
   - Expected: approx_eq(out[1].main_pos, 300.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Center shifts items toward middle")
val c = flex_container_row(600.0, 100.0)
c.justify = JustifyContent.Center
val items: [FlexItem] = []
items.push(flex_item_new(100.0, 50.0))
items.push(flex_item_new(100.0, 50.0))
val out = layout_flex(c, items)
# free = 400; offset = 200; item0 at 200, item1 at 300
expect(approx_eq(out[0].main_pos, 200.0)).to_equal(true)
expect(approx_eq(out[1].main_pos, 300.0)).to_equal(true)
# both items start after the left half of the free space
expect(out[0].main_pos).to_be_greater_than(0.0)
```

</details>

### layout_flex JustifyContent.SpaceBetween

#### SpaceBetween puts gaps between items

- SpaceBetween puts gaps between items
   - Expected: approx_eq(out[0].main_pos, 0.0) is true
   - Expected: approx_eq(out[1].main_pos, 200.0) is true
   - Expected: approx_eq(out[2].main_pos, 400.0) is true
   - Expected: approx_eq(gap1, gap2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SpaceBetween puts gaps between items")
val c = flex_container_row(500.0, 100.0)
c.justify = JustifyContent.SpaceBetween
val items: [FlexItem] = []
items.push(flex_item_new(100.0, 50.0))
items.push(flex_item_new(100.0, 50.0))
items.push(flex_item_new(100.0, 50.0))
val out = layout_flex(c, items)
# free = 200; gap between items = 100
# item0 at 0, item1 at 200, item2 at 400
expect(approx_eq(out[0].main_pos, 0.0)).to_equal(true)
expect(approx_eq(out[1].main_pos, 200.0)).to_equal(true)
expect(approx_eq(out[2].main_pos, 400.0)).to_equal(true)
# gaps are equal and larger than zero
val gap1 = out[1].main_pos - (out[0].main_pos + out[0].main_size)
val gap2 = out[2].main_pos - (out[1].main_pos + out[1].main_size)
expect(approx_eq(gap1, gap2)).to_equal(true)
expect(gap1).to_be_greater_than(0.0)
```

</details>

### layout_flex AlignItems.Stretch

#### Stretch sets cross_size to container

- Stretch sets cross_size to container
   - Expected: approx_eq(out[0].cross_size, 200.0) is true
   - Expected: approx_eq(out[1].cross_size, 200.0) is true
   - Expected: approx_eq(out[0].cross_pos, 0.0) is true
   - Expected: approx_eq(out[1].cross_pos, 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Stretch sets cross_size to container")
val c = flex_container_row(400.0, 200.0)
c.align = AlignItems.Stretch
val items: [FlexItem] = []
items.push(flex_item_new(100.0, 50.0))
items.push(flex_item_new(120.0, 80.0))
val out = layout_flex(c, items)
expect(approx_eq(out[0].cross_size, 200.0)).to_equal(true)
expect(approx_eq(out[1].cross_size, 200.0)).to_equal(true)
expect(approx_eq(out[0].cross_pos, 0.0)).to_equal(true)
expect(approx_eq(out[1].cross_pos, 0.0)).to_equal(true)
```

</details>

### layout_flex AlignItems.Center

#### Center positions items along cross midline

- Center positions items along cross midline
   - Expected: approx_eq(out[0].cross_pos, 70.0) is true
   - Expected: approx_eq(out[1].cross_pos, 80.0) is true
   - Expected: approx_eq(out[0].cross_size, 60.0) is true
   - Expected: approx_eq(out[1].cross_size, 40.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Center positions items along cross midline")
val c = flex_container_row(400.0, 200.0)
c.align = AlignItems.Center
val items: [FlexItem] = []
items.push(flex_item_new(100.0, 60.0))
items.push(flex_item_new(120.0, 40.0))
val out = layout_flex(c, items)
# item0 cross_pos = (200 - 60) / 2 = 70
expect(approx_eq(out[0].cross_pos, 70.0)).to_equal(true)
# item1 cross_pos = (200 - 40) / 2 = 80
expect(approx_eq(out[1].cross_pos, 80.0)).to_equal(true)
# cross_size unchanged
expect(approx_eq(out[0].cross_size, 60.0)).to_equal(true)
expect(approx_eq(out[1].cross_size, 40.0)).to_equal(true)
# both positions are within container bounds
expect(out[0].cross_pos).to_be_greater_than(0.0)
expect(out[1].cross_pos).to_be_greater_than(0.0)
expect(out[0].cross_pos).to_be_less_than(200.0)
expect(out[1].cross_pos).to_be_less_than(200.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `eb34f414241519f676fb54ece67e23709f98ca815bc509dcc34ca616a4e97740`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb34f414241519f676fb54ece67e23709f98ca815bc509dcc34ca616a4e97740`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb34f414241519f676fb54ece67e23709f98ca815bc509dcc34ca616a4e97740`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/blink/flex_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/flex_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/blink/flex_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/flex_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/flex_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grow 0, shrink 1 by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/flex_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Row with 3 fixed-size items: main_pos increments by prev.main_size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/flex_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'items with flex_grow distribute free space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
