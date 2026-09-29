# Responsive Widget Specification

> Tests covering SizeClass.to_wire, Orientation.to_wire, with_responsive_layout, with_responsive_columns, with_show_when_at_most, with_show_when_at_least, with_show_when_orientation, WidgetNode.responsive_columns, WidgetNode.responsive_layout, WidgetNode.show_when_at_most, WidgetNode.show_when_at_least, WidgetNode.show_when_orientation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Responsive Widget Specification

## Scenarios

### SizeClass.to_wire

#### compact serializes to lowercase compact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compact serializes to lowercase compact
   - Expected: SizeClass.Compact.to_wire() equals `compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compact serializes to lowercase compact")
expect(SizeClass.Compact.to_wire()).to_equal("compact")
```

</details>

#### regular serializes to lowercase regular

- regular serializes to lowercase regular
   - Expected: SizeClass.Regular.to_wire() equals `regular`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("regular serializes to lowercase regular")
expect(SizeClass.Regular.to_wire()).to_equal("regular")
```

</details>

#### expanded serializes to lowercase expanded

- expanded serializes to lowercase expanded
   - Expected: SizeClass.Expanded.to_wire() equals `expanded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expanded serializes to lowercase expanded")
expect(SizeClass.Expanded.to_wire()).to_equal("expanded")
```

</details>

### Orientation.to_wire

#### landscape serializes to lowercase landscape

- landscape serializes to lowercase landscape
   - Expected: Orientation.Landscape.to_wire() equals `landscape`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("landscape serializes to lowercase landscape")
expect(Orientation.Landscape.to_wire()).to_equal("landscape")
```

</details>

#### portrait serializes to lowercase portrait

- portrait serializes to lowercase portrait
   - Expected: Orientation.Portrait.to_wire() equals `portrait`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("portrait serializes to lowercase portrait")
expect(Orientation.Portrait.to_wire()).to_equal("portrait")
```

</details>

#### square serializes to lowercase square

- square serializes to lowercase square
   - Expected: Orientation.Square.to_wire() equals `square`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("square serializes to lowercase square")
expect(Orientation.Square.to_wire()).to_equal("square")
```

</details>

### with_responsive_layout

#### stores compact layout prop

- stores compact layout prop
   - Expected: n.get_prop("responsive_compact") equals `vbox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores compact layout prop")
val node = text_widget("w1", "hello")
val n = with_responsive_layout(node, "vbox", "hbox", "grid")
expect(n.get_prop("responsive_compact")).to_equal("vbox")
```

</details>

#### stores regular layout prop

- stores regular layout prop
   - Expected: n.get_prop("responsive_regular") equals `hbox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores regular layout prop")
val node = text_widget("w2", "hello")
val n = with_responsive_layout(node, "vbox", "hbox", "grid")
expect(n.get_prop("responsive_regular")).to_equal("hbox")
```

</details>

#### stores expanded layout prop

- stores expanded layout prop
   - Expected: n.get_prop("responsive_expanded") equals `grid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores expanded layout prop")
val node = text_widget("w3", "hello")
val n = with_responsive_layout(node, "vbox", "hbox", "grid")
expect(n.get_prop("responsive_expanded")).to_equal("grid")
```

</details>

### with_responsive_columns

#### stores compact column count

- stores compact column count
   - Expected: n.get_prop("responsive_cols_compact") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores compact column count")
val node = text_widget("g1", "x")
val n = with_responsive_columns(node, 1, 2, 4)
expect(n.get_prop("responsive_cols_compact")).to_equal("1")
```

</details>

#### stores regular column count

- stores regular column count
   - Expected: n.get_prop("responsive_cols_regular") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores regular column count")
val node = text_widget("g2", "x")
val n = with_responsive_columns(node, 1, 2, 4)
expect(n.get_prop("responsive_cols_regular")).to_equal("2")
```

</details>

#### stores expanded column count

- stores expanded column count
   - Expected: n.get_prop("responsive_cols_expanded") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores expanded column count")
val node = text_widget("g3", "x")
val n = with_responsive_columns(node, 1, 2, 4)
expect(n.get_prop("responsive_cols_expanded")).to_equal("4")
```

</details>

### with_show_when_at_most

#### stores compact threshold

- stores compact threshold
   - Expected: n.get_prop("show_when_at_most") equals `compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores compact threshold")
val node = text_widget("sm1", "x")
val n = with_show_when_at_most(node, SizeClass.Compact)
expect(n.get_prop("show_when_at_most")).to_equal("compact")
```

</details>

#### stores regular threshold

- stores regular threshold
   - Expected: n.get_prop("show_when_at_most") equals `regular`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores regular threshold")
val node = text_widget("sm2", "x")
val n = with_show_when_at_most(node, SizeClass.Regular)
expect(n.get_prop("show_when_at_most")).to_equal("regular")
```

</details>

### with_show_when_at_least

#### stores expanded threshold

- stores expanded threshold
   - Expected: n.get_prop("show_when_at_least") equals `expanded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores expanded threshold")
val node = text_widget("sl1", "x")
val n = with_show_when_at_least(node, SizeClass.Expanded)
expect(n.get_prop("show_when_at_least")).to_equal("expanded")
```

</details>

### with_show_when_orientation

#### stores portrait orientation

- stores portrait orientation
   - Expected: n.get_prop("show_when_orientation") equals `portrait`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores portrait orientation")
val node = text_widget("so1", "x")
val n = with_show_when_orientation(node, Orientation.Portrait)
expect(n.get_prop("show_when_orientation")).to_equal("portrait")
```

</details>

#### stores landscape orientation

- stores landscape orientation
   - Expected: n.get_prop("show_when_orientation") equals `landscape`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores landscape orientation")
val node = text_widget("so2", "x")
val n = with_show_when_orientation(node, Orientation.Landscape)
expect(n.get_prop("show_when_orientation")).to_equal("landscape")
```

</details>

### WidgetNode.responsive_columns

#### stores all three column counts via method

- stores all three column counts via method
   - Expected: node.get_prop("responsive_cols_compact") equals `1`
   - Expected: node.get_prop("responsive_cols_regular") equals `2`
   - Expected: node.get_prop("responsive_cols_expanded") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores all three column counts via method")
var node = text_widget("mn1", "x")
node = node.responsive_columns(1, 2, 4)
expect(node.get_prop("responsive_cols_compact")).to_equal("1")
expect(node.get_prop("responsive_cols_regular")).to_equal("2")
expect(node.get_prop("responsive_cols_expanded")).to_equal("4")
```

</details>

### WidgetNode.responsive_layout

#### stores all three layout names via method

- stores all three layout names via method
   - Expected: node.get_prop("responsive_compact") equals `vbox`
   - Expected: node.get_prop("responsive_regular") equals `hbox`
   - Expected: node.get_prop("responsive_expanded") equals `grid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores all three layout names via method")
var node = text_widget("mn2", "x")
node = node.responsive_layout("vbox", "hbox", "grid")
expect(node.get_prop("responsive_compact")).to_equal("vbox")
expect(node.get_prop("responsive_regular")).to_equal("hbox")
expect(node.get_prop("responsive_expanded")).to_equal("grid")
```

</details>

### WidgetNode.show_when_at_most

#### stores threshold via method

- stores threshold via method
   - Expected: node.get_prop("show_when_at_most") equals `compact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores threshold via method")
var node = text_widget("mn3", "x")
node = node.show_when_at_most(SizeClass.Compact)
expect(node.get_prop("show_when_at_most")).to_equal("compact")
```

</details>

### WidgetNode.show_when_at_least

#### stores threshold via method

- stores threshold via method
   - Expected: node.get_prop("show_when_at_least") equals `regular`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores threshold via method")
var node = text_widget("mn4", "x")
node = node.show_when_at_least(SizeClass.Regular)
expect(node.get_prop("show_when_at_least")).to_equal("regular")
```

</details>

### WidgetNode.show_when_orientation

#### stores orientation via method

- stores orientation via method
   - Expected: node.get_prop("show_when_orientation") equals `portrait`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores orientation via method")
var node = text_widget("mn5", "x")
node = node.show_when_orientation(Orientation.Portrait)
expect(node.get_prop("show_when_orientation")).to_equal("portrait")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/responsive_widget_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SizeClass.to_wire, Orientation.to_wire, with_responsive_layout, with_responsive_columns, with_show_when_at_most, with_show_when_at_least, with_show_when_orientation, WidgetNode.responsive_columns, WidgetNode.responsive_layout, WidgetNode.show_when_at_most, WidgetNode.show_when_at_least, WidgetNode.show_when_orientation.
- SizeClass.to_wire
- Orientation.to_wire
- with_responsive_layout
- with_responsive_columns
- with_show_when_at_most
- with_show_when_at_least
- with_show_when_orientation
- WidgetNode.responsive_columns
- WidgetNode.responsive_layout
- WidgetNode.show_when_at_most
- WidgetNode.show_when_at_least
- WidgetNode.show_when_orientation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `f8bc57cd5398a8f4f9dfeb759d1e2dcf6b071a24f25d1606400b57e8693f944f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8bc57cd5398a8f4f9dfeb759d1e2dcf6b071a24f25d1606400b57e8693f944f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8bc57cd5398a8f4f9dfeb759d1e2dcf6b071a24f25d1606400b57e8693f944f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/responsive_widget_spec.spl
mirror: doc/06_spec/unit/app/ui/responsive_widget_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/responsive_widget_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/responsive_widget_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/responsive_widget_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compact serializes to lowercase compact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/responsive_widget_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'regular serializes to lowercase regular' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/responsive_widget_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expanded serializes to lowercase expanded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
