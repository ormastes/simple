# chart_gui_view_spec

> Chart GUI view spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# chart_gui_view_spec

Chart GUI view spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/chart_gui_view_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Chart GUI view spec.

chart_gui_view(sheet, chart_kind, value_range, labels_range, title, w, h)
builds the chart GUI surface: a WidgetNode tree (rendered for real pixels by
the CLI, one progress-bar widget per data point since the browser engine has
no inline-SVG support) plus a plain-text pipe-separated dump (for testability
without parsing HTML/widget trees). The dump's first line is
"chart|<kind>|<title>"; each following line is
"bar|<label>|<value>|<pct-of-max>". Ranges that are empty/unparseable or
resolve to mismatched lengths fail closed with an "error|<reason>" line
instead of crashing.

## Scenarios

### chart_gui_view: header line

#### the first line carries the chart kind and title

- the first line carries the chart kind and title
   - Expected: lines[0] equals `chart|bar|Sales`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the first line carries the chart kind and title")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Q1")
sheet.set_value("B1", "5")
val view = chart_gui_view(sheet, "bar", "B1:B1", "A1:A1", "Sales", 80, 40)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("chart|bar|Sales")
```

</details>

### chart_gui_view: per-point values
_Each data point contributes one bar|<label>|<value>|<pct> line._

#### each data point line carries its label, value, and pct-of-max

- each data point line carries its label, value, and pct-of-max
   - Expected: lines[1] equals `bar|Widget|10|50`
   - Expected: lines[2] equals `bar|Gadget|20|100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each data point line carries its label, value, and pct-of-max")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
sheet.set_value("A2", "Gadget")
sheet.set_value("B2", "20")
val view = chart_gui_view(sheet, "bar", "B1:B2", "A1:A2", "T", 80, 40)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("bar|Widget|10|50")
expect(lines[2]).to_equal("bar|Gadget|20|100")
```

</details>

#### a formula cell's computed value appears, not the raw formula text

- a formula cell's computed value appears, not the raw formula text


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a formula cell's computed value appears, not the raw formula text")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Base")
sheet.set_value("B1", "10")
sheet.set_value("A2", "Sum")
sheet.set_value("B2", "=B1+5")
sheet = recalculate_formula_cells(sheet)
val view = chart_gui_view(sheet, "bar", "B1:B2", "A1:A2", "T", 80, 40)
expect(view.text_dump).to_contain("bar|Sum|15|100")
assert_false(_dump_contains(view.text_dump, "=B1+5"))
```

</details>

### chart_gui_view: column kind

#### each column line carries its label, value, and pct-of-max

- each column line carries its label, value, and pct-of-max
   - Expected: lines[0] equals `chart|column|T`
   - Expected: lines[1] equals `col|Widget|10|50`
   - Expected: lines[2] equals `col|Gadget|20|100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each column line carries its label, value, and pct-of-max")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
sheet.set_value("A2", "Gadget")
sheet.set_value("B2", "20")
val view = chart_gui_view(sheet, "column", "B1:B2", "A1:A2", "T", 80, 40)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("chart|column|T")
expect(lines[1]).to_equal("col|Widget|10|50")
expect(lines[2]).to_equal("col|Gadget|20|100")
```

</details>

### chart_gui_view: pie kind

#### each pie segment carries its label, value, and share-of-total

- each pie segment carries its label, value, and share-of-total
   - Expected: lines[0] equals `chart|pie|T`
   - Expected: lines[1] equals `pie|Widget|10|33`
   - Expected: lines[2] equals `pie|Gadget|20|66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each pie segment carries its label, value, and share-of-total")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
sheet.set_value("A2", "Gadget")
sheet.set_value("B2", "20")
val view = chart_gui_view(sheet, "pie", "B1:B2", "A1:A2", "T", 80, 40)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("chart|pie|T")
expect(lines[1]).to_equal("pie|Widget|10|33")
expect(lines[2]).to_equal("pie|Gadget|20|66")
```

</details>

### chart_gui_view: pct-of-max
_The point holding the max value always gets pct-of-max 100._

#### the max value point gets exactly 100, others scale proportionally

- the max value point gets exactly 100, others scale proportionally
   - Expected: lines[1] equals `bar|a|3|25`
   - Expected: lines[2] equals `bar|b|12|100`
   - Expected: lines[3] equals `bar|c|6|50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the max value point gets exactly 100, others scale proportionally")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "a")
sheet.set_value("B1", "3")
sheet.set_value("A2", "b")
sheet.set_value("B2", "12")
sheet.set_value("A3", "c")
sheet.set_value("B3", "6")
val view = chart_gui_view(sheet, "bar", "B1:B3", "A1:A3", "T", 80, 40)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("bar|a|3|25")
expect(lines[2]).to_equal("bar|b|12|100")
expect(lines[3]).to_equal("bar|c|6|50")
```

</details>

### chart_gui_view: empty range fails closed
_An empty/unparseable range must not crash; it produces an error line._

#### an unparseable value range produces an error line, no crash

- an unparseable value range produces an error line, no crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unparseable value range produces an error line, no crash")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "x")
val view = chart_gui_view(sheet, "bar", "", "A1:A1", "T", 80, 40)
expect(view.text_dump).to_contain("error|empty-range")
```

</details>

### chart_gui_view: mismatched range lengths fail closed

#### a 2-cell labels range against a 1-cell value range produces an error line

- a 2-cell labels range against a 1-cell value range produces an error line


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a 2-cell labels range against a 1-cell value range produces an error line")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "x")
sheet.set_value("A2", "y")
sheet.set_value("B1", "10")
val view = chart_gui_view(sheet, "bar", "B1:B1", "A1:A2", "T", 80, 40)
expect(view.text_dump).to_contain("error|range-length-mismatch")
```

</details>

### chart session

#### chart_session_view renders the same dump as a direct chart_gui_view call

- chart_session_view renders the same dump as a direct chart_gui_view call
   - Expected: view.text_dump equals `direct.text_dump`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chart_session_view renders the same dump as a direct chart_gui_view call")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
sheet.set_value("A2", "Gadget")
sheet.set_value("B2", "20")
val session = chart_session_new(sheet, "bar", "B1:B2", "A1:A2", "Sales")
val view = chart_session_view(session)
val direct = chart_gui_view(sheet, "bar", "B1:B2", "A1:A2", "Sales", 80, 40)
expect(view.text_dump).to_equal(direct.text_dump)
```

</details>

#### set_value_range changes the dump to the new column's hand-computed values/pcts

- set_value_range changes the dump to the new column's hand-computed values/pcts
   - Expected: session.last_error equals ``
   - Expected: session.value_range equals `C1:C2`
   - Expected: lines[1] equals `bar|Widget|5|33`
   - Expected: lines[2] equals `bar|Gadget|15|100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_value_range changes the dump to the new column's hand-computed values/pcts")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
sheet.set_value("C1", "5")
sheet.set_value("A2", "Gadget")
sheet.set_value("B2", "20")
sheet.set_value("C2", "15")
var session = chart_session_new(sheet, "bar", "B1:B2", "A1:A2", "Sales")
session = chart_session_set_value_range(session, "C1:C2")
expect(session.last_error).to_equal("")
expect(session.value_range).to_equal("C1:C2")
val view = chart_session_view(session)
val lines = view.text_dump.split("\n")
# C1:C2 = 5,15 -> max=15: Widget=5/15*100=33 (int-truncated), Gadget=15/15*100=100
expect(lines[1]).to_equal("bar|Widget|5|33")
expect(lines[2]).to_equal("bar|Gadget|15|100")
```

</details>

#### set_value_range with an unparseable range leaves value_range unchanged and sets last_error

- set_value_range with an unparseable range leaves value_range unchanged and sets last_error
   - Expected: session.value_range equals `B1:B1`
   - Expected: session.last_error equals `empty-range`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_value_range with an unparseable range leaves value_range unchanged and sets last_error")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
var session = chart_session_new(sheet, "bar", "B1:B1", "A1:A1", "Sales")
session = chart_session_set_value_range(session, "")
expect(session.value_range).to_equal("B1:B1")
expect(session.last_error).to_equal("empty-range")
```

</details>

#### set_kind with a chart.spl-known-but-GUI-unsupported kind leaves chart_kind unchanged and sets last_error

- set_kind with a chart.spl-known-but-GUI-unsupported kind leaves chart_kind unchanged and sets last_error
   - Expected: session.chart_kind equals `bar`
   - Expected: session.last_error equals `kind-not-in-gui`
   - Expected: session.chart_kind equals `bar`
   - Expected: session.last_error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_kind with a chart.spl-known-but-GUI-unsupported kind leaves chart_kind unchanged and sets last_error")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
var session = chart_session_new(sheet, "bar", "B1:B1", "A1:A1", "Sales")
session = chart_session_set_kind(session, "line")
expect(session.chart_kind).to_equal("bar")
expect(session.last_error).to_equal("kind-not-in-gui")
session = chart_session_set_kind(session, "bar")
expect(session.chart_kind).to_equal("bar")
expect(session.last_error).to_equal("")
```

</details>

#### step key \

- step key \
   - Expected: step1.session.chart_kind equals `column`
   - Expected: step1.session.last_error equals ``
   - Expected: step2.session.chart_kind equals `pie`
   - Expected: step3.session.chart_kind equals `bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("step key \")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
val session = chart_session_new(sheet, "bar", "B1:B1", "A1:A1", "Sales")
val step1 = chart_gui_step(session, "k")
assert_false(step1.quit)
expect(step1.session.chart_kind).to_equal("column")
expect(step1.session.last_error).to_equal("")
val step2 = chart_gui_step(step1.session, "k")
expect(step2.session.chart_kind).to_equal("pie")
val step3 = chart_gui_step(step2.session, "k")
expect(step3.session.chart_kind).to_equal("bar")
```

</details>

#### step key \

- step key \
   - Expected: step.session.title equals `Sales*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("step key \")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
val session = chart_session_new(sheet, "bar", "B1:B1", "A1:A1", "Sales")
val step = chart_gui_step(session, "t")
assert_false(step.quit)
expect(step.session.title).to_equal("Sales*")
```

</details>

#### step key \

- step key \
   - Expected: step.session.chart_kind equals `bar`
   - Expected: step.session.value_range equals `B1:B1`
   - Expected: step.session.title equals `Sales`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("step key \")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Widget")
sheet.set_value("B1", "10")
val session = chart_session_new(sheet, "bar", "B1:B1", "A1:A1", "Sales")
val step = chart_gui_step(session, "q")
assert_true(step.quit)
expect(step.session.chart_kind).to_equal("bar")
expect(step.session.value_range).to_equal("B1:B1")
expect(step.session.title).to_equal("Sales")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `de1ccce1678599e6bbbbf2e6449bb587534137dd40076b4e176423edea87e23a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de1ccce1678599e6bbbbf2e6449bb587534137dd40076b4e176423edea87e23a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de1ccce1678599e6bbbbf2e6449bb587534137dd40076b4e176423edea87e23a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/chart_gui_view_spec.spl
mirror: doc/06_spec/01_unit/app/office/chart_gui_view_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/chart_gui_view_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/chart_gui_view_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/chart_gui_view_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the first line carries the chart kind and title' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/chart_gui_view_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'each data point line carries its label, value, and pct-of-max' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/chart_gui_view_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a formula cell's computed value appears, not the raw formula text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
