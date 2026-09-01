# fill_series_edge_spec

> Office sheets fill-series edge-case spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fill_series_edge_spec

Office sheets fill-series edge-case spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/fill_series_edge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets fill-series edge-case spec.

Backward fills, zero-padded labels, negative and fractional steps, mixed or
empty seeds, and every shape of malformed fill request.

## Scenarios

### sheet_fill_series: backward fills

#### extends a numeric series upward

- extends a numeric series upward


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extends a numeric series upward")
var sheet = Sheet.new("B1")
sheet.set_value("A5", "10")
sheet.set_value("A6", "12")

val written = sheet_fill_series(sheet, "A5:A6", "A3:A4")

assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("A4")) == "8")
assert_true(cell_display_text(sheet.get_cell("A3")) == "6")
```

</details>

#### extends a month cycle leftward across the list start

- extends a month cycle leftward across the list start


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extends a month cycle leftward across the list start")
var sheet = Sheet.new("B2")
sheet.set_value("C1", "Feb")

val written = sheet_fill_series(sheet, "C1:C1", "A1:B1")

assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("B1")) == "Jan")
assert_true(cell_display_text(sheet.get_cell("A1")) == "Dec")
```

</details>

#### reverses a copy fill so the nearest cell repeats the last seed

- reverses a copy fill so the nearest cell repeats the last seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses a copy fill so the nearest cell repeats the last seed")
var sheet = Sheet.new("B3")
sheet.set_value("A4", "red")
sheet.set_value("A5", "blue")

val written = sheet_fill_series(sheet, "A4:A5", "A2:A3")

assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("A3")) == "blue")
assert_true(cell_display_text(sheet.get_cell("A2")) == "red")
```

</details>

### fill_series_cells: numeric edges
_Negative and fractional steps stay linear._

#### handles a descending series through zero

- handles a descending series through zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a descending series through zero")
var seed: [Cell] = [number_cell(2.0), number_cell(1.0)]
val out = fill_series_cells(seed, 3)
assert_true(cell_display_text(out[0]) == "0")
assert_true(cell_display_text(out[1]) == "-1")
assert_true(cell_display_text(out[2]) == "-2")
```

</details>

#### handles a fractional step

- handles a fractional step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a fractional step")
var seed: [Cell] = [number_cell(1.0), number_cell(1.5)]
val out = fill_series_cells(seed, 2)
assert_true(cell_display_text(out[0]) == "2")
assert_true(cell_display_text(out[1]) == "2.5")
```

</details>

### fill_series_cells: label edges
_Zero padding is preserved; non-numbered and mixed seeds copy._

#### preserves zero padding

- preserves zero padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves zero padding")
var seed: [Cell] = [text_cell("Q007")]
val out = fill_series_cells(seed, 2)
assert_true(cell_display_text(out[0]) == "Q008")
assert_true(cell_display_text(out[1]) == "Q009")
```

</details>

#### keeps a bare number label as a numbered fill with an empty prefix

- keeps a bare number label as a numbered fill with an empty prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a bare number label as a numbered fill with an empty prefix")
var seed: [Cell] = [text_cell("41")]
val out = fill_series_cells(seed, 1)
assert_true(cell_display_text(out[0]) == "42")
```

</details>

#### copies labels whose prefixes differ

- copies labels whose prefixes differ


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies labels whose prefixes differ")
var seed: [Cell] = [text_cell("A1"), text_cell("B2")]
val out = fill_series_cells(seed, 2)
assert_true(cell_display_text(out[0]) == "A1")
assert_true(cell_display_text(out[1]) == "B2")
```

</details>

#### copies a seed mixing numbers and text

- copies a seed mixing numbers and text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies a seed mixing numbers and text")
var seed: [Cell] = [number_cell(1.0), text_cell("x")]
val out = fill_series_cells(seed, 2)
assert_true(cell_display_text(out[0]) == "1")
assert_true(cell_display_text(out[1]) == "x")
```

</details>

#### returns nothing for an empty seed

- returns nothing for an empty seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nothing for an empty seed")
var seed: [Cell] = []
assert_true(fill_series_cells(seed, 3).len() == 3)
```

</details>

### sheet_fill_series: rejected requests
_Malformed or ambiguous fills write nothing and report 0._

#### rejects an unparseable range

- rejects an unparseable range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unparseable range")
var sheet = Sheet.new("R1")
sheet.set_value("A1", "1")
assert_true(sheet_fill_series(sheet, "A1:A2", "not-a-range") == 0)
```

</details>

#### rejects a target in a different column

- rejects a target in a different column


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a target in a different column")
var sheet = Sheet.new("R2")
sheet.set_value("A1", "1")
sheet.set_value("A2", "2")
assert_true(sheet_fill_series(sheet, "A1:A2", "B3:B4") == 0)
assert_true(cell_display_text(sheet.get_cell("B3")) == "")
```

</details>

#### rejects a target overlapping the seed

- rejects a target overlapping the seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a target overlapping the seed")
var sheet = Sheet.new("R3")
sheet.set_value("A1", "1")
sheet.set_value("A2", "2")
assert_true(sheet_fill_series(sheet, "A1:A2", "A2:A4") == 0)
```

</details>

#### rejects a rectangular target

- rejects a rectangular target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a rectangular target")
var sheet = Sheet.new("R4")
sheet.set_value("A1", "1")
assert_true(sheet_fill_series(sheet, "A1:A1", "B2:C3") == 0)
```

</details>

#### fills empty seed cells as an empty copy

- fills empty seed cells as an empty copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fills empty seed cells as an empty copy")
var sheet = Sheet.new("R5")
val written = sheet_fill_series(sheet, "A1:A1", "A2:A3")
assert_true(written == 2)
assert_true(cell_display_text(sheet.get_cell("A2")) == "")
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

- Canonical SPipe generation for source `b20ab611b2ce5de122b312190934008047a65d87be8199d05f220743edf4e9b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b20ab611b2ce5de122b312190934008047a65d87be8199d05f220743edf4e9b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b20ab611b2ce5de122b312190934008047a65d87be8199d05f220743edf4e9b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/fill_series_edge_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/fill_series_edge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/fill_series_edge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/fill_series_edge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/fill_series_edge_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extends a numeric series upward' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/fill_series_edge_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extends a month cycle leftward across the list start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/fill_series_edge_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reverses a copy fill so the nearest cell repeats the last seed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
