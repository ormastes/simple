# sheet_gui_view_spec

> Sheet GUI grid view spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheet_gui_view_spec

Sheet GUI grid view spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheet_gui_view_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Sheet GUI grid view spec.

sheet_gui_view(sheet, max_rows, max_cols) builds the first real spreadsheet
UI surface: a WidgetNode table (rendered for real pixels by the CLI) plus a
plain-text pipe-separated grid dump (for testability without parsing
HTML/widget trees). The dump's first line is the header row ("|A|B|C|...");
each following line is "{row_num}|{cell1}|{cell2}|...". Rows in
sheet.hidden_rows are skipped entirely, so a filtered sheet renders
filtered.

## Scenarios

### sheet_gui_view: column headers and row numbers

#### the header line lists column letters A, B, C in order

- the header line lists column letters A, B, C in order
   - Expected: lines[0] equals `|A|B|C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the header line lists column letters A, B, C in order")
var sheet = Sheet.new("S1")
val view = sheet_gui_view(sheet, 2, 3)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("|A|B|C")
```

</details>

#### each data row starts with its 1-based row number

- each data row starts with its 1-based row number
   - Expected: lines[1] equals `1|x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("each data row starts with its 1-based row number")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "x")
val view = sheet_gui_view(sheet, 1, 1)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("1|x")
```

</details>

### sheet_gui_view: cell display text
_Non-formula cell values show up verbatim in the grid dump._

#### contains a plain text cell's value

- contains a plain text cell's value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("contains a plain text cell's value")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "Hello")
val view = sheet_gui_view(sheet, 1, 1)
expect(view.text_dump).to_contain("Hello")
```

</details>

#### contains a numeric cell's display value

- contains a numeric cell's display value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("contains a numeric cell's display value")
var sheet = Sheet.new("S1")
sheet.set_value("B2", "42")
val view = sheet_gui_view(sheet, 2, 2)
expect(view.text_dump).to_contain("42")
```

</details>

### sheet_gui_view: formula cells show computed values

#### shows the computed SUM result, not the raw formula text

- shows the computed SUM result, not the raw formula text


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("shows the computed SUM result, not the raw formula text")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "3")
sheet.set_value("A2", "4")
sheet.set_value("A3", "=SUM(A1:A2)")
sheet = recalculate_formula_cells(sheet)
val view = sheet_gui_view(sheet, 3, 1)
expect(view.text_dump).to_contain("7")
assert_false(_dump_contains(view.text_dump, "=SUM(A1:A2)"))
```

</details>

### sheet_gui_view: hidden rows are skipped

#### a hidden row's line is absent from the dump

- a hidden row's line is absent from the dump
   - Expected: found_hidden is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a hidden row's line is absent from the dump")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "keep-1")
sheet.set_value("A2", "hide-me")
sheet.set_value("A3", "keep-3")
sheet.hide_row(2)
val view = sheet_gui_view(sheet, 3, 1)
val lines = view.text_dump.split("\n")
var found_hidden = false
for line in lines:
    if line == "2|hide-me":
        found_hidden = true
expect(found_hidden).to_equal(false)
expect(view.text_dump).to_contain("keep-1")
expect(view.text_dump).to_contain("keep-3")
```

</details>

#### surrounding visible rows still render when a middle row is hidden

- surrounding visible rows still render when a middle row is hidden
   - Expected: lines[1] equals `1|keep-1`
   - Expected: lines[2] equals `3|keep-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("surrounding visible rows still render when a middle row is hidden")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "keep-1")
sheet.set_value("A2", "hide-me")
sheet.set_value("A3", "keep-3")
sheet.hide_row(2)
val view = sheet_gui_view(sheet, 3, 1)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("1|keep-1")
expect(lines[2]).to_equal("3|keep-3")
```

</details>

### sheet_gui_view: empty sheet

#### renders headers only when max_rows is 0

- renders headers only when max_rows is 0
   - Expected: view.text_dump equals `|A|B|C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders headers only when max_rows is 0")
var sheet = Sheet.new("Empty")
val view = sheet_gui_view(sheet, 0, 3)
expect(view.text_dump).to_equal("|A|B|C")
```

</details>

#### an empty sheet's requested rows still render (blank cells, no crash)

- an empty sheet's requested rows still render (blank cells, no crash)
   - Expected: lines.len() equals `3`
   - Expected: lines[1] equals `1||`
   - Expected: lines[2] equals `2||`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("an empty sheet's requested rows still render (blank cells, no crash)")
var sheet = Sheet.new("Empty")
val view = sheet_gui_view(sheet, 2, 2)
val lines = view.text_dump.split("\n")
expect(lines.len()).to_equal(3)
expect(lines[1]).to_equal("1||")
expect(lines[2]).to_equal("2||")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ce15af3afad2de66d78c871ff97adf787e65616fd590160c5b5b4a8ea09f367`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ce15af3afad2de66d78c871ff97adf787e65616fd590160c5b5b4a8ea09f367`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ce15af3afad2de66d78c871ff97adf787e65616fd590160c5b5b4a8ea09f367`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/office/sheet_gui_view_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheet_gui_view_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheet_gui_view_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheet_gui_view_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheet_gui_view_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/sheet_gui_view_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the header line lists column letters A, B, C in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheet_gui_view_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'each data row starts with its 1-based row number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheet_gui_view_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains a plain text cell's value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
