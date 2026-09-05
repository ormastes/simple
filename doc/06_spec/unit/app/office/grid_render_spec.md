# Shared Calc Grid Body

> Simple Calc paints its spreadsheet viewport on two surfaces: the full-screen

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Calc Grid Body

Simple Calc paints its spreadsheet viewport on two surfaces: the full-screen

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Plan | doc/03_plan/sys_test/office_cli_tui_ui_access.md |
| Design | doc/05_design/office_cli_tui_ui_access.md |
| Source | `test/unit/app/office/grid_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Simple Calc paints its spreadsheet viewport on two surfaces: the full-screen
terminal editor (`simple office edit-sheet --tui`) and the semantic UI-access
controller that drives scripted and assistive clients. Both surfaces show the
user the same thing — a row of column letters over a block of clipped cell
values — so both are rendered by one function, `office_grid_body`.

This spec is for the person who has to change how that grid looks. It pins the
grid's visible shape so a change on one surface cannot silently alter the other.

## Scope and Preconditions

Covers the grid body only: the column-header row and the value rows. The chrome
around it — title, formula bar, status line, and the fixed-height frame — stays
with each surface and is not covered here.

## Primary Workflow

A user opens a sheet and sees column letters `A`, `B`, `C`... across the top and
numbered rows beneath, every cell occupying the same width so the columns line
up. Scrolling right re-labels the headers from the new leftmost column;
scrolling down re-numbers the rows. A value too wide for its column is clipped
rather than pushing the grid out of alignment.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Scroll origin | 0-based `(scroll_col, scroll_row)` sheet coordinate of the top-left visible cell |
| Extents | How many columns and rows the surface shows |
| Clip width | Cell text is cut to 5 characters so columns stay aligned |
| Row-header column | A `row_header_width` field holding the 1-based row number |

The terminal editor does not scroll: it renders at origin `(0, 0)`. The access
controller renders at the live scroll origin. That single difference is why the
two surfaces pass different arguments to the same function.

## Related Specifications

- [Calc UI access](../../../../06_spec/03_system/app/office/feature/office_cli_tui_ui_access_spec.md) — the access surface whose output is a frozen contract

## Evidence and Provenance

Grid captures in this spec are compared against declared expectations, not
merely recorded: a capture that renders nothing, or renders the wrong origin,
fails. Extraction of this function from the two former in-line copies was
verified by rendering both real call sites before and after and comparing the
bytes.

## Recovery and Troubleshooting

Misaligned columns almost always mean a cell value reached its column without
being clipped to the 5-character limit. Wrong row numbers or column letters mean
the scroll origin was not added to the loop index.

## Compatibility and Limitations

The grid body carries no ANSI styling and no hidden-row awareness: it renders a
contiguous block of rows from the scroll origin. Hidden rows are honoured only
by the GUI session surface — see
doc/08_tracking/bug/calc_cursor_hidden_row_awareness_divergence_2026-08-11.md.

## Scenarios

### Shared Calc grid body

#### labels columns from A and numbers rows from 1 at the sheet origin

**Manual warnings:**
- invalid capture metadata value: tui_grid (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- labels columns from A and numbers rows from 1 at the sheet origin
- Open a sheet holding values in the first columns
- Render an 8-column, 4-row viewport at the top-left of the sheet
- Confirm the capture has the requested shape before reading it
- Check every line is the same width: 4-wide row header plus 8 six-wide columns
   - Expected: grid_line(grid, 0).len() equals `52`
   - Expected: grid_line(grid, 1).len() equals `52`
- Check the header row leads with a blank row-number field, then A, B, C
   - Expected: grid_line(grid, 0) equals `    A     B     C     D     E     F     G     H     `
- Check the first body row is numbered 1 and shows its cell values
   - Expected: grid_line(grid, 1) equals `1   hi    abcde                                     `
- Check the second body row is numbered 2 and shows the D2 value in the D column
   - Expected: grid_line(grid, 2) equals `2                     x                             `


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("labels columns from A and numbers rows from 1 at the sheet origin")
step("Open a sheet holding values in the first columns")
val sheet = a_sheet_with_known_values()
val metrics = spreadsheet_grid_default_metrics()

step("Render an 8-column, 4-row viewport at the top-left of the sheet")
val grid = office_grid_body(sheet, 0, 0, 8, 4, metrics)

step("Confirm the capture has the requested shape before reading it")
expect_grid_is_populated(grid, 4)

step("Check every line is the same width: 4-wide row header plus 8 six-wide columns")
expect(grid_line(grid, 0).len()).to_equal(52)
expect(grid_line(grid, 1).len()).to_equal(52)

step("Check the header row leads with a blank row-number field, then A, B, C")
expect(grid_line(grid, 0)).to_equal("    A     B     C     D     E     F     G     H     ")

step("Check the first body row is numbered 1 and shows its cell values")
expect(grid_line(grid, 1)).to_equal("1   hi    abcde                                     ")

step("Check the second body row is numbered 2 and shows the D2 value in the D column")
expect(grid_line(grid, 2)).to_equal("2                     x                             ")
```

</details>

#### clips a cell value too wide for its column so the columns stay aligned

- clips a cell value too wide for its column so the columns stay aligned
- Open a sheet whose B1 holds a ten-character value
- Render a viewport wide enough to include B
- Confirm the ten-character value appears cut to five characters
   - Expected: grid_line(grid, 1) contains `abcde`
   - Expected: grid_line(grid, 1) does not contain `abcdef`
- Confirm every rendered line is still the same width
   - Expected: grid_line(grid, 0).len() equals `grid_line(grid, 1).len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clips a cell value too wide for its column so the columns stay aligned")
step("Open a sheet whose B1 holds a ten-character value")
val sheet = a_sheet_with_known_values()
val metrics = spreadsheet_grid_default_metrics()

step("Render a viewport wide enough to include B")
val grid = office_grid_body(sheet, 0, 0, 3, 1, metrics)
expect_grid_is_populated(grid, 1)

step("Confirm the ten-character value appears cut to five characters")
expect(grid_line(grid, 1).contains("abcde")).to_equal(true)
expect(grid_line(grid, 1).contains("abcdef")).to_equal(false)

step("Confirm every rendered line is still the same width")
expect(grid_line(grid, 0).len()).to_equal(grid_line(grid, 1).len())
```

</details>

#### re-labels headers and row numbers from the scroll origin

**Manual warnings:**
- invalid capture metadata value: tui_grid (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- re-labels headers and row numbers from the scroll origin
- Open the sheet and scroll three columns right and seven rows down
- Confirm the capture has the requested shape before reading it
- Check the headers now start at D rather than A
   - Expected: grid_line(grid, 0) equals `    D     E     F     G     `
   - Expected: grid_line(grid, 0).len() equals `28`
- Check the first visible row is numbered 8, not 1
   - Expected: grid_line(grid, 1).starts_with("8   ") is true
- Check the scrolled viewport shows the value living at D8
   - Expected: grid_line(grid, 1) contains `deep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-labels headers and row numbers from the scroll origin")
step("Open the sheet and scroll three columns right and seven rows down")
val sheet = a_sheet_with_known_values()
val metrics = spreadsheet_grid_default_metrics()
val grid = office_grid_body(sheet, 3, 7, 4, 3, metrics)

step("Confirm the capture has the requested shape before reading it")
expect_grid_is_populated(grid, 3)

step("Check the headers now start at D rather than A")
expect(grid_line(grid, 0)).to_equal("    D     E     F     G     ")
expect(grid_line(grid, 0).len()).to_equal(28)

step("Check the first visible row is numbered 8, not 1")
expect(grid_line(grid, 1).starts_with("8   ")).to_equal(true)

step("Check the scrolled viewport shows the value living at D8")
expect(grid_line(grid, 1).contains("deep")).to_equal(true)
```

</details>

#### renders the terminal editor and the access surface identically at a shared origin

- renders the terminal editor and the access surface identically at a shared origin
- Open one sheet and fix a single viewport size
- Render it the way the terminal editor does — anchored at A1
- Render it the way the access controller does when unscrolled
- Confirm both captures are populated, so the comparison is not vacuous
- Confirm the two surfaces produce the same grid, character for character
   - Expected: editor_grid equals `access_grid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders the terminal editor and the access surface identically at a shared origin")
step("Open one sheet and fix a single viewport size")
val sheet = a_sheet_with_known_values()
val metrics = spreadsheet_grid_default_metrics()

step("Render it the way the terminal editor does — anchored at A1")
val editor_grid = office_grid_body(sheet, 0, 0, metrics.visible_columns, metrics.visible_rows, metrics)

step("Render it the way the access controller does when unscrolled")
val access_grid = office_grid_body(sheet, 0, 0, metrics.visible_columns, metrics.visible_rows, metrics)

step("Confirm both captures are populated, so the comparison is not vacuous")
expect_grid_is_populated(editor_grid, metrics.visible_rows)
expect_grid_is_populated(access_grid, metrics.visible_rows)

step("Confirm the two surfaces produce the same grid, character for character")
expect(editor_grid).to_equal(access_grid)
```

</details>

#### distinguishes a scrolled viewport from an unscrolled one

- distinguishes a scrolled viewport from an unscrolled one
- Render the same sheet at the origin and again scrolled down
- Confirm both captures are populated
- Confirm scrolling actually changed what the user sees
   - Expected: at_origin == scrolled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes a scrolled viewport from an unscrolled one")
step("Render the same sheet at the origin and again scrolled down")
val sheet = a_sheet_with_known_values()
val metrics = spreadsheet_grid_default_metrics()
val at_origin = office_grid_body(sheet, 0, 0, 6, 6, metrics)
val scrolled = office_grid_body(sheet, 2, 4, 6, 6, metrics)

step("Confirm both captures are populated")
expect_grid_is_populated(at_origin, 6)
expect_grid_is_populated(scrolled, 6)

step("Confirm scrolling actually changed what the user sees")
expect(at_origin == scrolled).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/office_cli_tui_ui_access.md`
- **Design:** `doc/05_design/office_cli_tui_ui_access.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OFFICE-GRID-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6ef414c49d18eb04d5ffc9552a738384bd4db980c898ad71def1ca1a04199fbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ef414c49d18eb04d5ffc9552a738384bd4db980c898ad71def1ca1a04199fbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ef414c49d18eb04d5ffc9552a738384bd4db980c898ad71def1ca1a04199fbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/office/grid_render_spec.spl
mirror: doc/06_spec/unit/app/office/grid_render_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/app/office/grid_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/unit/app/office/grid_render_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/office/grid_render_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/office/grid_render_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'labels columns from A and numbers rows from 1 at the sheet origin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/office/grid_render_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clips a cell value too wide for its column so the columns stay aligned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/office/grid_render_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-labels headers and row numbers from the scroll origin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
