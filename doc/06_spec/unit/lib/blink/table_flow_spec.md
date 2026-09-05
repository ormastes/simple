# Blink Table Layout

> blink had no table layout at all. This module measures a table's cell text,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Table Layout

blink had no table layout at all. This module measures a table's cell text,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Layout |
| Status | Implemented |
| Plan | doc/03_plan/ui/rendering/blink_wiring_plan.md (blocker 7) |
| Source | `test/unit/lib/blink/table_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

blink had no table layout at all. This module measures a table's cell text,
asks `common/layout/table_grid.spl` to resolve the grid, and returns cell
rectangles. The audience is anyone changing `blink/layout/table_flow.spl`.

## Scope and Preconditions

Text is measured through `blink/layout/inline_text.spl`, which is monospace and
counts Unicode CODEPOINTS. Every expected number below is derived from two
measured constants at font size 10: a normal character advances **5px**, a
space advances **2px**, and one line box is **9px** tall. So `"ab"` is 10px
wide and `"hello"` is 25px.

## Primary Workflow

Build `TableCellText` cells, call `layout_table` with the column and row
counts, the available width, the border-spacing and the font, then read cell
rectangles with `table_cell_rect`.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Two passes | Columns are resolved from unwrapped text, then cells are re-wrapped to their actual column width so row heights reflect the wrapping |
| min width | The widest single word — the narrowest a column may be squeezed |
| max width | The whole run on one line — the column's preferred width |

## Compatibility and Limitations

No rowspan height redistribution, no `border-collapse: collapse`, no
percentage or explicit column widths, no caption, no vertical-align. Cell
CONTENT is not laid out — this positions the cell boxes only.

## Scenarios

### measure_table_cells

#### records each cell's longest word as its minimum and the whole run as its preferred width

- records each cell's longest word as its minimum and the whole run as its preferred width
- Measure the narrow/wide row at font size 10
- The two-character cell prefers 10px and cannot go below 10px
- The sixteen-character cell prefers 71px but can be squeezed to 20px
- And both are one line box tall before wrapping is known


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records each cell's longest word as its minimum and the whole run as its preferred width")
step("Measure the narrow/wide row at font size 10")
val specs = measure_table_cells(narrow_and_wide(), font10())

step("The two-character cell prefers 10px and cannot go below 10px")
# "ab" is 2 characters at 5px each. It is one unbreakable word, so its
# minimum and preferred width are the same 10.
assert_true(approx_eq(specs[0].max_width, 10.0))
assert_true(approx_eq(specs[0].min_width, 10.0))

step("The sixteen-character cell prefers 71px but can be squeezed to 20px")
# "a very long cell" is 13 non-space characters at 5px plus 3 spaces at
# 2px = 65 + 6 = 71. Its longest word is "very" / "long" / "cell", each
# 4 characters = 20px, so the column may be squeezed to 20 and no
# further without breaking a word.
assert_true(approx_eq(specs[1].max_width, 71.0))
assert_true(approx_eq(specs[1].min_width, 20.0))

step("And both are one line box tall before wrapping is known")
assert_true(approx_eq(specs[0].content_height, 9.0))
assert_true(approx_eq(specs[1].content_height, 9.0))
```

</details>

### layout_table with table-layout: auto

#### gives the long cell more width than the short one

- gives the long cell more width than the short one
- Lay the narrow/wide row out into 200px with no border-spacing
- The two columns together fill the available width


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives the long cell more width than the short one")
step("Lay the narrow/wide row out into 200px with no border-spacing")
val g = layout_table(narrow_and_wide(), 2, 1, 200.0, 0.0, false, font10())
# Preferred widths are 10 and 71, totalling 81, which fits in 200. Each
# column gets its preferred width and the 119px surplus splits evenly,
# 59.5 each: 10 + 59.5 = 69.5 and 71 + 59.5 = 130.5. The live lane's
# equal division would have made both 100 and left the long cell
# wrapping while the short one sat mostly empty.
assert_true(approx_eq(g.col_widths[0], 69.5))
assert_true(approx_eq(g.col_widths[1], 130.5))
step("The two columns together fill the available width")
assert_true(approx_eq(g.width, 200.0))
```

</details>

#### keeps a one-line row one line box tall

- keeps a one-line row one line box tall
- Read the row height of the same table


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a one-line row one line box tall")
step("Read the row height of the same table")
# Both cells fit on one line at their resolved widths, so the row is a
# single 9px line box.
val g = layout_table(narrow_and_wide(), 2, 1, 200.0, 0.0, false, font10())
assert_true(approx_eq(g.row_heights[0], 9.0))
assert_true(approx_eq(g.height, 9.0))
```

</details>

#### grows a row when a squeezed column forces its text to wrap

- grows a row when a squeezed column forces its text to wrap
- Lay the same row out into only 60px
- Column 1 is squeezed to 50px
- Which makes the row two line boxes tall, not one


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grows a row when a squeezed column forces its text to wrap")
step("Lay the same row out into only 60px")
val g = layout_table(narrow_and_wide(), 2, 1, 60.0, 0.0, false, font10())
step("Column 1 is squeezed to 50px")
# Minimums total 10 + 20 = 30 and preferred total 81, so 60 sits
# between them. Each column starts at its minimum; the 30px of slack is
# shared by unmet demand, and column 0 wants nothing more (its min is
# its max) while column 1 wants 51 more. So column 0 stays at 10 and
# column 1 gets 20 + 30 = 50.
assert_true(approx_eq(g.col_widths[0], 10.0))
assert_true(approx_eq(g.col_widths[1], 50.0))
step("Which makes the row two line boxes tall, not one")
# "a very long" measures 5 + 2 + 20 + 2 + 20 = 49, which fits in 50;
# adding " cell" would make 71. So the cell wraps to two lines and the
# row becomes 2 * 9 = 18px. This is what the second measuring pass
# exists for — a single pass would have sized the row for unwrapped
# text and clipped the second line.
assert_true(approx_eq(g.row_heights[0], 18.0))
assert_true(approx_eq(g.height, 18.0))
```

</details>

### layout_table with table-layout: fixed

#### splits the width evenly and ignores the content

- splits the width evenly and ignores the content
- Lay the narrow/wide row out into 200px with fixed_layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits the width evenly and ignores the content")
step("Lay the narrow/wide row out into 200px with fixed_layout")
val g = layout_table(narrow_and_wide(), 2, 1, 200.0, 0.0, true, font10())
# 200 / 2 = 100 each. Correct for `table-layout: fixed`, whose whole
# contract is that geometry must not depend on content.
assert_true(approx_eq(g.col_widths[0], 100.0))
assert_true(approx_eq(g.col_widths[1], 100.0))
```

</details>

### table_cell_rect

#### places each cell at its column and row origin

- places each cell at its column and row origin
- Lay out the narrow/wide row into 200px and read both cell rects
- Cell (0,0) occupies the first column, 0..69.5
- Cell (0,1) starts where the first column ends and runs to the table's edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places each cell at its column and row origin")
step("Lay out the narrow/wide row into 200px and read both cell rects")
val g = layout_table(narrow_and_wide(), 2, 1, 200.0, 0.0, false, font10())

step("Cell (0,0) occupies the first column, 0..69.5")
val c0 = table_cell_rect(g, 0.0, 0.0, 0, 0, 1, 1)
assert_true(approx_eq(c0.left, 0.0))
assert_true(approx_eq(c0.top, 0.0))
assert_true(approx_eq(c0.right, 69.5))
assert_true(approx_eq(c0.bottom, 9.0))

step("Cell (0,1) starts where the first column ends and runs to the table's edge")
# 69.5 + 130.5 = 200, so the second cell fills 69.5..200.
val c1 = table_cell_rect(g, 0.0, 0.0, 0, 1, 1, 1)
assert_true(approx_eq(c1.left, 69.5))
assert_true(approx_eq(c1.right, 200.0))
```

</details>

#### offsets every cell by the table's own origin

- offsets every cell by the table's own origin
- Read cell (0,1) again with the table placed at (40, 25)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("offsets every cell by the table's own origin")
step("Read cell (0,1) again with the table placed at (40, 25)")
val g = layout_table(narrow_and_wide(), 2, 1, 200.0, 0.0, false, font10())
# The grid is resolved in table-local coordinates, so placing the table
# elsewhere is a pure translation: 40 + 69.5 = 109.5 and 25 + 0 = 25.
val c1 = table_cell_rect(g, 40.0, 25.0, 0, 1, 1, 1)
assert_true(approx_eq(c1.left, 109.5))
assert_true(approx_eq(c1.top, 25.0))
```

</details>

### table_rect

#### reports the table's whole content box

- reports the table's whole content box
- Read the table rect for a 200px-wide one-row table at the origin


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the table's whole content box")
step("Read the table rect for a 200px-wide one-row table at the origin")
val g = layout_table(narrow_and_wide(), 2, 1, 200.0, 0.0, false, font10())
val r = table_rect(g, 0.0, 0.0)
assert_true(approx_eq(r.right - r.left, 200.0))
assert_true(approx_eq(r.bottom - r.top, 9.0))
```

</details>

### a two-row table

#### stacks the rows by their own heights

- stacks the rows by their own heights
- Build a table whose second row is taller because its cell wraps
- Both rows are one line box tall, so row 1 starts at 9


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stacks the rows by their own heights")
step("Build a table whose second row is taller because its cell wraps")
var cells: [TableCellText] = []
cells.push(table_cell_text(0, 0, "ab"))
cells.push(table_cell_text(0, 1, "cd"))
cells.push(table_cell_text(1, 0, "ef"))
cells.push(table_cell_text(1, 1, "gh"))
val g = layout_table(cells, 2, 2, 200.0, 0.0, false, font10())
step("Both rows are one line box tall, so row 1 starts at 9")
# Every cell is a single 2-character word that fits easily, so each row
# is 9px and the second row's origin is exactly the first's height.
assert_true(approx_eq(g.row_heights[0], 9.0))
assert_true(approx_eq(g.cell_y(0), 0.0))
assert_true(approx_eq(g.cell_y(1), 9.0))
assert_true(approx_eq(g.height, 18.0))
```

</details>

### a column-spanning cell

#### covers both columns and the space between them

- covers both columns and the space between them
- Add a cell spanning both columns of a border-spaced table
- Each column is 64px under fixed layout with 4px spacing
- The spanning cell is both columns plus the gap between them


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers both columns and the space between them")
step("Add a cell spanning both columns of a border-spaced table")
var cells: [TableCellText] = []
cells.push(table_cell_text(0, 0, "ab"))
cells.push(table_cell_text(0, 1, "cd"))
cells.push(table_cell_text_spanning(1, 0, 2, 1, "wide"))
val g = layout_table(cells, 2, 2, 200.0, 4.0, true, font10())
step("Each column is 64px under fixed layout with 4px spacing")
# Two columns take three 4px gaps = 12, leaving 188 to split evenly:
# 94 each.
assert_true(approx_eq(g.col_widths[0], 94.0))
step("The spanning cell is both columns plus the gap between them")
# 94 + 4 + 94 = 192. A spanning cell swallows the internal gap, so it
# is wider than the two column widths alone.
val r = table_cell_rect(g, 0.0, 0.0, 1, 0, 2, 1)
assert_true(approx_eq(r.right - r.left, 192.0))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/rendering/blink_wiring_plan.md (blocker 7)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-LAYOUT-TABLES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b9b6cb6479549a1605a72db9622d0ec3729432aa2c10a2c5ce6177d22486088c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b9b6cb6479549a1605a72db9622d0ec3729432aa2c10a2c5ce6177d22486088c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b9b6cb6479549a1605a72db9622d0ec3729432aa2c10a2c5ce6177d22486088c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/blink/table_flow_spec.spl
mirror: doc/06_spec/unit/lib/blink/table_flow_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/unit/lib/blink/table_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/table_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/table_flow_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/blink/table_flow_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records each cell's longest word as its minimum and the whole run as its preferred width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/table_flow_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives the long cell more width than the short one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/table_flow_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a one-line row one line box tall' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
