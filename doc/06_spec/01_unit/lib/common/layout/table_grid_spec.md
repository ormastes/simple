# CSS Table Grid Resolution

> Laying out a table means deciding how wide each column is, how tall each row

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Table Grid Resolution

Laying out a table means deciding how wide each column is, how tall each row

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib / Layout |
| Status | Implemented |
| Plan | doc/03_plan/ui/rendering/blink_wiring_plan.md (blocker 7) |
| Source | `test/01_unit/lib/common/layout/table_grid_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Laying out a table means deciding how wide each column is, how tall each row
is, and where every cell's rectangle therefore sits. This module does exactly
that and nothing else — it takes cells described by their grid position and
their measured content sizes and returns the resolved grid.

The audience is a table-layout driver: `blink/layout/table_flow.spl` today,
which measures the text and then asks this module where it goes.

## Scope and Preconditions

DOM-free. The caller has already walked its own tree and measured its own text;
sizes arrive as `min_width` (the widest unbreakable word) and `max_width` (the
whole content on one line) in `f64` CSS pixels.

## Primary Workflow

`resolve_table_grid` returns a `TableGrid` carrying column widths, row heights
and the origin of each column and row, from which `cell_x`, `cell_y`,
`cell_width` and `cell_height` give any cell's box.

## Key Concepts

| Concept | Description |
|---------|-------------|
| auto layout | Columns sized from content: preferred widths when they fit, otherwise minimums plus a share of the slack proportional to unmet demand |
| fixed layout | Columns divided equally — `table-layout: fixed`, and what the live lane does unconditionally |
| border-spacing | The separate-borders gap; `n` columns consume `(n + 1)` gaps |

## Compatibility and Limitations

Rowspan HEIGHT redistribution is not implemented — a tall spanning cell can
overflow its last row. No `border-collapse: collapse`, no percentage or
explicit column widths, no `<col>`, no caption, no vertical-align.

## Scenarios

### column_min_widths and column_max_widths

#### take the widest cell in each column

- take the widest cell in each column
- Build a two-column table and read off the intrinsic widths
   - Expected: mins[0] equals `10.0`
   - Expected: mins[1] equals `10.0`
   - Expected: maxs[0] equals `20.0`
   - Expected: maxs[1] equals `80.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("take the widest cell in each column")
step("Build a two-column table and read off the intrinsic widths")
val cells = two_cell_row()
val mins = column_min_widths(cells, 2)
val maxs = column_max_widths(cells, 2)
# One cell per column, so each column simply inherits its cell's sizes.
expect(mins[0]).to_equal(10.0)
expect(mins[1]).to_equal(10.0)
expect(maxs[0]).to_equal(20.0)
expect(maxs[1]).to_equal(80.0)
```

</details>

#### ignore column-spanning cells

- ignore column-spanning cells
- Add a cell spanning both columns with a huge minimum
   - Expected: mins[0] equals `10.0`
   - Expected: mins[1] equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignore column-spanning cells")
step("Add a cell spanning both columns with a huge minimum")
var cells = two_cell_row()
cells.push(table_cell_spanning(1, 0, 2, 1, 500.0, 500.0, 20.0))
val mins = column_min_widths(cells, 2)
# CSS 2.1 §17.5.2.2 gives spanning cells the lowest priority: they do
# not raise a single column's minimum, because there is no way to say
# WHICH column should grow. Their demand is resolved later, only if the
# columns they cross are together too narrow.
expect(mins[0]).to_equal(10.0)
expect(mins[1]).to_equal(10.0)
```

</details>

### resolve_table_grid with table-layout: auto

#### gives a wide column more space than a narrow one

- gives a wide column more space than a narrow one
- Resolve the two-cell row into 200px with no border-spacing
- And the two together still fill the table


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives a wide column more space than a narrow one")
step("Resolve the two-cell row into 200px with no border-spacing")
val g = resolve_table_grid(two_cell_row(), 2, 1, 200.0, 0.0, false)
# Preferred widths are 20 and 80, totalling 100, which fits in 200. So
# every column gets its preferred width and the 100px surplus is shared
# equally, 50 each: 20 + 50 = 70 and 80 + 50 = 130. The wide column
# stays wider, which is exactly what the live lane's equal division
# (100/100) gets wrong.
assert_true(approx_eq(g.col_widths[0], 70.0))
assert_true(approx_eq(g.col_widths[1], 130.0))
step("And the two together still fill the table")
assert_true(approx_eq(g.width, 200.0))
```

</details>

#### shares the slack by unmet demand when preferred widths do not fit

- shares the slack by unmet demand when preferred widths do not fit
- Resolve the same row into only 60px


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shares the slack by unmet demand when preferred widths do not fit")
step("Resolve the same row into only 60px")
val g = resolve_table_grid(two_cell_row(), 2, 1, 60.0, 0.0, false)
# Minimums total 20, preferred total 100, and 60 is between them. Each
# column starts at its minimum of 10, leaving 40 of slack. Column 0
# wants 20 - 10 = 10 more and column 1 wants 80 - 10 = 70 more, so the
# slack splits 10/80 and 70/80: column 0 gets 10 + 40*(10/80) = 15 and
# column 1 gets 10 + 40*(70/80) = 45.
assert_true(approx_eq(g.col_widths[0], 15.0))
assert_true(approx_eq(g.col_widths[1], 45.0))
```

</details>

#### falls back to the minimums and overflows when even those do not fit

- falls back to the minimums and overflows when even those do not fit
- Resolve the same row into 10px, below the 20px total minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to the minimums and overflows when even those do not fit")
step("Resolve the same row into 10px, below the 20px total minimum")
val g = resolve_table_grid(two_cell_row(), 2, 1, 10.0, 0.0, false)
# A column may not be squeezed below its longest unbreakable word, so
# both stay at 10 and the table is 20 wide inside a 10px slot. Silently
# shrinking them would clip text instead.
assert_true(approx_eq(g.col_widths[0], 10.0))
assert_true(approx_eq(g.col_widths[1], 10.0))
assert_true(approx_eq(g.width, 20.0))
```

</details>

#### widens the columns a spanning cell crosses when they are too narrow

- widens the columns a spanning cell crosses when they are too narrow
- Add a 2-column-spanning cell needing 300px to a 200px table


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("widens the columns a spanning cell crosses when they are too narrow")
step("Add a 2-column-spanning cell needing 300px to a 200px table")
var cells = two_cell_row()
cells.push(table_cell_spanning(1, 0, 2, 1, 300.0, 300.0, 20.0))
val g = resolve_table_grid(cells, 2, 2, 200.0, 0.0, false)
# Without the spanning cell the columns resolve to 70 and 130 (see
# above), totalling 200 — 100 short of the spanning cell's 300px
# minimum. The shortfall is shared equally, +50 each, giving 120 and
# 180, which together are exactly the 300 the spanning cell needs.
assert_true(approx_eq(g.col_widths[0], 120.0))
assert_true(approx_eq(g.col_widths[1], 180.0))
assert_true(approx_eq(g.cell_width(0, 2), 300.0))
```

</details>

### resolve_table_grid with table-layout: fixed

#### ignores content and splits the width evenly

- ignores content and splits the width evenly
- Resolve the two-cell row into 200px with fixed_layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores content and splits the width evenly")
step("Resolve the two-cell row into 200px with fixed_layout")
val g = resolve_table_grid(two_cell_row(), 2, 1, 200.0, 0.0, true)
# 200 / 2 = 100 each, regardless of the 20-vs-80 content. This IS the
# right answer for `table-layout: fixed` — the point of that value is
# that layout must not depend on content.
assert_true(approx_eq(g.col_widths[0], 100.0))
assert_true(approx_eq(g.col_widths[1], 100.0))
```

</details>

### row heights

#### take the tallest cell in the row

- take the tallest cell in the row
- Give row 0 cells 30px and 45px tall


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("take the tallest cell in the row")
step("Give row 0 cells 30px and 45px tall")
var cells: [TableCellSpec] = []
cells.push(table_cell(0, 0, 10.0, 20.0, 30.0))
cells.push(table_cell(0, 1, 10.0, 20.0, 45.0))
val g = resolve_table_grid(cells, 2, 1, 200.0, 0.0, false)
# A row is as tall as its tallest cell; the shorter one is stretched.
assert_true(approx_eq(g.row_heights[0], 45.0))
assert_true(approx_eq(g.height, 45.0))
```

</details>

### border-spacing

#### consumes a gap at each edge and between every pair of columns

- consumes a gap at each edge and between every pair of columns
- Resolve two columns into 200px with 5px border-spacing
- Column origins step past the gaps
- And the table's own width still comes to 200


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("consumes a gap at each edge and between every pair of columns")
step("Resolve two columns into 200px with 5px border-spacing")
val g = resolve_table_grid(two_cell_row(), 2, 1, 200.0, 5.0, true)
# Two columns take three gaps (outer, middle, outer) = 15px, leaving
# 185 for the columns: 92.5 each under fixed layout.
assert_true(approx_eq(g.col_widths[0], 92.5))
assert_true(approx_eq(g.col_widths[1], 92.5))
step("Column origins step past the gaps")
# Column 0 starts one gap in, at 5. Column 1 starts after column 0's
# 92.5 plus another 5: 5 + 92.5 + 5 = 102.5.
assert_true(approx_eq(g.cell_x(0), 5.0))
assert_true(approx_eq(g.cell_x(1), 102.5))
step("And the table's own width still comes to 200")
assert_true(approx_eq(g.width, 200.0))
```

</details>

### cell geometry accessors

#### give a spanning cell the two columns plus the gap between them

- give a spanning cell the two columns plus the gap between them
- Resolve two 92.5px columns with a 5px gap, then measure a 2-col span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("give a spanning cell the two columns plus the gap between them")
step("Resolve two 92.5px columns with a 5px gap, then measure a 2-col span")
val g = resolve_table_grid(two_cell_row(), 2, 1, 200.0, 5.0, true)
# 92.5 + 5 + 92.5 = 190: a spanning cell swallows the internal gap,
# which is why it is wider than the sum of the column widths alone.
assert_true(approx_eq(g.cell_width(0, 2), 190.0))
```

</details>

#### return zero for an out-of-range row or column

- return zero for an out-of-range row or column
- Ask for column 9 of a two-column table
   - Expected: g.cell_x(9) equals `0.0`
   - Expected: g.cell_y(9) equals `0.0`
   - Expected: g.cell_width(9, 1) equals `0.0`
   - Expected: g.cell_height(9, 1) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("return zero for an out-of-range row or column")
step("Ask for column 9 of a two-column table")
# Fail soft rather than reading past the array: a caller that gets its
# column count wrong sees a zero-sized cell, not a crash.
val g = resolve_table_grid(two_cell_row(), 2, 1, 200.0, 0.0, false)
expect(g.cell_x(9)).to_equal(0.0)
expect(g.cell_y(9)).to_equal(0.0)
expect(g.cell_width(9, 1)).to_equal(0.0)
expect(g.cell_height(9, 1)).to_equal(0.0)
```

</details>

### degenerate tables

#### resolve a table with no columns to a zero-width grid

- resolve a table with no columns to a zero-width grid
- Resolve zero columns and zero rows
   - Expected: g.col_widths.len() equals `0`
   - Expected: g.width equals `0.0`
   - Expected: g.height equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolve a table with no columns to a zero-width grid")
step("Resolve zero columns and zero rows")
var none: [TableCellSpec] = []
val g = resolve_table_grid(none, 0, 0, 200.0, 0.0, false)
expect(g.col_widths.len()).to_equal(0)
expect(g.width).to_equal(0.0)
expect(g.height).to_equal(0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9ae8f6dfee8fc39e39daaf00a7e27f385b79cceda30ca0f9fe239255dd7883bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ae8f6dfee8fc39e39daaf00a7e27f385b79cceda30ca0f9fe239255dd7883bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ae8f6dfee8fc39e39daaf00a7e27f385b79cceda30ca0f9fe239255dd7883bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/layout/table_grid_spec.spl
mirror: doc/06_spec/01_unit/lib/common/layout/table_grid_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/layout/table_grid_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/layout/table_grid_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/layout/table_grid_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/layout/table_grid_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/layout/table_grid_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'take the widest cell in each column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/layout/table_grid_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignore column-spanning cells' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/layout/table_grid_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives a wide column more space than a narrow one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
