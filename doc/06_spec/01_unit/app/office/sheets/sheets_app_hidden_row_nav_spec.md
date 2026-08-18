# sheets_app_hidden_row_nav_spec

> SheetsApp.navigate_to hidden-row awareness spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheets_app_hidden_row_nav_spec

SheetsApp.navigate_to hidden-row awareness spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/sheets_app_hidden_row_nav_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

SheetsApp.navigate_to hidden-row awareness spec.

Regression for the third cursor-movement path in
doc/08_tracking/bug/calc_cursor_hidden_row_awareness_divergence_2026-08-11.md.
The GUI session (_sheet_gui_move_within_bounds) and the TUI (_tui_move) both
skip hidden rows; SheetsApp.navigate_to -- the widget-app arrow/Tab handler --
clamped to >= 0 and nothing else, so it parked the active cell ON a hidden row.

Semantics asserted here are exactly the other two paths': step in the SAME
direction of travel until a visible row is found; if the grid edge is reached
first, stay on the row the cursor came from (no wrap). Vertical direction is
inferred from the delta against the current active cell, so a pure-horizontal
move (Tab, ArrowLeft/Right) never touches the row.

Note the index base: hidden_rows / is_row_hidden are 1-BASED, CellRef.row is
0-BASED, so row index r corresponds to is_row_hidden(r + 1).

## Scenarios

### SheetsApp.navigate_to: hidden-row awareness

#### downward move skips a hidden row instead of landing on it

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = _app_with_hidden([2])
# cursor starts at row index 0 (1-based row 1); ArrowDown targets index
# 1 (1-based row 2) which is hidden -> must continue to index 2.
app.navigate_to(0, 1)
expect(app.active_cell.row).to_equal(2)
```

</details>

#### upward move skips a hidden row instead of landing on it

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = _app_with_hidden([2])
app.navigate_to(0, 2)
expect(app.active_cell.row).to_equal(2)
app.navigate_to(0, 1)
expect(app.active_cell.row).to_equal(0)
```

</details>

#### skips a run of consecutive hidden rows in one move

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = _app_with_hidden([2, 3, 4])
app.navigate_to(0, 1)
expect(app.active_cell.row).to_equal(4)
```

</details>

#### stays on the original row when every row below is hidden

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = _app_with_hidden([])
val sh = app.workbook.active()
var r = 2
while r <= 100:
    sh.hide_row(r.to_i64())
    r = r + 1
app.navigate_to(0, 1)
expect(app.active_cell.row).to_equal(0)
```

</details>

#### leaves a pure horizontal move untouched by hidden rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = _app_with_hidden([2])
app.navigate_to(0, 1)
expect(app.active_cell.row).to_equal(2)
# Tab: same row, next column -- the row must not be re-scanned or moved.
app.navigate_to(1, 2)
expect(app.active_cell.row).to_equal(2)
expect(app.active_cell.col).to_equal(1)
```

</details>

#### never lands on a hidden row for any downward step across the sheet

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = _app_with_hidden([3, 4, 7, 11])
val sh = app.workbook.active()
var step = 0
while step < 12:
    val cur = app.active_cell.row
    app.navigate_to(0, cur + 1)
    assert_false(sh.is_row_hidden((app.active_cell.row + 1).to_i64()))
    step = step + 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
