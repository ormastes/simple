# sheet_gui_session_spec

> Sheet GUI session spec: cell selection + cell edit + recalculation +

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sheet_gui_session_spec

Sheet GUI session spec: cell selection + cell edit + recalculation +

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheet_gui_session_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Sheet GUI session spec: cell selection + cell edit + recalculation +
viewport/scroll.

SheetGuiSession (session_new/session_select/session_edit) plus
sheet_gui_view_with_selection are the first sheet-GUI INTERACTION: select a
cell (marks it in the dump with "[...]" brackets and, per gui.spl's
office_gui_sheet_session_pixels, the widget carries the framework's real
"focused" CSS class), edit a cell's raw content (recalculates every formula
cell and returns a NEW session -- copy semantics, callers reassign), and
selection survives an edit.

The "viewport" describe block below covers the SECOND interaction pillar:
sheet_gui_view_with_selection renders only an N-VISIBLE window (view_rows x
view_cols VISIBLE rows/cols starting at session.view_top_row/view_left_col,
1-based) instead of the whole sheet, and selection-follows-scroll -- arrow
keys (session_key) and session_select auto-scroll the window the minimal
amount when the target ref would land outside it, and session_scroll does
explicit page moves. See gui.spl's "Viewport/scroll arithmetic" comment for
why N-visible (not N-grid) is the chosen semantics: a hidden row costs no
space in the viewport, so a window can backfill past it.

## Scenarios

### session_select: marks the right cell

#### brackets the selected cell's text and leaves other cells plain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_select(session_new(_demo_sheet(), "D2"), "D2", 5, 4)
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("[20]")
assert_false(_dump_contains(view.text_dump, "[10]"))
assert_false(_dump_contains(view.text_dump, "[2]"))
```

</details>

#### re-selecting a different ref moves the bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_select(session_new(_demo_sheet(), "D2"), "D2", 5, 4)
session = session_select(session, "B2", 5, 4)
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("[10]")
assert_false(_dump_contains(view.text_dump, "[20]"))
```

</details>

### session_edit: updates the cell

#### a plain-value cell shows its new text after edit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "A2")
session = session_edit(session, "A2", "Sprocket")
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("Sprocket")
assert_false(_dump_contains(view.text_dump, "Widget"))
```

</details>

### session_edit: dependent formula cells recalculate

#### editing B2 from 10 to 40 recalculates D2 (=B2*C2) and D5 (=SUM(D2:D3))

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "D2")
val before = sheet_gui_view_with_selection(session, 5, 4)
expect(before.text_dump).to_contain("[20]")

session = session_edit(session, "B2", "40")
val after = sheet_gui_view_with_selection(session, 5, 4)
expect(after.text_dump).to_contain("[80]")
expect(after.text_dump).to_contain("140")
assert_false(_dump_contains(after.text_dump, "[20]"))
```

</details>

### session_edit: selection survives an edit

#### the selected_ref is unchanged after editing a different cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_select(session_new(_demo_sheet(), "D2"), "D2", 5, 4)
session = session_edit(session, "B2", "40")
expect(session.selected_ref).to_equal("D2")
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("[80]")
```

</details>

### session_edit: editing a formula cell replaces the formula

#### overwriting D2 (=B2*C2) with a literal drops the formula entirely

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "D2")
session = session_edit(session, "D2", "999")
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("999")
assert_false(_dump_contains(view.text_dump, "=B2*C2"))
# D5 (=SUM(D2:D3)) now sums the literal 999 + D3's 60, not 20 + 60
expect(view.text_dump).to_contain("1059")
```

</details>

### pointer selection

#### a click computed to land on cell B2 selects B2

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_select(session_new(_demo_sheet(), "D2"), "D2", 5, 4)
val view = sheet_gui_view_with_selection(session, 5, 4)
val point = sheet_gui_cell_click_point(view, "B2", 640, 480)
val click_x = point.0
val click_y = point.1
assert_true(click_x >= 0)
assert_true(click_y >= 0)

val clicked = session_click(session, click_x, click_y, 5, 4, 640, 480)
expect(clicked.selected_ref).to_equal("B2")
val clicked_view = sheet_gui_view_with_selection(clicked, 5, 4)
expect(clicked_view.text_dump).to_contain("[10]")
assert_false(_dump_contains(clicked_view.text_dump, "[20]"))
```

</details>

#### a click outside the rendered viewport leaves the selection unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_select(session_new(_demo_sheet(), "D2"), "D2", 5, 4)
# (-10, -10) is outside every widget's rect at this viewport (the
# tree's root rect itself starts at (0, 0)) -- handle_pointer's
# hit-test finds nothing, so the real click-miss path (state
# unchanged) applies, not a fallback stub.
val clicked = session_click(session, -10, -10, 5, 4, 640, 480)
expect(clicked.selected_ref).to_equal("D2")
```

</details>

#### a click on a column-header widget (non-cell id) leaves the selection unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_select(session_new(_demo_sheet(), "D2"), "D2", 5, 4)
val view = sheet_gui_view_with_selection(session, 5, 4)
val rects = compute_layout(view.tree.root_node(), 0, 0, 640, 480)
var header_x = -1
var header_y = -1
match find_rect(rects, "sheet_sel_hdr_B"):
    case Some(r):
        header_x = r.x + r.w / 2
        header_y = r.y + r.h / 2
    case _:
        pass
assert_true(header_x >= 0)
assert_true(header_y >= 0)

val clicked = session_click(session, header_x, header_y, 5, 4, 640, 480)
expect(clicked.selected_ref).to_equal("D2")
```

</details>

#### clicked-then-edited flow: click selects B2, then editing B2 recalculates D2 and D5

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_select(session_new(_demo_sheet(), "D2"), "D2", 5, 4)
val view = sheet_gui_view_with_selection(session, 5, 4)
val point = sheet_gui_cell_click_point(view, "B2", 640, 480)
session = session_click(session, point.0, point.1, 5, 4, 640, 480)
expect(session.selected_ref).to_equal("B2")

session = session_edit(session, "B2", "40")
val after = sheet_gui_view_with_selection(session, 5, 4)
expect(after.text_dump).to_contain("[40]")
expect(after.text_dump).to_contain("140")
assert_false(_dump_contains(after.text_dump, "[10]"))
```

</details>

### keyboard

<details>
<summary>Advanced: arrow keys move the selection one cell at a time, looping back to the start</summary>

#### arrow keys move the selection one cell at a time, looping back to the start

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "B2")
session = session_key(session, "down", 5, 4, 5, 4)
expect(session.selected_ref).to_equal("B3")
session = session_key(session, "right", 5, 4, 5, 4)
expect(session.selected_ref).to_equal("C3")
session = session_key(session, "up", 5, 4, 5, 4)
expect(session.selected_ref).to_equal("C2")
session = session_key(session, "left", 5, 4, 5, 4)
expect(session.selected_ref).to_equal("B2")
```

</details>


</details>

#### arrow keys clamp at the grid's top-left edge instead of moving off-grid

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "A1")
session = session_key(session, "up", 5, 4, 5, 4)
expect(session.selected_ref).to_equal("A1")
session = session_key(session, "left", 5, 4, 5, 4)
expect(session.selected_ref).to_equal("A1")
```

</details>

#### down/up skip a hidden row instead of landing on it

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hidden_sheet = _demo_sheet_with_hidden_row()
var session = session_new(hidden_sheet, "B3")
session = session_key(session, "down", 5, 4, 5, 4)
expect(session.selected_ref).to_equal("B5")
session = session_key(session, "up", 5, 4, 5, 4)
expect(session.selected_ref).to_equal("B3")
```

</details>

#### typing accumulates a pending buffer, shown as ref:buffer in the dump

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "B3")
session = session_key(session, "9", 5, 4, 5, 4)
var view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("B3:9")
session = session_key(session, "9", 5, 4, 5, 4)
view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("B3:99")
assert_false(_dump_contains(view.text_dump, "[20]"))
```

</details>

#### enter commits the pending buffer and recalculates dependent formula cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "B3")
session = session_key(session, "9", 5, 4, 5, 4)
session = session_key(session, "9", 5, 4, 5, 4)
session = session_key(session, "enter", 5, 4, 5, 4)
expect(session.pending_input).to_equal("")
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("[99]")
expect(view.text_dump).to_contain("297")
expect(view.text_dump).to_contain("317")
assert_false(_dump_contains(view.text_dump, "[20]"))
```

</details>

#### escape cancels the pending buffer without committing or changing the sheet

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "B3")
session = session_key(session, "9", 5, 4, 5, 4)
session = session_key(session, "escape", 5, 4, 5, 4)
expect(session.pending_input).to_equal("")
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("[20]")
assert_false(_dump_contains(view.text_dump, "B3:9"))
```

</details>

#### backspace trims the last character off the pending buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "B3")
session = session_key(session, "9", 5, 4, 5, 4)
session = session_key(session, "9", 5, 4, 5, 4)
session = session_key(session, "backspace", 5, 4, 5, 4)
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("B3:9")
assert_false(_dump_contains(view.text_dump, "B3:99"))
```

</details>

### viewport

#### renders the correct N-visible slice for a mid-sheet window (headers + a mid-window value)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _scroll_demo_sheet()
# Constructed directly (not via session_select/session_key) to
# isolate sheet_gui_view_with_selection's OWN windowing/backfill
# logic from the scroll-to-show helpers exercised further below.
val session = SheetGuiSession(sheet: sheet, selected_ref: "B10", pending_input: "", view_top_row: 10, view_left_col: 1)
val view = sheet_gui_view_with_selection(session, 5, 2)
expect(view.text_dump).to_contain("viewport|A10:B15")
expect(view.text_dump).to_contain("|A|B")
# Row 13 (Item 12 / value 12) sits in the middle of the rendered window.
expect(view.text_dump).to_contain("13|Item 12|12")
```

</details>

#### a hidden row inside the window is excluded and the window backfills the next visible row

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _scroll_demo_sheet()
val session = SheetGuiSession(sheet: sheet, selected_ref: "B10", pending_input: "", view_top_row: 10, view_left_col: 1)
val view = sheet_gui_view_with_selection(session, 5, 2)
# Window starting at row 10 with row 12 hidden shows exactly
# 10,11,13,14,15 -- row 15 is the backfilled row that pays for
# row 12's exclusion, so the window still has 5 VISIBLE rows.
expect(view.text_dump).to_contain("\n10|Item 9|[9]")
expect(view.text_dump).to_contain("\n11|Item 10|10")
expect(view.text_dump).to_contain("\n13|Item 12|12")
expect(view.text_dump).to_contain("\n14|Item 13|13")
expect(view.text_dump).to_contain("\n15|Item 14|14")
assert_false(_dump_contains(view.text_dump, "\n12|"))
```

</details>

#### an arrow-key move past the window's bottom edge scrolls the viewport by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _scroll_demo_sheet()
var session = session_new(sheet, "B4")
# B4 -> B5: still inside the initial window (rows 1..5) -- no scroll.
session = session_key(session, "down", 30, 2, 5, 2)
expect(session.selected_ref).to_equal("B5")
expect(session.view_top_row).to_equal(1)
# B5 -> B6: steps past the window's bottom edge -- scrolls by
# exactly one grid row (view_top_row 1 -> 2), not a full page.
session = session_key(session, "down", 30, 2, 5, 2)
expect(session.selected_ref).to_equal("B6")
expect(session.view_top_row).to_equal(2)
val view = sheet_gui_view_with_selection(session, 5, 2)
expect(view.text_dump).to_contain("viewport|A2:B6")
```

</details>

#### session_select to an off-window ref scrolls the viewport to reveal it

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _scroll_demo_sheet()
var session = session_new(sheet, "B2")
# B14 is well outside the initial window (rows 1..5); with row 12
# hidden, the minimal backward-filled window ending at row 14 is
# 9,10,11,13,14 (row 12 skipped), so view_top_row becomes 9.
session = session_select(session, "B14", 5, 2)
expect(session.selected_ref).to_equal("B14")
expect(session.view_top_row).to_equal(9)
val view = sheet_gui_view_with_selection(session, 5, 2)
expect(view.text_dump).to_contain("viewport|A9:B14")
expect(view.text_dump).to_contain("[13]")
```

</details>

#### session_scroll page_down moves the viewport by a full window and keeps the selection's relative row

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = _scroll_demo_sheet()
var session = session_new(sheet, "B3")
# B3 is at index 2 (0-based) inside the initial window [1,2,3,4,5].
# Paging down moves the window to the next 5 visible rows (6..10,
# none hidden) and keeps the selection at the SAME relative index
# (2), landing on row 8.
session = session_scroll(session, "page_down", 5, 2)
expect(session.view_top_row).to_equal(6)
expect(session.selected_ref).to_equal("B8")
val view = sheet_gui_view_with_selection(session, 5, 2)
expect(view.text_dump).to_contain("viewport|A6:B10")
```

</details>

#### session_scroll page_right moves the column viewport by a full window and keeps the selection's relative column

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hand-computed on the 10-col fixture (A..J): starting at column A
# (view_left_col=1, i.e. 0-based old_left0=0) with a 4-visible-
# column window and A1 selected (0-based col 0, so col_offset =
# 0 - 0 = 0). page_right: new_left0 = old_left0 + view_cols =
# 0 + 4 = 4 (column E, 0-based), new_sel_col0 = new_left0 +
# col_offset = 4 + 0 = 4 -> column E -- so the window becomes
# E..H and the selection moves from A1 to E1 (same relative
# position -- first column of the window -- as it held before).
val sheet = _wide_demo_sheet()
var session = session_new(sheet, "A1")
session = session_scroll(session, "page_right", 1, 4)
expect(session.view_left_col).to_equal(5)
expect(session.selected_ref).to_equal("E1")
val view = sheet_gui_view_with_selection(session, 1, 4)
expect(view.text_dump).to_contain("viewport|E1:H1")
expect(view.text_dump).to_contain("[5]")
```

</details>

#### session_scroll page_left after page_right returns to the original column window (round trip)

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Continues from the page_right state above (window E..H, E1
# selected, 0-based old_left0=4, col_offset = 4 - 4 = 0).
# page_left: new_left0 = old_left0 - view_cols = 4 - 4 = 0 (back
# to column A), new_sel_col0 = new_left0 + col_offset = 0 + 0 = 0
# -> column A -- an exact round trip back to the state before
# page_right.
val sheet = _wide_demo_sheet()
var session = session_new(sheet, "A1")
session = session_scroll(session, "page_right", 1, 4)
session = session_scroll(session, "page_left", 1, 4)
expect(session.view_left_col).to_equal(1)
expect(session.selected_ref).to_equal("A1")
val view = sheet_gui_view_with_selection(session, 1, 4)
expect(view.text_dump).to_contain("viewport|A1:D1")
```

</details>

#### session_scroll page_left clamps at column A instead of scrolling past the left edge, preserving the selection's relative column

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hand-computed: window starts at column C (view_left_col=3, i.e.
# 0-based old_left0=2) with a 4-visible-column window (C..F) and
# D1 selected (0-based col 3, so col_offset = 3 - 2 = 1, one
# column into the window). page_left: new_left0 = old_left0 -
# view_cols = 2 - 4 = -2, clamped to 0 (column A) since there is
# no column left of A. new_sel_col0 = new_left0 + col_offset =
# 0 + 1 = 1 -> column B -- the selection keeps its SAME
# relative-into-the-window position (index 1) in the new,
# clamped A..D window, landing on B1 instead of the unclamped
# (and invalid) column -1.
val sheet = _wide_demo_sheet()
val session = SheetGuiSession(sheet: sheet, selected_ref: "D1", pending_input: "", view_top_row: 1, view_left_col: 3)
val scrolled = session_scroll(session, "page_left", 1, 4)
expect(scrolled.view_left_col).to_equal(1)
expect(scrolled.selected_ref).to_equal("B1")
val view = sheet_gui_view_with_selection(scrolled, 1, 4)
expect(view.text_dump).to_contain("viewport|A1:D1")
expect(view.text_dump).to_contain("[2]")
```

</details>

### live loop step

#### step with \

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_new(_demo_sheet(), "B2")
val step = run_gui_live_step(session, "down", 5, 4, 5, 4)
assert_false(step.quit)
expect(step.session.selected_ref).to_equal("B3")
```

</details>

#### step with typed chars then enter commits and recalculates dependent formula cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "B2")
var step = run_gui_live_step(session, "4", 5, 4, 5, 4)
session = step.session
step = run_gui_live_step(session, "0", 5, 4, 5, 4)
session = step.session
step = run_gui_live_step(session, "enter", 5, 4, 5, 4)
session = step.session
assert_false(step.quit)
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("[40]")
expect(view.text_dump).to_contain("140")
```

</details>

#### step with \

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = session_new(_demo_sheet(), "B2")
var step = run_gui_live_step(session, "9", 5, 4, 5, 4)
session = step.session
step = run_gui_live_step(session, "escape", 5, 4, 5, 4)
session = step.session
assert_false(step.quit)
expect(session.pending_input).to_equal("")
val view = sheet_gui_view_with_selection(session, 5, 4)
expect(view.text_dump).to_contain("[10]")
```

</details>

#### step with \

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_select(session_new(_demo_sheet(), "D2"), "D2", 5, 4)
val step = run_gui_live_step(session, "q", 5, 4, 5, 4)
assert_true(step.quit)
expect(step.session.selected_ref).to_equal("D2")
```

</details>

#### step with \

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_new(_demo_sheet(), "B2")
val step = run_gui_live_step(session, "ctrl_c", 5, 4, 5, 4)
assert_true(step.quit)
expect(step.session.selected_ref).to_equal("B2")
```

</details>

#### step with \

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = session_new(_demo_sheet(), "B2")
val step = run_gui_live_step(session, "eof", 5, 4, 5, 4)
assert_true(step.quit)
expect(step.session.selected_ref).to_equal("B2")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
