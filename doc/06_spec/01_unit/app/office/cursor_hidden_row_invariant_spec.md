# cursor_hidden_row_invariant_spec

> Defect-CLASS spec: hidden-row awareness is a SHARED invariant of every

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cursor_hidden_row_invariant_spec

Defect-CLASS spec: hidden-row awareness is a SHARED invariant of every

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/cursor_hidden_row_invariant_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Defect-CLASS spec: hidden-row awareness is a SHARED invariant of every
cursor-movement entry point in Calc, not a property of any one of them.

The recurring defect tracked by
doc/08_tracking/bug/calc_cursor_hidden_row_awareness_divergence_2026-08-11.md
is not "path X has a bug" -- it is "a NEW cursor-movement entry point was
added and forgot hidden-row awareness". Three independent implementations
exist today:

  * GUI session   -- app.office.gui.session_key -> _sheet_gui_move_within_bounds
  * TUI           -- app.office.interactive.tui_apply_key -> _tui_move
  * Widget app    -- app.office.sheets.sheets_app.SheetsApp.navigate_to

Each was fixed separately, in that order, after each was separately found
broken. So this spec deliberately does NOT test one path's arithmetic. It
drives ALL THREE over the SAME fixture and asserts the invariant they must
jointly satisfy:

  I1. a vertical move never leaves the cursor on a hidden row;
  I2. all three paths agree on the resulting row (no silent divergence);
  I3. at a grid edge with no visible row left, the cursor stays put rather
      than landing on a hidden row or wrapping.

A fourth entry point added later fails this spec the moment it is added to
_row_after_down/_row_after_up below -- which is the point. Index base: the
hidden-row API is 1-BASED, CellRef.row is 0-BASED.

## Scenarios

### cursor movement: hidden-row awareness is a shared invariant

#### I1: no path leaves the cursor on a hidden row (single hidden row)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hidden = [2.to_i64()]
val sh = _hidden_sheet(hidden)
for landed in _all_paths(hidden, 0, "down"):
    assert_false(sh.is_row_hidden((landed + 1).to_i64()))
```

</details>

#### I1: no path leaves the cursor on a hidden row (run of hidden rows)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hidden = [2.to_i64(), 3.to_i64(), 4.to_i64()]
val sh = _hidden_sheet(hidden)
for landed in _all_paths(hidden, 0, "down"):
    assert_false(sh.is_row_hidden((landed + 1).to_i64()))
```

</details>

#### I2: all paths agree on the landing row going down

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = _all_paths([2.to_i64()], 0, "down")
expect(rows[0]).to_equal(2)
expect(rows[1]).to_equal(rows[0])
expect(rows[2]).to_equal(rows[0])
```

</details>

#### I2: all paths agree on the landing row going down over a run

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = _all_paths([2.to_i64(), 3.to_i64(), 4.to_i64()], 0, "down")
expect(rows[0]).to_equal(4)
expect(rows[1]).to_equal(rows[0])
expect(rows[2]).to_equal(rows[0])
```

</details>

#### I2: all paths agree on the landing row going up

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = _all_paths([2.to_i64()], 2, "up")
expect(rows[0]).to_equal(0)
expect(rows[1]).to_equal(rows[0])
expect(rows[2]).to_equal(rows[0])
```

</details>

#### I3: every path stays put when no visible row remains below

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var hidden: [i64] = []
var r = 2
while r <= GRID_ROWS:
    hidden = hidden + [r.to_i64()]
    r = r + 1
val sh = _hidden_sheet(hidden)
for landed in _all_paths(hidden, 0, "down"):
    expect(landed).to_equal(0)
    assert_false(sh.is_row_hidden((landed + 1).to_i64()))
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
