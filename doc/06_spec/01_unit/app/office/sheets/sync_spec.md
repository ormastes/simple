# sync_spec

> Office sheets diff/apply sync spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sync_spec

Office sheets diff/apply sync spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/sync_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets diff/apply sync spec.

sheet_diff change detection (added/changed/cleared cells, formula raw text,
row-major op order, hide/unhide row-visibility ops), sheet_apply replay of
every op kind with formula recalculation, THE round-trip law
(apply(base, diff(base, current)) has an empty diff vs current) on a
multi-cell fixture including a formula, "op|kind|ref|text" line
serialization round trip, and composition with sheet_merge3 (disjoint op
sets merge cleanly; overlapping ops record a conflict).

## Scenarios

### sheet_diff: change detection

#### returns an empty diff for identical sheets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = base_fixture()
val b = base_fixture()
val ops = sheet_diff(a, b)
assert_equal(ops.len(), 0)
```

</details>

#### emits a set op for an added cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var cur = Sheet.new("s")
cur.set_value("A1", "10")
val ops = sheet_diff(base, cur)
assert_equal(ops.len(), 1)
val op = ops[0]
assert_equal(op.kind, "set")
assert_equal(op.ref, "A1")
assert_equal(op.text, "10")
```

</details>

#### emits a set op with the new raw text for a changed cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var cur = Sheet.new("s")
cur.set_value("A1", "20")
val ops = sheet_diff(base, cur)
assert_equal(ops.len(), 1)
val op = ops[0]
assert_equal(op.kind, "set")
assert_equal(op.text, "20")
```

</details>

#### emits formula SOURCE, not cached display, for formula cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var cur = Sheet.new("s")
cur.set_value("A1", "=SUM(1,2)")
cur = recalculate_formula_cells(cur)
val ops = sheet_diff(base, cur)
assert_equal(ops.len(), 1)
val op = ops[0]
assert_equal(op.text, "=SUM(1,2)")
```

</details>

#### emits a clear op for a deleted cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.set_value("A1", "10")
var cur = Sheet.new("s")
val ops = sheet_diff(base, cur)
assert_equal(ops.len(), 1)
val op = ops[0]
assert_equal(op.kind, "clear")
assert_equal(op.ref, "A1")
```

</details>

#### orders cell ops row-major regardless of insertion order

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var cur = Sheet.new("s")
cur.set_value("C1", "c1")
cur.set_value("A2", "a2")
cur.set_value("A1", "a1")
cur.set_value("B1", "b1")
val ops = sheet_diff(base, cur)
assert_equal(ops.len(), 4)
val op0 = ops[0]
val op1 = ops[1]
val op2 = ops[2]
val op3 = ops[3]
assert_equal(op0.ref, "A1")
assert_equal(op1.ref, "B1")
assert_equal(op2.ref, "C1")
assert_equal(op3.ref, "A2")
```

</details>

### sheet_diff: row visibility

#### emits a hide op for a newly hidden row

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
var cur = Sheet.new("s")
cur.hide_row(3)
val ops = sheet_diff(base, cur)
assert_equal(ops.len(), 1)
val op = ops[0]
assert_equal(op.kind, "hide")
assert_equal(op.ref, "3")
```

</details>

#### emits an unhide op for a newly unhidden row

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = Sheet.new("s")
base.hide_row(2)
var cur = Sheet.new("s")
val ops = sheet_diff(base, cur)
assert_equal(ops.len(), 1)
val op = ops[0]
assert_equal(op.kind, "unhide")
assert_equal(op.ref, "2")
```

</details>

### sheet_apply: op replay

#### applies a set op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = sheet_apply(sh, [SheetOp(ref: "A1", kind: "set", text: "42")])
assert_equal(cell_display_text(sh.get_cell("A1")), "42")
```

</details>

#### applies a clear op

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "9")
sh = sheet_apply(sh, [SheetOp(ref: "A1", kind: "clear", text: "")])
assert_equal(is_empty_cell(sh, "A1"), true)
```

</details>

#### applies hide and unhide ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = sheet_apply(sh, [SheetOp(ref: "4", kind: "hide", text: "")])
assert_equal(sh.is_row_hidden(4), true)
sh = sheet_apply(sh, [SheetOp(ref: "4", kind: "unhide", text: "")])
assert_equal(sh.is_row_hidden(4), false)
```

</details>

#### recalculates formulas when a set op carries formula text

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
var ops: [SheetOp] = []
ops.push(SheetOp(ref: "A1", kind: "set", text: "2"))
ops.push(SheetOp(ref: "B1", kind: "set", text: "3"))
ops.push(SheetOp(ref: "C1", kind: "set", text: "=A1+B1"))
sh = sheet_apply(sh, ops)
assert_equal(cell_display_text(sh.get_cell("C1")), "5")
```

</details>

### round-trip law

#### apply(base, diff(base, current)) has an empty diff vs current

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = base_fixture()
var cur = base_fixture()
cur.set_value("B1", "99")
cur.set_value("A2", "")
cur.set_value("D4", "=A1*2")
cur.hide_row(5)
cur = recalculate_formula_cells(cur)

val ops = sheet_diff(base, cur)
var replayed = sheet_apply(base, ops)
val residual = sheet_diff(replayed, cur)
assert_equal(residual.len(), 0)

# Cell-by-cell probe on top of the empty-residual law.
assert_equal(cell_display_text(replayed.get_cell("B1")), "99")
assert_equal(is_empty_cell(replayed, "A2"), true)
assert_equal(cell_display_text(replayed.get_cell("D4")), "2")
# C2 (=A1+B1) recalculates against the replayed B1=99 -> 100.
assert_equal(cell_display_text(replayed.get_cell("C2")), "100")
assert_equal(replayed.is_row_hidden(5), true)
```

</details>

### line serialization

#### formats each op as op|kind|ref|text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ops = [SheetOp(ref: "A1", kind: "set", text: "=A1+B1")]
val lines = ops_to_lines(ops)
assert_equal(lines.len(), 1)
assert_equal(lines[0], "op|set|A1|=A1+B1")
```

</details>

#### round-trips ops through lines, including pipes in cell text

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ops: [SheetOp] = []
ops.push(SheetOp(ref: "A1", kind: "set", text: "a|b"))
ops.push(SheetOp(ref: "B2", kind: "clear", text: ""))
ops.push(SheetOp(ref: "3", kind: "hide", text: ""))
val lines = ops_to_lines(ops)
val back = lines_to_ops(lines)
assert_equal(back.len(), 3)
val b0 = back[0]
val b1 = back[1]
val b2 = back[2]
assert_equal(b0.kind, "set")
assert_equal(b0.ref, "A1")
assert_equal(b0.text, "a|b")
assert_equal(b1.kind, "clear")
assert_equal(b1.ref, "B2")
assert_equal(b2.kind, "hide")
assert_equal(b2.ref, "3")
```

</details>

#### skips lines that are not ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["not an op", "op|set|A1|9"]
val back = lines_to_ops(lines)
assert_equal(back.len(), 1)
val b0 = back[0]
assert_equal(b0.ref, "A1")
assert_equal(b0.text, "9")
```

</details>

### composition with merge3

#### disjoint op sets merge with zero conflicts and both edits present

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = base_fixture()
var mine = base_fixture()
mine = sheet_apply(mine, [SheetOp(ref: "D1", kind: "set", text: "left")])
var theirs = base_fixture()
theirs = sheet_apply(theirs, [SheetOp(ref: "E1", kind: "set", text: "right")])

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 0)
assert_equal(cell_display_text(result.merged.get_cell("D1")), "left")
assert_equal(cell_display_text(result.merged.get_cell("E1")), "right")
```

</details>

#### overlapping ops on the same cell record a conflict (mine wins)

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = base_fixture()
var mine = base_fixture()
mine = sheet_apply(mine, [SheetOp(ref: "B1", kind: "set", text: "mine-b1")])
var theirs = base_fixture()
theirs = sheet_apply(theirs, [SheetOp(ref: "B1", kind: "set", text: "theirs-b1")])

val result = sheet_merge3(base, mine, theirs)
assert_equal(result.conflicts.len(), 1)
val c = result.conflicts[0]
assert_equal(c.ref, "B1")
assert_equal(c.mine_text, "mine-b1")
assert_equal(c.theirs_text, "theirs-b1")
assert_equal(cell_display_text(result.merged.get_cell("B1")), "mine-b1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
