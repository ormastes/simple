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
| Updated | 2026-08-26 |
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

- returns an empty diff for identical sheets


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty diff for identical sheets")
val a = base_fixture()
val b = base_fixture()
val ops = sheet_diff(a, b)
assert_equal(ops.len(), 0)
```

</details>

#### emits a set op for an added cell

- emits a set op for an added cell


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a set op for an added cell")
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

- emits a set op with the new raw text for a changed cell


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a set op with the new raw text for a changed cell")
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

- emits formula SOURCE, not cached display, for formula cells


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits formula SOURCE, not cached display, for formula cells")
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

- emits a clear op for a deleted cell


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a clear op for a deleted cell")
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

- orders cell ops row-major regardless of insertion order


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders cell ops row-major regardless of insertion order")
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

- emits a hide op for a newly hidden row


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a hide op for a newly hidden row")
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

- emits an unhide op for a newly unhidden row


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits an unhide op for a newly unhidden row")
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

- applies a set op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies a set op")
var sh = Sheet.new("s")
sh = sheet_apply(sh, [SheetOp(ref: "A1", kind: "set", text: "42")])
assert_equal(cell_display_text(sh.get_cell("A1")), "42")
```

</details>

#### applies a clear op

- applies a clear op


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies a clear op")
var sh = Sheet.new("s")
sh.set_value("A1", "9")
sh = sheet_apply(sh, [SheetOp(ref: "A1", kind: "clear", text: "")])
assert_equal(is_empty_cell(sh, "A1"), true)
```

</details>

#### applies hide and unhide ops

- applies hide and unhide ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies hide and unhide ops")
var sh = Sheet.new("s")
sh = sheet_apply(sh, [SheetOp(ref: "4", kind: "hide", text: "")])
assert_equal(sh.is_row_hidden(4), true)
sh = sheet_apply(sh, [SheetOp(ref: "4", kind: "unhide", text: "")])
assert_equal(sh.is_row_hidden(4), false)
```

</details>

#### recalculates formulas when a set op carries formula text

- recalculates formulas when a set op carries formula text


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recalculates formulas when a set op carries formula text")
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

- apply(base, diff(base, current)) has an empty diff vs current


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply(base, diff(base, current)) has an empty diff vs current")
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

- formats each op as op|kind|ref|text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats each op as op|kind|ref|text")
val ops = [SheetOp(ref: "A1", kind: "set", text: "=A1+B1")]
val lines = ops_to_lines(ops)
assert_equal(lines.len(), 1)
assert_equal(lines[0], "op|set|A1|=A1+B1")
```

</details>

#### round-trips ops through lines, including pipes in cell text

- round-trips ops through lines, including pipes in cell text


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips ops through lines, including pipes in cell text")
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

- skips lines that are not ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips lines that are not ops")
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

- disjoint op sets merge with zero conflicts and both edits present


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disjoint op sets merge with zero conflicts and both edits present")
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

- overlapping ops on the same cell record a conflict (mine wins)


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overlapping ops on the same cell record a conflict (mine wins)")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7bb91925744758c79912f56c1619be50231c2293a401e1d7181a06d32070cc01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bb91925744758c79912f56c1619be50231c2293a401e1d7181a06d32070cc01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bb91925744758c79912f56c1619be50231c2293a401e1d7181a06d32070cc01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/app/office/sheets/sync_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/sync_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/sync_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/sync_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/sync_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/office/sheets/sync_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an empty diff for identical sheets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/sync_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a set op for an added cell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/sync_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a set op with the new raw text for a changed cell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
