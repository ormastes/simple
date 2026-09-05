# formula_arrays_spec

> Calc dynamic-array (spill) formulas spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_arrays_spec

Calc dynamic-array (spill) formulas spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_arrays_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc dynamic-array (spill) formulas spec.

Excel-style dynamic arrays: a formula whose result is a 2D range writes its
top-left value in its own cell and spills the rest into the adjacent rectangle.
If a target cell holds a value that is not the one being written, the origin
shows #SPILL! and nothing spills. Recalculation is idempotent (a prior identical
spill never blocks its own origin). Every expected value below is hand-computed.

## Scenarios

### Calc dynamic arrays — spill

#### SEQUENCE(3) spills three rows down

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SEQUENCE(3) spills three rows down
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "A2") equals `2`
   - Expected: _disp(sh, "A3") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SEQUENCE(3) spills three rows down")
var sh = Sheet.new("s")
sh.set_value("A1", "=SEQUENCE(3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "A3")).to_equal("3")
```

</details>

#### SEQUENCE(2,2,10,5) fills the exact 2x2 grid row-major

- SEQUENCE(2,2,10,5) fills the exact 2x2 grid row-major
   - Expected: _disp(sh, "A1") equals `10`
   - Expected: _disp(sh, "B1") equals `15`
   - Expected: _disp(sh, "A2") equals `20`
   - Expected: _disp(sh, "B2") equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SEQUENCE(2,2,10,5) fills the exact 2x2 grid row-major")
var sh = Sheet.new("s")
sh.set_value("A1", "=SEQUENCE(2,2,10,5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("10")
expect(_disp(sh, "B1")).to_equal("15")
expect(_disp(sh, "A2")).to_equal("20")
expect(_disp(sh, "B2")).to_equal("25")
```

</details>

#### TRANSPOSE of a 2x3 range yields a 3x2 range

- TRANSPOSE of a 2x3 range yields a 3x2 range
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "B1") equals `4`
   - Expected: _disp(sh, "A2") equals `2`
   - Expected: _disp(sh, "B2") equals `5`
   - Expected: _disp(sh, "A3") equals `3`
   - Expected: _disp(sh, "B3") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRANSPOSE of a 2x3 range yields a 3x2 range")
var sh = Sheet.new("s")
sh.set_value("D1", "1")
sh.set_value("E1", "2")
sh.set_value("F1", "3")
sh.set_value("D2", "4")
sh.set_value("E2", "5")
sh.set_value("F2", "6")
sh.set_value("A1", "=TRANSPOSE(D1:F2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("4")
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "B2")).to_equal("5")
expect(_disp(sh, "A3")).to_equal("3")
expect(_disp(sh, "B3")).to_equal("6")
```

</details>

#### UNIQUE keeps distinct values in first-seen order

- UNIQUE keeps distinct values in first-seen order
   - Expected: _disp(sh, "A1") equals `b`
   - Expected: _disp(sh, "A2") equals `a`
   - Expected: _disp(sh, "A3") equals `c`
   - Expected: _disp(sh, "A4") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UNIQUE keeps distinct values in first-seen order")
var sh = Sheet.new("s")
sh.set_value("D1", "b")
sh.set_value("D2", "a")
sh.set_value("D3", "b")
sh.set_value("D4", "c")
sh.set_value("D5", "a")
sh.set_value("A1", "=UNIQUE(D1:D5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("b")
expect(_disp(sh, "A2")).to_equal("a")
expect(_disp(sh, "A3")).to_equal("c")
expect(_disp(sh, "A4")).to_equal("")
```

</details>

#### SORT ascending orders a numeric column

- SORT ascending orders a numeric column
   - Expected: _disp(sh, "A1") equals `10`
   - Expected: _disp(sh, "A2") equals `20`
   - Expected: _disp(sh, "A3") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SORT ascending orders a numeric column")
var sh = Sheet.new("s")
sh.set_value("D1", "30")
sh.set_value("D2", "10")
sh.set_value("D3", "20")
sh.set_value("A1", "=SORT(D1:D3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("10")
expect(_disp(sh, "A2")).to_equal("20")
expect(_disp(sh, "A3")).to_equal("30")
```

</details>

#### SORT descending reverses the order

- SORT descending reverses the order
   - Expected: _disp(sh, "A1") equals `30`
   - Expected: _disp(sh, "A2") equals `20`
   - Expected: _disp(sh, "A3") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SORT descending reverses the order")
var sh = Sheet.new("s")
sh.set_value("D1", "30")
sh.set_value("D2", "10")
sh.set_value("D3", "20")
sh.set_value("A1", "=SORT(D1:D3,1,FALSE)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("30")
expect(_disp(sh, "A2")).to_equal("20")
expect(_disp(sh, "A3")).to_equal("10")
```

</details>

#### FILTER keeps rows matching a >10 criteria

- FILTER keeps rows matching a >10 criteria
   - Expected: _disp(sh, "A1") equals `15`
   - Expected: _disp(sh, "A2") equals `25`
   - Expected: _disp(sh, "A3") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FILTER keeps rows matching a >10 criteria")
var sh = Sheet.new("s")
sh.set_value("D1", "5")
sh.set_value("D2", "15")
sh.set_value("D3", "25")
sh.set_value("D4", "8")
sh.set_value("A1", "=FILTER(D1:D4,1,\">10\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("15")
expect(_disp(sh, "A2")).to_equal("25")
expect(_disp(sh, "A3")).to_equal("")
```

</details>

#### shows #SPILL! when a target cell is occupied

- shows #SPILL! when a target cell is occupied
   - Expected: _disp(sh, "A1") equals `#SPILL!`
   - Expected: _disp(sh, "A2") equals `X`
   - Expected: _disp(sh, "A3") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows #SPILL! when a target cell is occupied")
var sh = Sheet.new("s")
sh.set_value("A2", "X")
sh.set_value("A1", "=SEQUENCE(3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#SPILL!")
expect(_disp(sh, "A2")).to_equal("X")
expect(_disp(sh, "A3")).to_equal("")
```

</details>

#### recalculation is idempotent for a spilled formula

- recalculation is idempotent for a spilled formula
   - Expected: _disp(sh, "A1") equals `a1`
   - Expected: _disp(sh, "A2") equals `a2`
   - Expected: _disp(sh, "A3") equals `a3`
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "A3") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recalculation is idempotent for a spilled formula")
var sh = Sheet.new("s")
sh.set_value("A1", "=SEQUENCE(3)")
sh = recalculate_formula_cells(sh)
val a1 = _disp(sh, "A1")
val a2 = _disp(sh, "A2")
val a3 = _disp(sh, "A3")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal(a1)
expect(_disp(sh, "A2")).to_equal(a2)
expect(_disp(sh, "A3")).to_equal(a3)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "A3")).to_equal("3")
```

</details>

#### recalculation is idempotent for a blocked #SPILL!

- recalculation is idempotent for a blocked #SPILL!
   - Expected: _disp(sh, "A1") equals `#SPILL!`
   - Expected: _disp(sh, "A2") equals `X`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recalculation is idempotent for a blocked #SPILL!")
var sh = Sheet.new("s")
sh.set_value("A2", "X")
sh.set_value("A1", "=SEQUENCE(3)")
sh = recalculate_formula_cells(sh)
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#SPILL!")
expect(_disp(sh, "A2")).to_equal("X")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e1e8f1c667f1fff5f6630c741d84001a697231e3d6ea82a7d34ed21418f8a4c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1e8f1c667f1fff5f6630c741d84001a697231e3d6ea82a7d34ed21418f8a4c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1e8f1c667f1fff5f6630c741d84001a697231e3d6ea82a7d34ed21418f8a4c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_arrays_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_arrays_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_arrays_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_arrays_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_arrays_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SEQUENCE(3) spills three rows down' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_arrays_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SEQUENCE(2,2,10,5) fills the exact 2x2 grid row-major' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_arrays_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TRANSPOSE of a 2x3 range yields a 3x2 range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
