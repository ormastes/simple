# formula_ref2_spec

> Calc reference/lookup tail spec: OFFSET, INDIRECT, AREAS, HYPERLINK.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_ref2_spec

Calc reference/lookup tail spec: OFFSET, INDIRECT, AREAS, HYPERLINK.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_ref2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc reference/lookup tail spec: OFFSET, INDIRECT, AREAS, HYPERLINK.

OFFSET and INDIRECT live on TWO paths: the scalar formula path returns the
single referenced value (FormulaVal targets re-evaluate, empty targets report
0, per the CELL("contents") convention), and evaluate_formula_array spills the
referenced rectangle when OFFSET's height/width exceed 1 or INDIRECT's text is
a range like "A1:B2".

CEILING (documented, not faked): the generic numeric argument collector only
accepts literal REF:REF tokens or scalar expressions, so an array function
nested inside SUM — e.g. =SUM(OFFSET(A1,0,0,2,2)) — CANNOT deliver its grid.
In scalar context a height/width > 1 OFFSET yields its grid's TOP-LEFT value
(implicit-intersection-like), so the nested form totals 10 where Excel gives
100; that degradation is asserted below as documented behavior. The supported
equivalent — spill the OFFSET grid, then SUM over the spilled range — totals
100 and is asserted too (the top-left scalar convention is what lets the
range SUM re-evaluate the spill-origin cell correctly).

All expected values hand-checked against Excel semantics on the fixture
A1=10, A2=20, B1=30, B2=40.

## Scenarios

### OFFSET — scalar path

#### shifts down one row: OFFSET(A1,1,0) = 20

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shifts down one row: OFFSET(A1,1,0) = 20
   - Expected: _eval1("=OFFSET(A1,1,0)") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shifts down one row: OFFSET(A1,1,0) = 20")
expect(_eval1("=OFFSET(A1,1,0)")).to_equal("20")
```

</details>

#### shifts right one column: OFFSET(A1,0,1) = 30

- shifts right one column: OFFSET(A1,0,1) = 30
   - Expected: _eval1("=OFFSET(A1,0,1)") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shifts right one column: OFFSET(A1,0,1) = 30")
expect(_eval1("=OFFSET(A1,0,1)")).to_equal("30")
```

</details>

#### shifts diagonally: OFFSET(A1,1,1) = 40

- shifts diagonally: OFFSET(A1,1,1) = 40
   - Expected: _eval1("=OFFSET(A1,1,1)") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shifts diagonally: OFFSET(A1,1,1) = 40")
expect(_eval1("=OFFSET(A1,1,1)")).to_equal("40")
```

</details>

#### zero shift returns the reference itself: OFFSET(A1,0,0) = 10

- zero shift returns the reference itself: OFFSET(A1,0,0) = 10
   - Expected: _eval1("=OFFSET(A1,0,0)") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero shift returns the reference itself: OFFSET(A1,0,0) = 10")
expect(_eval1("=OFFSET(A1,0,0)")).to_equal("10")
```

</details>

#### uses the top-left corner of a range reference: OFFSET(A1:B2,1,1) = 40

- uses the top-left corner of a range reference: OFFSET(A1:B2,1,1) = 40
   - Expected: _eval1("=OFFSET(A1:B2,1,1)") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the top-left corner of a range reference: OFFSET(A1:B2,1,1) = 40")
expect(_eval1("=OFFSET(A1:B2,1,1)")).to_equal("40")
```

</details>

#### re-evaluates a formula target like CELL contents

- re-evaluates a formula target like CELL contents
   - Expected: _disp(sh, "D1") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-evaluates a formula target like CELL contents")
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("A3", "=A1+A2")
sh.set_value("D1", "=OFFSET(A3,0,0)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("30")
```

</details>

#### reports 0 for an empty target cell

- reports 0 for an empty target cell
   - Expected: _eval1("=OFFSET(A1,5,0)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports 0 for an empty target cell")
expect(_eval1("=OFFSET(A1,5,0)")).to_equal("0")
```

</details>

#### fails closed above row 1: OFFSET(A1,-1,0) = #ERR

- fails closed above row 1: OFFSET(A1,-1,0) = #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed above row 1: OFFSET(A1,-1,0) = #ERR")
expect(_eval1("=OFFSET(A1,-1,0)")).to_contain("#ERR")
```

</details>

#### fails closed left of column A: OFFSET(A1,0,-1) = #ERR

- fails closed left of column A: OFFSET(A1,0,-1) = #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed left of column A: OFFSET(A1,0,-1) = #ERR")
expect(_eval1("=OFFSET(A1,0,-1)")).to_contain("#ERR")
```

</details>

#### fails closed on height < 1

- fails closed on height < 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on height < 1")
expect(_eval1("=OFFSET(A1,0,0,0,1)")).to_contain("#ERR")
```

</details>

#### fails closed on width < 1

- fails closed on width < 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on width < 1")
expect(_eval1("=OFFSET(A1,0,0,1,0)")).to_contain("#ERR")
```

</details>

#### fails closed when rows/cols are missing

- fails closed when rows/cols are missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when rows/cols are missing")
expect(_eval1("=OFFSET(A1,1)")).to_contain("#ERR")
```

</details>

### OFFSET — array path (spills)

#### OFFSET(A1,0,0,2,2) spills the 2x2 rectangle

- OFFSET(A1,0,0,2,2) spills the 2x2 rectangle
   - Expected: _disp(sh, "D1") equals `10`
   - Expected: _disp(sh, "E1") equals `30`
   - Expected: _disp(sh, "D2") equals `20`
   - Expected: _disp(sh, "E2") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OFFSET(A1,0,0,2,2) spills the 2x2 rectangle")
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=OFFSET(A1,0,0,2,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("10")
expect(_disp(sh, "E1")).to_equal("30")
expect(_disp(sh, "D2")).to_equal("20")
expect(_disp(sh, "E2")).to_equal("40")
```

</details>

#### OFFSET(A1,1,0,1,2) spills the shifted 1x2 row

- OFFSET(A1,1,0,1,2) spills the shifted 1x2 row
   - Expected: _disp(sh, "D1") equals `20`
   - Expected: _disp(sh, "E1") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OFFSET(A1,1,0,1,2) spills the shifted 1x2 row")
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=OFFSET(A1,1,0,1,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("20")
expect(_disp(sh, "E1")).to_equal("40")
```

</details>

#### SUM over the spilled OFFSET grid totals 100 (supported form of SUM(OFFSET(...)))

- SUM over the spilled OFFSET grid totals 100 (supported form of SUM(OFFSET(...)))
   - Expected: _disp(sh, "G1") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUM over the spilled OFFSET grid totals 100 (supported form of SUM(OFFSET(...)))")
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=OFFSET(A1,0,0,2,2)")
sh = recalculate_formula_cells(sh)
sh.set_value("G1", "=SUM(D1:E2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "G1")).to_equal("100")
```

</details>

#### CEILING: nested SUM(OFFSET(...,2,2)) degrades to the grid's top-left (Excel: 100)

- CEILING: nested SUM(OFFSET(...,2,2)) degrades to the grid's top-left (Excel: 100)
   - Expected: _eval1("=SUM(OFFSET(A1,0,0,2,2))") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING: nested SUM(OFFSET(...,2,2)) degrades to the grid's top-left (Excel: 100)")
expect(_eval1("=SUM(OFFSET(A1,0,0,2,2))")).to_equal("10")
```

</details>

#### CEILING: grid OFFSET in a scalar expression yields the top-left value

- CEILING: grid OFFSET in a scalar expression yields the top-left value
   - Expected: _disp(sh, "D1") equals `[10]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING: grid OFFSET in a scalar expression yields the top-left value")
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=\"[\"&OFFSET(A1,0,0,2,2)&\"]\"")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("[10]")
```

</details>

### INDIRECT

#### resolves a literal reference string: INDIRECT(\

- resolves a literal reference string: INDIRECT(\
   - Expected: _eval1("=INDIRECT(\"B2\")") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a literal reference string: INDIRECT(\")
expect(_eval1("=INDIRECT(\"B2\")")).to_equal("40")
```

</details>

#### resolves a concatenated reference: INDIRECT(\

- resolves a concatenated reference: INDIRECT(\
   - Expected: _eval1("=INDIRECT(\"A\"&\"1\")") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a concatenated reference: INDIRECT(\")
expect(_eval1("=INDIRECT(\"A\"&\"1\")")).to_equal("10")
```

</details>

#### resolves a reference stored in another cell

- resolves a reference stored in another cell
   - Expected: _disp(sh, "D1") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a reference stored in another cell")
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("C1", "B1")
sh.set_value("D1", "=INDIRECT(C1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("30")
```

</details>

#### fails closed on unparseable text: INDIRECT(\

- fails closed on unparseable text: INDIRECT(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on unparseable text: INDIRECT(\")
expect(_eval1("=INDIRECT(\"nonsense\")")).to_contain("#ERR")
```

</details>

#### range form spills the referenced rectangle

- range form spills the referenced rectangle
   - Expected: _disp(sh, "D1") equals `10`
   - Expected: _disp(sh, "E1") equals `30`
   - Expected: _disp(sh, "D2") equals `20`
   - Expected: _disp(sh, "E2") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range form spills the referenced rectangle")
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=INDIRECT(\"A1:B2\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("10")
expect(_disp(sh, "E1")).to_equal("30")
expect(_disp(sh, "D2")).to_equal("20")
expect(_disp(sh, "E2")).to_equal("40")
```

</details>

### AREAS and HYPERLINK

#### AREAS of a range is 1 (single-area model)

- AREAS of a range is 1 (single-area model)
   - Expected: _eval1("=AREAS(A1:B2)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AREAS of a range is 1 (single-area model)")
expect(_eval1("=AREAS(A1:B2)")).to_equal("1")
```

</details>

#### AREAS of a single cell is 1

- AREAS of a single cell is 1
   - Expected: _eval1("=AREAS(A1)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AREAS of a single cell is 1")
expect(_eval1("=AREAS(A1)")).to_equal("1")
```

</details>

#### AREAS without a reference fails closed

- AREAS without a reference fails closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AREAS without a reference fails closed")
expect(_eval1("=AREAS()")).to_contain("#ERR")
```

</details>

#### HYPERLINK returns the friendly text

- HYPERLINK returns the friendly text
   - Expected: _eval1("=HYPERLINK(\"http://x.test\",\"Click\")") equals `Click`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HYPERLINK returns the friendly text")
expect(_eval1("=HYPERLINK(\"http://x.test\",\"Click\")")).to_equal("Click")
```

</details>

#### HYPERLINK without friendly text returns the url

- HYPERLINK without friendly text returns the url
   - Expected: _eval1("=HYPERLINK(\"http://x.test\")") equals `http://x.test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HYPERLINK without friendly text returns the url")
expect(_eval1("=HYPERLINK(\"http://x.test\")")).to_equal("http://x.test")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `6d9fed453f1890bbbc8ac7f82defb163e9b2c99acd60f0b96dbcd52e872c682c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d9fed453f1890bbbc8ac7f82defb163e9b2c99acd60f0b96dbcd52e872c682c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d9fed453f1890bbbc8ac7f82defb163e9b2c99acd60f0b96dbcd52e872c682c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_ref2_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_ref2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_ref2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_ref2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_ref2_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shifts down one row: OFFSET(A1,1,0) = 20' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_ref2_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shifts right one column: OFFSET(A1,0,1) = 30' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_ref2_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shifts diagonally: OFFSET(A1,1,1) = 40' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
