# formula_xlookup_arrays_spec

> Calc Excel-365 lookup + array-manipulation spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_xlookup_arrays_spec

Calc Excel-365 lookup + array-manipulation spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_xlookup_arrays_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc Excel-365 lookup + array-manipulation spec.

Scalar lookups (XLOOKUP/XMATCH/LOOKUP) evaluate through the scalar formula path
and cache a single display value. Array-manipulation functions
(CHOOSECOLS/CHOOSEROWS/TAKE/DROP/VSTACK/HSTACK/TOCOL/TOROW) evaluate to a 2D
grid: the top-left value stays in the formula's own cell and the rest spills into
the adjacent rectangle. Every expected value below is hand-computed against
Excel semantics.

## Scenarios

### Calc Excel-365 lookups — scalar

#### XLOOKUP finds an exact needle and returns the aligned value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- XLOOKUP finds an exact needle and returns the aligned value
   - Expected: _disp(sh, "D1") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XLOOKUP finds an exact needle and returns the aligned value")
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XLOOKUP(\"banana\",A1:A3,B1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("20")
```

</details>

#### XLOOKUP returns the if_not_found value when absent

- XLOOKUP returns the if_not_found value when absent
   - Expected: _disp(sh, "D1") equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XLOOKUP returns the if_not_found value when absent")
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XLOOKUP(\"kiwi\",A1:A3,B1:B3,\"none\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("none")
```

</details>

#### XLOOKUP with no if_not_found yields an error when absent

- XLOOKUP with no if_not_found yields an error when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XLOOKUP with no if_not_found yields an error when absent")
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XLOOKUP(\"kiwi\",A1:A3,B1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### XMATCH returns the 1-based position of an exact match

- XMATCH returns the 1-based position of an exact match
   - Expected: _disp(sh, "D1") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XMATCH returns the 1-based position of an exact match")
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XMATCH(\"cherry\",A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("3")
```

</details>

#### XMATCH yields an error when the needle is absent

- XMATCH yields an error when the needle is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("XMATCH yields an error when the needle is absent")
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XMATCH(\"kiwi\",A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### LOOKUP returns the result aligned to the largest value <= needle

- LOOKUP returns the result aligned to the largest value <= needle
   - Expected: _disp(sh, "D1") equals `banana`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOOKUP returns the result aligned to the largest value <= needle")
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=LOOKUP(25,B1:B3,A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("banana")
```

</details>

#### LOOKUP errors when the needle precedes the first value

- LOOKUP errors when the needle precedes the first value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LOOKUP errors when the needle precedes the first value")
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=LOOKUP(5,B1:B3,A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

### Calc Excel-365 array manipulation — spill

#### CHOOSECOLS keeps the named columns in order

- CHOOSECOLS keeps the named columns in order
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "B1") equals `3`
   - Expected: _disp(sh, "A2") equals `4`
   - Expected: _disp(sh, "B2") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CHOOSECOLS keeps the named columns in order")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=CHOOSECOLS(H1:J2,1,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("3")
expect(_disp(sh, "A2")).to_equal("4")
expect(_disp(sh, "B2")).to_equal("6")
```

</details>

#### CHOOSEROWS with a negative index takes the last row

- CHOOSEROWS with a negative index takes the last row
   - Expected: _disp(sh, "A1") equals `4`
   - Expected: _disp(sh, "B1") equals `5`
   - Expected: _disp(sh, "C1") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CHOOSEROWS with a negative index takes the last row")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=CHOOSEROWS(H1:J2,-1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("4")
expect(_disp(sh, "B1")).to_equal("5")
expect(_disp(sh, "C1")).to_equal("6")
```

</details>

#### CHOOSECOLS fails closed with #ERR on an out-of-range index

- CHOOSECOLS fails closed with #ERR on an out-of-range index
   - Expected: _disp(sh, "A1") equals `#ERR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CHOOSECOLS fails closed with #ERR on an out-of-range index")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=CHOOSECOLS(H1:J2,9)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

#### TAKE keeps the first rows and columns

- TAKE keeps the first rows and columns
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "B1") equals `2`
   - Expected: _disp(sh, "A2") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TAKE keeps the first rows and columns")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TAKE(H1:J2,1,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "A2")).to_equal("")
```

</details>

#### TAKE with a negative row count takes from the end

- TAKE with a negative row count takes from the end
   - Expected: _disp(sh, "A1") equals `4`
   - Expected: _disp(sh, "B1") equals `5`
   - Expected: _disp(sh, "C1") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TAKE with a negative row count takes from the end")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TAKE(H1:J2,-1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("4")
expect(_disp(sh, "B1")).to_equal("5")
expect(_disp(sh, "C1")).to_equal("6")
```

</details>

#### TAKE fails closed with #ERR on a zero count

- TAKE fails closed with #ERR on a zero count
   - Expected: _disp(sh, "A1") equals `#ERR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TAKE fails closed with #ERR on a zero count")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TAKE(H1:J2,0)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

#### DROP removes the first row

- DROP removes the first row
   - Expected: _disp(sh, "A1") equals `4`
   - Expected: _disp(sh, "B1") equals `5`
   - Expected: _disp(sh, "C1") equals `6`
   - Expected: _disp(sh, "A2") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DROP removes the first row")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=DROP(H1:J2,1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("4")
expect(_disp(sh, "B1")).to_equal("5")
expect(_disp(sh, "C1")).to_equal("6")
expect(_disp(sh, "A2")).to_equal("")
```

</details>

#### DROP fails closed with #ERR when it would remove every row

- DROP fails closed with #ERR when it would remove every row
   - Expected: _disp(sh, "A1") equals `#ERR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DROP fails closed with #ERR when it would remove every row")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=DROP(H1:J2,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

#### VSTACK stacks vertically and pads ragged widths with #N/A

- VSTACK stacks vertically and pads ragged widths with #N/A
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "B1") equals `2`
   - Expected: _disp(sh, "C1") equals `#N/A`
   - Expected: _disp(sh, "A2") equals `4`
   - Expected: _disp(sh, "B2") equals `5`
   - Expected: _disp(sh, "C2") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSTACK stacks vertically and pads ragged widths with #N/A")
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("I1", "2")
sh.set_value("H2", "4")
sh.set_value("I2", "5")
sh.set_value("J2", "6")
sh.set_value("A1", "=VSTACK(H1:I1,H2:J2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "C1")).to_equal("#N/A")
expect(_disp(sh, "A2")).to_equal("4")
expect(_disp(sh, "B2")).to_equal("5")
expect(_disp(sh, "C2")).to_equal("6")
```

</details>

#### HSTACK places grids side by side

- HSTACK places grids side by side
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "B1") equals `2`
   - Expected: _disp(sh, "A2") equals `4`
   - Expected: _disp(sh, "B2") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HSTACK places grids side by side")
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("H2", "4")
sh.set_value("I1", "2")
sh.set_value("I2", "5")
sh.set_value("A1", "=HSTACK(H1:H2,I1:I2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "A2")).to_equal("4")
expect(_disp(sh, "B2")).to_equal("5")
```

</details>

#### TOCOL flattens the grid row-major into one column

- TOCOL flattens the grid row-major into one column
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "A2") equals `2`
   - Expected: _disp(sh, "A3") equals `3`
   - Expected: _disp(sh, "A4") equals `4`
   - Expected: _disp(sh, "A5") equals `5`
   - Expected: _disp(sh, "A6") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TOCOL flattens the grid row-major into one column")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TOCOL(H1:J2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "A3")).to_equal("3")
expect(_disp(sh, "A4")).to_equal("4")
expect(_disp(sh, "A5")).to_equal("5")
expect(_disp(sh, "A6")).to_equal("6")
```

</details>

#### TOROW flattens the grid row-major into one row

- TOROW flattens the grid row-major into one row
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "B1") equals `2`
   - Expected: _disp(sh, "C1") equals `3`
   - Expected: _disp(sh, "D1") equals `4`
   - Expected: _disp(sh, "E1") equals `5`
   - Expected: _disp(sh, "F1") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TOROW flattens the grid row-major into one row")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TOROW(H1:J2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "C1")).to_equal("3")
expect(_disp(sh, "D1")).to_equal("4")
expect(_disp(sh, "E1")).to_equal("5")
expect(_disp(sh, "F1")).to_equal("6")
```

</details>

#### spill for an array function is idempotent

- spill for an array function is idempotent
   - Expected: _disp(sh, "A1") equals `a1`
   - Expected: _disp(sh, "A6") equals `a6`
   - Expected: _disp(sh, "A1") equals `1`
   - Expected: _disp(sh, "A6") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spill for an array function is idempotent")
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TOCOL(H1:J2)")
sh = recalculate_formula_cells(sh)
val a1 = _disp(sh, "A1")
val a6 = _disp(sh, "A6")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal(a1)
expect(_disp(sh, "A6")).to_equal(a6)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "A6")).to_equal("6")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `930478818eda26fa5e1cfa3133a23d31282c6135b53646b723916d32b7224f71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `930478818eda26fa5e1cfa3133a23d31282c6135b53646b723916d32b7224f71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `930478818eda26fa5e1cfa3133a23d31282c6135b53646b723916d32b7224f71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_xlookup_arrays_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_xlookup_arrays_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_xlookup_arrays_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_xlookup_arrays_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_xlookup_arrays_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'XLOOKUP finds an exact needle and returns the aligned value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_xlookup_arrays_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'XLOOKUP returns the if_not_found value when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_xlookup_arrays_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'XLOOKUP with no if_not_found yields an error when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
