# formula_lambda_helpers_spec

> Calc lambda helper functions: MAP, REDUCE, SCAN, BYROW, BYCOL, MAKEARRAY, ISOMITTED.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_lambda_helpers_spec

Calc lambda helper functions: MAP, REDUCE, SCAN, BYROW, BYCOL, MAKEARRAY, ISOMITTED.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_lambda_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc lambda helper functions: MAP, REDUCE, SCAN, BYROW, BYCOL, MAKEARRAY, ISOMITTED.

These functions enable higher-order array operations via immediate LAMBDA invocation.
Ground truths computed by hand and verified against expected math.

## Scenarios

### MAP basic

#### MAP(1:3, LAMBDA(x, x*2)) with A1:A3=[1,2,3] spills to C1:C3

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- MAP(1:3, LAMBDA(x, x*2)) with A1:A3=[1,2,3] spills to C1:C3
   - Expected: cell_display_text(sh.get_cell("C1")) equals `2`
   - Expected: cell_display_text(sh.get_cell("C2")) equals `4`
   - Expected: cell_display_text(sh.get_cell("C3")) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAP(1:3, LAMBDA(x, x*2)) with A1:A3=[1,2,3] spills to C1:C3")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("C1", "=MAP(A1:A3, LAMBDA(x, x*2))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C1"))).to_equal("2")
expect(cell_display_text(sh.get_cell("C2"))).to_equal("4")
expect(cell_display_text(sh.get_cell("C3"))).to_equal("6")
```

</details>

#### MAP with string transformation

- MAP with string transformation
   - Expected: cell_display_text(sh.get_cell("C1")) equals `HELLO`
   - Expected: cell_display_text(sh.get_cell("C2")) equals `WORLD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAP with string transformation")
var sh = Sheet.new("f")
sh.set_value("A1", "hello")
sh.set_value("A2", "world")
sh.set_value("C1", "=MAP(A1:A2, LAMBDA(x, UPPER(x)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C1"))).to_equal("HELLO")
expect(cell_display_text(sh.get_cell("C2"))).to_equal("WORLD")
```

</details>

### REDUCE basic

#### REDUCE(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 6

- REDUCE(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 6
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REDUCE(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 6")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("Z1", "=REDUCE(0, A1:A3, LAMBDA(a, b, a+b))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("6")
```

</details>

#### REDUCE(10, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 16

- REDUCE(10, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 16
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REDUCE(10, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 16")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("Z1", "=REDUCE(10, A1:A3, LAMBDA(a, b, a+b))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("16")
```

</details>

### SCAN basic

#### SCAN(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] spills [1,3,6]

- SCAN(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] spills [1,3,6]
   - Expected: cell_display_text(sh.get_cell("C1")) equals `1`
   - Expected: cell_display_text(sh.get_cell("C2")) equals `3`
   - Expected: cell_display_text(sh.get_cell("C3")) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SCAN(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] spills [1,3,6]")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("C1", "=SCAN(0, A1:A3, LAMBDA(a, b, a+b))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C1"))).to_equal("1")
expect(cell_display_text(sh.get_cell("C2"))).to_equal("3")
expect(cell_display_text(sh.get_cell("C3"))).to_equal("6")
```

</details>

### BYROW basic

#### BYROW(A1:B2, LAMBDA(r, SUM(r))) with [[1,2],[3,4]] spills [3,7] down

- BYROW(A1:B2, LAMBDA(r, SUM(r))) with [[1,2],[3,4]] spills [3,7] down
   - Expected: cell_display_text(sh.get_cell("D1")) equals `3`
   - Expected: cell_display_text(sh.get_cell("D2")) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BYROW(A1:B2, LAMBDA(r, SUM(r))) with [[1,2],[3,4]] spills [3,7] down")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("B1", "2")
sh.set_value("A2", "3")
sh.set_value("B2", "4")
sh.set_value("D1", "=BYROW(A1:B2, LAMBDA(r, SUM(r)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("3")
expect(cell_display_text(sh.get_cell("D2"))).to_equal("7")
```

</details>

#### BYROW(A1:B2, LAMBDA(r, PRODUCT(r))) with [[1,2],[3,4]] spills [2,12] down (general F(r) body, not just AGG)

- BYROW(A1:B2, LAMBDA(r, PRODUCT(r))) with [[1,2],[3,4]] spills [2,12] down (general F(r) body, not just AGG)
   - Expected: cell_display_text(sh.get_cell("D1")) equals `2`
   - Expected: cell_display_text(sh.get_cell("D2")) equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BYROW(A1:B2, LAMBDA(r, PRODUCT(r))) with [[1,2],[3,4]] spills [2,12] down (general F(r) body, not just AGG)")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("B1", "2")
sh.set_value("A2", "3")
sh.set_value("B2", "4")
sh.set_value("D1", "=BYROW(A1:B2, LAMBDA(r, PRODUCT(r)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("2")
expect(cell_display_text(sh.get_cell("D2"))).to_equal("12")
```

</details>

### BYCOL basic

#### BYCOL(A1:B2, LAMBDA(c, SUM(c))) with [[1,2],[3,4]] spills [4,6] across

- BYCOL(A1:B2, LAMBDA(c, SUM(c))) with [[1,2],[3,4]] spills [4,6] across
   - Expected: cell_display_text(sh.get_cell("D1")) equals `4`
   - Expected: cell_display_text(sh.get_cell("E1")) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BYCOL(A1:B2, LAMBDA(c, SUM(c))) with [[1,2],[3,4]] spills [4,6] across")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("B1", "2")
sh.set_value("A2", "3")
sh.set_value("B2", "4")
sh.set_value("D1", "=BYCOL(A1:B2, LAMBDA(c, SUM(c)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("4")
expect(cell_display_text(sh.get_cell("E1"))).to_equal("6")
```

</details>

#### BYCOL(A1:B2, LAMBDA(c, MEDIAN(c))) with [[1,2],[3,4]] spills [2,3] across (general F(c) body, not just AGG)

- BYCOL(A1:B2, LAMBDA(c, MEDIAN(c))) with [[1,2],[3,4]] spills [2,3] across (general F(c) body, not just AGG)
   - Expected: cell_display_text(sh.get_cell("D1")) equals `2`
   - Expected: cell_display_text(sh.get_cell("E1")) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BYCOL(A1:B2, LAMBDA(c, MEDIAN(c))) with [[1,2],[3,4]] spills [2,3] across (general F(c) body, not just AGG)")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("B1", "2")
sh.set_value("A2", "3")
sh.set_value("B2", "4")
sh.set_value("D1", "=BYCOL(A1:B2, LAMBDA(c, MEDIAN(c)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("2")
expect(cell_display_text(sh.get_cell("E1"))).to_equal("3")
```

</details>

### MAKEARRAY basic

#### MAKEARRAY(2, 3, LAMBDA(r, c, r*c)) spills [[1,2,3],[2,4,6]]

- MAKEARRAY(2, 3, LAMBDA(r, c, r*c)) spills [[1,2,3],[2,4,6]]
   - Expected: cell_display_text(sh.get_cell("C1")) equals `1`
   - Expected: cell_display_text(sh.get_cell("D1")) equals `2`
   - Expected: cell_display_text(sh.get_cell("E1")) equals `3`
   - Expected: cell_display_text(sh.get_cell("C2")) equals `2`
   - Expected: cell_display_text(sh.get_cell("D2")) equals `4`
   - Expected: cell_display_text(sh.get_cell("E2")) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAKEARRAY(2, 3, LAMBDA(r, c, r*c)) spills [[1,2,3],[2,4,6]]")
var sh = Sheet.new("f")
sh.set_value("C1", "=MAKEARRAY(2, 3, LAMBDA(r, c, r*c))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C1"))).to_equal("1")
expect(cell_display_text(sh.get_cell("D1"))).to_equal("2")
expect(cell_display_text(sh.get_cell("E1"))).to_equal("3")
expect(cell_display_text(sh.get_cell("C2"))).to_equal("2")
expect(cell_display_text(sh.get_cell("D2"))).to_equal("4")
expect(cell_display_text(sh.get_cell("E2"))).to_equal("6")
```

</details>

### ISOMITTED basic

#### LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5) = 5

- LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5) = 5
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5) = 5")
var sh = Sheet.new("f")
sh.set_value("Z1", "=LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("5")
```

</details>

#### LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5, 3) = 8

- LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5, 3) = 8
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5, 3) = 8")
var sh = Sheet.new("f")
sh.set_value("Z1", "=LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5, 3)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("8")
```

</details>

### Error domains

#### MAP without LAMBDA argument returns #ERR

- MAP without LAMBDA argument returns #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAP without LAMBDA argument returns #ERR")
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("Z1", "=MAP(A1, 42)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("Z1"))
assert_true(result.starts_with("#"))
```

</details>

#### REDUCE with no range returns #ERR

- REDUCE with no range returns #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REDUCE with no range returns #ERR")
var sh = Sheet.new("f")
sh.set_value("Z1", "=REDUCE(0, \"\", LAMBDA(a, b, a+b))")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("Z1"))
assert_true(result.starts_with("#"))
```

</details>

#### MAKEARRAY with negative rows returns #ERR

- MAKEARRAY with negative rows returns #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAKEARRAY with negative rows returns #ERR")
# Ground-truth correction: Excel's MAKEARRAY raises #CALC! for
# rows < 1 (rows/cols must be positive integers) — it does NOT
# silently return empty. This evaluator's array-path fails closed
# ([]) for rows<1, which falls back to the scalar dispatch and
# naturally yields "#ERR: Unknown function: MAKEARRAY" (the same
# fallback every array-only function gets on a malformed call).
var sh = Sheet.new("f")
sh.set_value("Z1", "=MAKEARRAY(-1, 2, LAMBDA(r, c, r))")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("Z1"))
assert_true(result.starts_with("#"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `d7188c37614da3ee1e1227b1289ad5fbbc83bc316d83f108fb0a4f56ed018ced`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7188c37614da3ee1e1227b1289ad5fbbc83bc316d83f108fb0a4f56ed018ced`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7188c37614da3ee1e1227b1289ad5fbbc83bc316d83f108fb0a4f56ed018ced`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_lambda_helpers_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_lambda_helpers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_lambda_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_lambda_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_lambda_helpers_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MAP(1:3, LAMBDA(x, x*2)) with A1:A3=[1,2,3] spills to C1:C3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_lambda_helpers_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MAP with string transformation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_lambda_helpers_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REDUCE(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 6' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
