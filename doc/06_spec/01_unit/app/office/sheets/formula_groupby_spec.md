# formula_groupby_spec

> PERCENTOF, GROUPBY, PIVOTBY aggregation functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_groupby_spec

PERCENTOF, GROUPBY, PIVOTBY aggregation functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_groupby_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

PERCENTOF, GROUPBY, PIVOTBY aggregation functions spec.

PERCENTOF(data_subset, data_all) — numeric path: SUM(subset)/SUM(all).
GROUPBY(row_fields, values, function_name) — array path: groups by key, aggregates per group.
PIVOTBY(row_fields, col_fields, values, function_name) — array path: pivot table with totals.

## Scenarios

### PERCENTOF numeric aggregation

#### PERCENTOF(subset, all) divides sum of subset by sum of all

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- PERCENTOF(subset, all) divides sum of subset by sum of all


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTOF(subset, all) divides sum of subset by sum of all")
var sh = Sheet.new("s")
sh.set_value("B1", "10")
sh.set_value("B2", "20")
sh.set_value("B3", "30")
sh.set_value("B4", "40")
sh.set_value("B5", "50")
sh.set_value("B6", "60")
sh.set_value("A1", "=PERCENTOF(B1:B3, B1:B6)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_start_with("0.285714")
```

</details>

#### PERCENTOF with all equal values returns 1.0

- PERCENTOF with all equal values returns 1.0
   - Expected: _disp(sh, "A1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTOF with all equal values returns 1.0")
var sh = Sheet.new("s")
sh.set_value("B1", "5")
sh.set_value("B2", "5")
sh.set_value("B3", "5")
sh.set_value("A1", "=PERCENTOF(B1:B3, B1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
```

</details>

#### PERCENTOF with zero denominator returns #ERR

- PERCENTOF with zero denominator returns #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTOF with zero denominator returns #ERR")
var sh = Sheet.new("s")
sh.set_value("B1", "0")
sh.set_value("B2", "0")
sh.set_value("A1", "=PERCENTOF(B1:B2, B1:B2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_contain("#ERR")
```

</details>

### GROUPBY array aggregation

#### GROUPBY with SUM groups by key and sums values

- GROUPBY with SUM groups by key and sums values
   - Expected: _disp(sh, "D1") equals `East`
   - Expected: _disp(sh, "E1") equals `90`
   - Expected: _disp(sh, "D2") equals `West`
   - Expected: _disp(sh, "E2") equals `120`
   - Expected: _disp(sh, "D3") equals `Total`
   - Expected: _disp(sh, "E3") equals `210`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GROUPBY with SUM groups by key and sums values")
var sh = Sheet.new("s")
sh.set_value("A1", "East")
sh.set_value("A2", "West")
sh.set_value("A3", "East")
sh.set_value("A4", "West")
sh.set_value("A5", "East")
sh.set_value("A6", "West")
sh.set_value("B1", "10")
sh.set_value("B2", "20")
sh.set_value("B3", "30")
sh.set_value("B4", "40")
sh.set_value("B5", "50")
sh.set_value("B6", "60")
sh.set_value("D1", "=GROUPBY(A1:A6, B1:B6, SUM)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("East")
expect(_disp(sh, "E1")).to_equal("90")
expect(_disp(sh, "D2")).to_equal("West")
expect(_disp(sh, "E2")).to_equal("120")
expect(_disp(sh, "D3")).to_equal("Total")
expect(_disp(sh, "E3")).to_equal("210")
```

</details>

#### GROUPBY with AVERAGE computes mean per group

- GROUPBY with AVERAGE computes mean per group
   - Expected: _disp(sh, "D1") equals `East`
   - Expected: _disp(sh, "E1") equals `30`
   - Expected: _disp(sh, "D2") equals `West`
   - Expected: _disp(sh, "E2") equals `40`
   - Expected: _disp(sh, "D3") equals `Total`
   - Expected: _disp(sh, "E3") equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GROUPBY with AVERAGE computes mean per group")
var sh = Sheet.new("s")
sh.set_value("A1", "East")
sh.set_value("A2", "West")
sh.set_value("A3", "East")
sh.set_value("A4", "West")
sh.set_value("A5", "East")
sh.set_value("A6", "West")
sh.set_value("B1", "10")
sh.set_value("B2", "20")
sh.set_value("B3", "30")
sh.set_value("B4", "40")
sh.set_value("B5", "50")
sh.set_value("B6", "60")
sh.set_value("D1", "=GROUPBY(A1:A6, B1:B6, AVERAGE)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("East")
expect(_disp(sh, "E1")).to_equal("30")
expect(_disp(sh, "D2")).to_equal("West")
expect(_disp(sh, "E2")).to_equal("40")
expect(_disp(sh, "D3")).to_equal("Total")
expect(_disp(sh, "E3")).to_equal("35")
```

</details>

#### GROUPBY with COUNT counts rows per group

- GROUPBY with COUNT counts rows per group
   - Expected: _disp(sh, "D1") equals `East`
   - Expected: _disp(sh, "E1") equals `3`
   - Expected: _disp(sh, "D2") equals `West`
   - Expected: _disp(sh, "E2") equals `3`
   - Expected: _disp(sh, "D3") equals `Total`
   - Expected: _disp(sh, "E3") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GROUPBY with COUNT counts rows per group")
var sh = Sheet.new("s")
sh.set_value("A1", "East")
sh.set_value("A2", "West")
sh.set_value("A3", "East")
sh.set_value("A4", "West")
sh.set_value("A5", "East")
sh.set_value("A6", "West")
sh.set_value("B1", "10")
sh.set_value("B2", "20")
sh.set_value("B3", "30")
sh.set_value("B4", "40")
sh.set_value("B5", "50")
sh.set_value("B6", "60")
sh.set_value("D1", "=GROUPBY(A1:A6, B1:B6, COUNT)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("East")
expect(_disp(sh, "E1")).to_equal("3")
expect(_disp(sh, "D2")).to_equal("West")
expect(_disp(sh, "E2")).to_equal("3")
expect(_disp(sh, "D3")).to_equal("Total")
expect(_disp(sh, "E3")).to_equal("6")
```

</details>

#### GROUPBY with mismatched range heights returns #ERR

- GROUPBY with mismatched range heights returns #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GROUPBY with mismatched range heights returns #ERR")
var sh = Sheet.new("s")
sh.set_value("A1", "East")
sh.set_value("A2", "West")
sh.set_value("B1", "10")
sh.set_value("D1", "=GROUPBY(A1:A2, B1:B3, SUM)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### GROUPBY with unknown function returns #ERR

- GROUPBY with unknown function returns #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GROUPBY with unknown function returns #ERR")
var sh = Sheet.new("s")
sh.set_value("A1", "East")
sh.set_value("B1", "10")
sh.set_value("D1", "=GROUPBY(A1:A1, B1:B1, FOO)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

### PIVOTBY array pivot table

#### PIVOTBY with SUM creates a pivot grid with row/col totals

- PIVOTBY with SUM creates a pivot grid with row/col totals
   - Expected: _disp(sh, "E1") equals `East`
   - Expected: _disp(sh, "F1") equals `90`
   - Expected: _disp(sh, "G1") equals `0`
   - Expected: _disp(sh, "H1") equals `90`
   - Expected: _disp(sh, "E2") equals `West`
   - Expected: _disp(sh, "F2") equals `0`
   - Expected: _disp(sh, "G2") equals `120`
   - Expected: _disp(sh, "H2") equals `120`
   - Expected: _disp(sh, "E3") equals `Total`
   - Expected: _disp(sh, "F3") equals `90`
   - Expected: _disp(sh, "G3") equals `120`
   - Expected: _disp(sh, "H3") equals `210`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PIVOTBY with SUM creates a pivot grid with row/col totals")
var sh = Sheet.new("s")
sh.set_value("A1", "East")
sh.set_value("A2", "West")
sh.set_value("A3", "East")
sh.set_value("A4", "West")
sh.set_value("A5", "East")
sh.set_value("A6", "West")
sh.set_value("B1", "A")
sh.set_value("B2", "B")
sh.set_value("B3", "A")
sh.set_value("B4", "B")
sh.set_value("B5", "A")
sh.set_value("B6", "B")
sh.set_value("C1", "10")
sh.set_value("C2", "20")
sh.set_value("C3", "30")
sh.set_value("C4", "40")
sh.set_value("C5", "50")
sh.set_value("C6", "60")
sh.set_value("E1", "=PIVOTBY(A1:A6, B1:B6, C1:C6, SUM)")
sh = recalculate_formula_cells(sh)
# Design grid (no header row): a formula origin cell cannot cache an
# empty display (empty cached_display falls back to raw formula text),
# so the spill starts at the first row key. First-appearance order.
expect(_disp(sh, "E1")).to_equal("East")
expect(_disp(sh, "F1")).to_equal("90")
expect(_disp(sh, "G1")).to_equal("0")
expect(_disp(sh, "H1")).to_equal("90")
expect(_disp(sh, "E2")).to_equal("West")
expect(_disp(sh, "F2")).to_equal("0")
expect(_disp(sh, "G2")).to_equal("120")
expect(_disp(sh, "H2")).to_equal("120")
expect(_disp(sh, "E3")).to_equal("Total")
expect(_disp(sh, "F3")).to_equal("90")
expect(_disp(sh, "G3")).to_equal("120")
expect(_disp(sh, "H3")).to_equal("210")
```

</details>

#### PIVOTBY with mismatched range heights returns #ERR

- PIVOTBY with mismatched range heights returns #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PIVOTBY with mismatched range heights returns #ERR")
var sh = Sheet.new("s")
sh.set_value("A1", "East")
sh.set_value("A2", "West")
sh.set_value("B1", "A")
sh.set_value("C1", "10")
sh.set_value("E1", "=PIVOTBY(A1:A2, B1:B1, C1:C2, SUM)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "E1")).to_contain("#ERR")
```

</details>

#### PERCENTOF result with small percent

- PERCENTOF result with small percent


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTOF result with small percent")
var sh = Sheet.new("s")
sh.set_value("B1", "1")
sh.set_value("B2", "1")
sh.set_value("B3", "1")
sh.set_value("B4", "1")
sh.set_value("B5", "1")
sh.set_value("B6", "1")
sh.set_value("A1", "=PERCENTOF(B1:B1, B1:B6)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_start_with("0.166666")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `9e67b1b9d268fbe86cf8fbeb6635ae2a77833c5e9480eab35926acdecd95b1b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e67b1b9d268fbe86cf8fbeb6635ae2a77833c5e9480eab35926acdecd95b1b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e67b1b9d268fbe86cf8fbeb6635ae2a77833c5e9480eab35926acdecd95b1b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_groupby_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_groupby_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_groupby_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_groupby_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_groupby_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PERCENTOF(subset, all) divides sum of subset by sum of all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_groupby_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PERCENTOF with all equal values returns 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_groupby_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PERCENTOF with zero denominator returns #ERR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
