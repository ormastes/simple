# formula_ifs_stats_spec

> Calc plural-criteria + statistics-tail functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_ifs_stats_spec

Calc plural-criteria + statistics-tail functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_ifs_stats_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc plural-criteria + statistics-tail functions spec.

Plural criteria (multi-range AND semantics, Excel argument order): SUMIFS
puts the value range FIRST, followed by (crit_range, criteria) pairs, unlike
singular SUMIF; COUNTIFS/AVERAGEIFS/MAXIFS/MINIFS follow the same shape. A row
qualifies only when every (crit_range[i], criteria) pair matches, and all
ranges must be congruent else #ERR.

Statistics tail: QUARTILE (inclusive linear interpolation, pos = q/4*(n-1)),
PERCENTRANK (inclusive, 3 significant digits), TRIMMEAN (trim FLOOR(n*p/2) from
each end), SKEW / KURT (Excel sample formulas), COUNTBLANK / COUNTA over cell
ranges. Fractional expectations verified against recomputed Excel values.

## Scenarios

### Calc plural-criteria aggregation

#### SUMIFS sums the value range where all criteria match (value range first)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SUMIFS sums the value range where all criteria match (value range first)
   - Expected: _eval("=SUMIFS(A1:A4, B1:B4, \"x\")") equals `20`
   - Expected: _eval("=SUMIFS(A1:A4, B1:B4, \"x\", C1:C4, \">1\")") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUMIFS sums the value range where all criteria match (value range first)")
expect(_eval("=SUMIFS(A1:A4, B1:B4, \"x\")")).to_equal("20")
expect(_eval("=SUMIFS(A1:A4, B1:B4, \"x\", C1:C4, \">1\")")).to_equal("15")
```

</details>

#### COUNTIFS counts rows matching every criteria pair

- COUNTIFS counts rows matching every criteria pair
   - Expected: _eval("=COUNTIFS(B1:B4, \"y\", A1:A4, \">=10\")") equals `2`
   - Expected: _eval("=COUNTIFS(B1:B4, \"x\")") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COUNTIFS counts rows matching every criteria pair")
expect(_eval("=COUNTIFS(B1:B4, \"y\", A1:A4, \">=10\")")).to_equal("2")
expect(_eval("=COUNTIFS(B1:B4, \"x\")")).to_equal("2")
```

</details>

#### AVERAGEIFS averages qualifying value cells

- AVERAGEIFS averages qualifying value cells
   - Expected: _eval("=AVERAGEIFS(A1:A4, B1:B4, \"y\")") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AVERAGEIFS averages qualifying value cells")
expect(_eval("=AVERAGEIFS(A1:A4, B1:B4, \"y\")")).to_equal("15")
```

</details>

#### MAXIFS and MINIFS reduce qualifying value cells

- MAXIFS and MINIFS reduce qualifying value cells
   - Expected: _eval("=MAXIFS(A1:A4, C1:C4, \"<4\")") equals `15`
   - Expected: _eval("=MINIFS(A1:A4, B1:B4, \"y\")") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAXIFS and MINIFS reduce qualifying value cells")
expect(_eval("=MAXIFS(A1:A4, C1:C4, \"<4\")")).to_equal("15")
expect(_eval("=MINIFS(A1:A4, B1:B4, \"y\")")).to_equal("10")
```

</details>

#### incongruent ranges fail closed

- incongruent ranges fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incongruent ranges fail closed")
expect(_eval("=SUMIFS(A1:A4, B1:B2, \"x\")")).to_contain("#ERR")
expect(_eval("=COUNTIFS(B1:B4, \"x\", A1:A2, \">1\")")).to_contain("#ERR")
```

</details>

### Calc statistics tail

#### QUARTILE interpolates via q/4*(n-1)

- QUARTILE interpolates via q/4*(n-1)
   - Expected: _eval("=QUARTILE(E1:E5, 3)") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QUARTILE interpolates via q/4*(n-1)")
expect(_eval("=QUARTILE(D1:D4, 1)")).to_start_with("1.75")
expect(_eval("=QUARTILE(D1:D4, 2)")).to_start_with("2.5")
expect(_eval("=QUARTILE(E1:E5, 3)")).to_equal("3")
```

</details>

#### QUARTILE q=5 is out of domain

- QUARTILE q=5 is out of domain


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QUARTILE q=5 is out of domain")
expect(_eval("=QUARTILE(D1:D4, 5)")).to_contain("#ERR")
```

</details>

#### PERCENTRANK is inclusive to 3 significant digits

- PERCENTRANK is inclusive to 3 significant digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PERCENTRANK is inclusive to 3 significant digits")
expect(_eval("=PERCENTRANK(F1:F5, 3)")).to_start_with("0.5")
expect(_eval("=PERCENTRANK(F1:F5, 4)")).to_start_with("0.75")
```

</details>

#### TRIMMEAN trims FLOOR(n*p/2) from each end

- TRIMMEAN trims FLOOR(n*p/2) from each end


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRIMMEAN trims FLOOR(n*p/2) from each end")
expect(_eval("=TRIMMEAN(G1:G10, 0.2)")).to_start_with("5.5")
```

</details>

#### TRIMMEAN percent >= 1 fails closed

- TRIMMEAN percent >= 1 fails closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRIMMEAN percent >= 1 fails closed")
expect(_eval("=TRIMMEAN(G1:G10, 1)")).to_contain("#ERR")
```

</details>

#### SKEW and KURT match Excel sample formulas

- SKEW and KURT match Excel sample formulas


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SKEW and KURT match Excel sample formulas")
expect(_eval("=SKEW(H1:H10)")).to_start_with("0.35954")
expect(_eval("=KURT(H1:H10)")).to_start_with("-0.1517")
```

</details>

#### COUNTA counts non-empty and COUNTBLANK counts empty cells

- COUNTA counts non-empty and COUNTBLANK counts empty cells
   - Expected: _eval("=COUNTA(A1:A4)") equals `4`
   - Expected: _eval("=COUNTA(I1:I4)") equals `2`
   - Expected: _eval("=COUNTBLANK(I1:I4)") equals `2`
   - Expected: _eval("=COUNTBLANK(A1:A4)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COUNTA counts non-empty and COUNTBLANK counts empty cells")
expect(_eval("=COUNTA(A1:A4)")).to_equal("4")
expect(_eval("=COUNTA(I1:I4)")).to_equal("2")
expect(_eval("=COUNTBLANK(I1:I4)")).to_equal("2")
expect(_eval("=COUNTBLANK(A1:A4)")).to_equal("0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `62701ce9dbc3b70b7222923d01dcf340e36a0719e71f2ac88cfa0951436c4749`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62701ce9dbc3b70b7222923d01dcf340e36a0719e71f2ac88cfa0951436c4749`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62701ce9dbc3b70b7222923d01dcf340e36a0719e71f2ac88cfa0951436c4749`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_ifs_stats_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_ifs_stats_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_ifs_stats_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_ifs_stats_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_ifs_stats_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SUMIFS sums the value range where all criteria match (value range first)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_ifs_stats_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COUNTIFS counts rows matching every criteria pair' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_ifs_stats_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AVERAGEIFS averages qualifying value cells' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
