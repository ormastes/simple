# formula_stats_spec

> Calc statistical functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_stats_spec

Calc statistical functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_stats_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc statistical functions spec.

MEDIAN / VAR / STDEV / LARGE / SMALL over ranges, matching Excel semantics
(sample variance, 1-based k). Evaluated through the real recalc path.

## Scenarios

### Calc statistics: MEDIAN/VAR/STDEV

#### computes the median of an even-sized range

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes the median of an even-sized range
   - Expected: cell_display_text(sh.get_cell("B1")) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes the median of an even-sized range")
var sh = _stats_sheet()
sh.set_value("B1", "=MEDIAN(A1:A4)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_equal("7")
```

</details>

#### computes sample variance (n-1) like Excel VAR

- computes sample variance (n-1) like Excel VAR


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes sample variance (n-1) like Excel VAR")
var sh = _stats_sheet()
sh.set_value("B1", "=VAR(A1:A4)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_start_with("6.66666")
```

</details>

#### computes STDEV as sqrt of sample variance

- computes STDEV as sqrt of sample variance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes STDEV as sqrt of sample variance")
var sh = _stats_sheet()
sh.set_value("B1", "=STDEV(A1:A4)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_start_with("2.58198")
```

</details>

### Calc statistics: LARGE/SMALL

#### returns the k-th largest and smallest

- returns the k-th largest and smallest
   - Expected: cell_display_text(sh.get_cell("B1")) equals `8`
   - Expected: cell_display_text(sh.get_cell("B2")) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the k-th largest and smallest")
var sh = _stats_sheet()
sh.set_value("B1", "=LARGE(A1:A4, 2)")
sh.set_value("B2", "=SMALL(A1:A4, 1)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_equal("8")
expect(cell_display_text(sh.get_cell("B2"))).to_equal("4")
```

</details>

#### fails closed on k out of range

- fails closed on k out of range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on k out of range")
var sh = _stats_sheet()
sh.set_value("B1", "=LARGE(A1:A4, 9)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_contain("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `45684afcf68b96bbda5f77d41635ae1a73b1a0463f0f840b285f8ab3b87af2e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45684afcf68b96bbda5f77d41635ae1a73b1a0463f0f840b285f8ab3b87af2e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45684afcf68b96bbda5f77d41635ae1a73b1a0463f0f840b285f8ab3b87af2e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_stats_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_stats_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_stats_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_stats_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_stats_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes the median of an even-sized range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_stats_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes sample variance (n-1) like Excel VAR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_stats_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes STDEV as sqrt of sample variance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
