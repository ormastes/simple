# formula_stats2_spec

> Calc statistics batch 2 — 14 additions (79 functions total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_stats2_spec

Calc statistics batch 2 — 14 additions (79 functions total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_stats2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc statistics batch 2 — 14 additions (79 functions total).

GEOMEAN/HARMEAN/FISHER build on the pure LN/EXP series; RANK is descending
1-based; PERCENTILE uses Excel's inclusive linear interpolation; SUMPRODUCT
is pairwise over equal-length ranges.

## Scenarios

### Calc statistics batch 2

#### GEOMEAN/HARMEAN/MODE over ranges

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- GEOMEAN/HARMEAN/MODE over ranges
   - Expected: _eval("=MODE(A1:A4)") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GEOMEAN/HARMEAN/MODE over ranges")
expect(_eval("=GEOMEAN(A1:A4)")).to_start_with("4")
expect(_eval("=HARMEAN(A1, A2)")).to_start_with("2.66666")
expect(_eval("=MODE(A1:A4)")).to_equal("4")
```

</details>

#### RANK descending and PERCENTILE inclusive

- RANK descending and PERCENTILE inclusive
   - Expected: _eval("=RANK(4, A1:A4)") equals `2`
   - Expected: _eval("=RANK(8, A1:A4)") equals `1`
   - Expected: _eval("=PERCENTILE(A1:A4, 0.5)") equals `4`
   - Expected: _eval("=PERCENTILE(A1:A4, 1)") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RANK descending and PERCENTILE inclusive")
expect(_eval("=RANK(4, A1:A4)")).to_equal("2")
expect(_eval("=RANK(8, A1:A4)")).to_equal("1")
expect(_eval("=PERCENTILE(A1:A4, 0.5)")).to_equal("4")
expect(_eval("=PERCENTILE(A1:A4, 1)")).to_equal("8")
```

</details>

#### SUMPRODUCT pairs ranges and fails closed on size mismatch

- SUMPRODUCT pairs ranges and fails closed on size mismatch
   - Expected: _eval("=SUMPRODUCT(A1:A4, B1:B4)") equals `118`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUMPRODUCT pairs ranges and fails closed on size mismatch")
expect(_eval("=SUMPRODUCT(A1:A4, B1:B4)")).to_equal("118")
expect(_eval("=SUMPRODUCT(A1:A2, B1:B4)")).to_contain("#ERR")
```

</details>

#### engineering predicates and Fisher transform

- engineering predicates and Fisher transform
   - Expected: _eval("=ISEVEN(4)") equals `TRUE`
   - Expected: _eval("=ISODD(3)") equals `TRUE`
   - Expected: _eval("=DELTA(2, 2)") equals `1`
   - Expected: _eval("=GESTEP(5, 3)") equals `1`
   - Expected: _eval("=TRUE()") equals `TRUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("engineering predicates and Fisher transform")
expect(_eval("=ISEVEN(4)")).to_equal("TRUE")
expect(_eval("=ISODD(3)")).to_equal("TRUE")
expect(_eval("=DELTA(2, 2)")).to_equal("1")
expect(_eval("=GESTEP(5, 3)")).to_equal("1")
expect(_eval("=FISHER(0.5)")).to_start_with("0.54930")
expect(_eval("=TRUE()")).to_equal("TRUE")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `a24ff1ad5d8e27bb3c1726916847fe770408ca36378a6e065bcbb0d8c95f45a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a24ff1ad5d8e27bb3c1726916847fe770408ca36378a6e065bcbb0d8c95f45a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a24ff1ad5d8e27bb3c1726916847fe770408ca36378a6e065bcbb0d8c95f45a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_stats2_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_stats2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_stats2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_stats2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_stats2_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GEOMEAN/HARMEAN/MODE over ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_stats2_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RANK descending and PERCENTILE inclusive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_stats2_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SUMPRODUCT pairs ranges and fails closed on size mismatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
