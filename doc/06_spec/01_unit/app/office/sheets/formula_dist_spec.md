# formula_dist_spec

> Calc statistical distributions + DATEVALUE spec (136 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_dist_spec

Calc statistical distributions + DATEVALUE spec (136 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_dist_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc statistical distributions + DATEVALUE spec (136 total).

NORMSDIST uses Abramowitz-Stegun erf (|err| < 1.5e-7) — verified at the
textbook 1.96 -> 0.975 point; BINOMDIST exact on fair-coin cases; POISSON and
EXPONDIST against closed-form references; DATEVALUE parses ISO and US forms
into the same serial as DATE.

## Scenarios

### Calc distributions

#### NORMSDIST matches textbook points

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- NORMSDIST matches textbook points


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NORMSDIST matches textbook points")
expect(_eval("=NORMSDIST(0)")).to_start_with("0.5000000")
expect(_eval("=NORMSDIST(1.96)")).to_start_with("0.97500")
```

</details>

#### BINOMDIST is exact on fair coins; POISSON and EXPONDIST match closed forms

- BINOMDIST is exact on fair coins; POISSON and EXPONDIST match closed forms
   - Expected: _eval("=BINOMDIST(2, 5, 0.5, FALSE())") equals `0.3125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BINOMDIST is exact on fair coins; POISSON and EXPONDIST match closed forms")
expect(_eval("=BINOMDIST(2, 5, 0.5, FALSE())")).to_equal("0.3125")
expect(_eval("=POISSON(2, 3, FALSE())")).to_start_with("0.22404")
expect(_eval("=EXPONDIST(1, 1, TRUE())")).to_start_with("0.63212")
```

</details>

#### cumulative flags switch pdf/cdf and domains fail closed

- cumulative flags switch pdf/cdf and domains fail closed
   - Expected: _eval("=BINOMDIST(2, 5, 0.5, TRUE())") equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cumulative flags switch pdf/cdf and domains fail closed")
expect(_eval("=NORMDIST(3, 3, 1, TRUE())")).to_start_with("0.5000000")
expect(_eval("=BINOMDIST(2, 5, 0.5, TRUE())")).to_equal("0.5")
expect(_eval("=NORMDIST(1, 0, 0, TRUE())")).to_contain("#ERR")
```

</details>

### Calc DATEVALUE

#### parses ISO and US date text to the DATE serial

- parses ISO and US date text to the DATE serial
   - Expected: _eval("=DATEVALUE(\"2026-07-03\")") equals `46206`
   - Expected: _eval("=DATEVALUE(\"7/3/2026\")") equals `46206`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses ISO and US date text to the DATE serial")
expect(_eval("=DATEVALUE(\"2026-07-03\")")).to_equal("46206")
expect(_eval("=DATEVALUE(\"7/3/2026\")")).to_equal("46206")
expect(_eval("=DATEVALUE(\"nonsense\")")).to_contain("#ERR")
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

- Canonical SPipe generation for source `0b1e7e00c69f16a127fc29305fe1cf71cf23cd25a7a6b4dbc73d05db590a6418`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b1e7e00c69f16a127fc29305fe1cf71cf23cd25a7a6b4dbc73d05db590a6418`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b1e7e00c69f16a127fc29305fe1cf71cf23cd25a7a6b4dbc73d05db590a6418`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_dist_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_dist_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_dist_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_dist_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_dist_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'NORMSDIST matches textbook points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_dist_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BINOMDIST is exact on fair coins; POISSON and EXPONDIST match closed forms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_dist_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cumulative flags switch pdf/cdf and domains fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
