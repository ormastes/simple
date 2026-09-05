# formula_finance_spec

> Calc regression + financial functions spec — 20 additions (99 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_finance_spec

Calc regression + financial functions spec — 20 additions (99 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_finance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc regression + financial functions spec — 20 additions (99 total).

SLOPE/INTERCEPT/CORREL/RSQ verified on an exact linear series; PMT/NPV/NPER
match Excel's closed forms; inverse-hyperbolics build on the LN series.

## Scenarios

### Calc regression pack

#### fits the exact line y = 2x

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fits the exact line y = 2x
   - Expected: _eval("=SLOPE(B1:B3, A1:A3)") equals `2`
   - Expected: _eval("=INTERCEPT(B1:B3, A1:A3)") equals `0`
   - Expected: _eval("=CORREL(A1:A3, B1:B3)") equals `1`
   - Expected: _eval("=RSQ(A1:A3, B1:B3)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fits the exact line y = 2x")
expect(_eval("=SLOPE(B1:B3, A1:A3)")).to_equal("2")
expect(_eval("=INTERCEPT(B1:B3, A1:A3)")).to_equal("0")
expect(_eval("=CORREL(A1:A3, B1:B3)")).to_equal("1")
expect(_eval("=RSQ(A1:A3, B1:B3)")).to_equal("1")
```

</details>

#### population statistics use the n denominator

- population statistics use the n denominator
   - Expected: _eval("=DEVSQ(A1:A3)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("population statistics use the n denominator")
expect(_eval("=STDEVP(A1:A3)")).to_start_with("0.81649")
expect(_eval("=VARP(A1:A3)")).to_start_with("0.66666")
expect(_eval("=DEVSQ(A1:A3)")).to_equal("2")
```

</details>

### Calc financial pack

#### PMT matches Excel's annuity formula

- PMT matches Excel's annuity formula


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PMT matches Excel's annuity formula")
expect(_eval("=PMT(0.01, 60, 10000)")).to_start_with("-222.444")
```

</details>

#### NPV discounts each period and NPER inverts the annuity

- NPV discounts each period and NPER inverts the annuity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NPV discounts each period and NPER inverts the annuity")
expect(_eval("=NPV(0.1, B1:B3)")).to_start_with("9.6318")
expect(_eval("=NPER(0.01, -100, 1000)")).to_start_with("10.588")
```

</details>

### Calc inverse trig/hyperbolic

#### ATAN2 handles quadrants, ATANH matches Fisher

- ATAN2 handles quadrants, ATANH matches Fisher
   - Expected: _eval("=ACOSH(1)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ATAN2 handles quadrants, ATANH matches Fisher")
expect(_eval("=ATAN2(1, 1)")).to_start_with("0.78539")
expect(_eval("=ATANH(0.5)")).to_start_with("0.54930")
expect(_eval("=ACOSH(1)")).to_equal("0")
expect(_eval("=COT(PI() / 4)")).to_start_with("1.0000")
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

- Canonical SPipe generation for source `6223c135097f2e7c8c1dc4bc70e8a72e1b44a62330c2131072b8542f8f2b2534`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6223c135097f2e7c8c1dc4bc70e8a72e1b44a62330c2131072b8542f8f2b2534`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6223c135097f2e7c8c1dc4bc70e8a72e1b44a62330c2131072b8542f8f2b2534`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_finance_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_finance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_finance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_finance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_finance_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fits the exact line y = 2x' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_finance_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'population statistics use the n denominator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_finance_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PMT matches Excel's annuity formula' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
