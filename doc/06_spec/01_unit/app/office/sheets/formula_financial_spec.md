# formula_financial_spec

> Calc financial-tail functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_financial_spec

Calc financial-tail functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_financial_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc financial-tail functions spec.

Amortization (IPMT/PPMT/CUMIPMT/CUMPRINC/ISPMT), solvers
(RATE/IRR/MIRR), depreciation (SLN/SYD/DB/DDB) and rate conversions
(EFFECT/NOMINAL/RRI/PDURATION/FVSCHEDULE). Every expected value is verified
against Excel-documented examples; fractional powers route through the
exp/ln helper, and fail-closed #ERR domains are exercised (RATE
non-convergence, DDB/DB/SYD period past life). Range-consuming functions
(IRR/MIRR/FVSCHEDULE) read their cashflows/rates from pre-seeded cells.

## Scenarios

### Calc financial — depreciation

#### SLN is straight-line, SYD sums the digits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SLN is straight-line, SYD sums the digits
   - Expected: _eval("=SLN(30000, 7500, 10)") equals `2250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SLN is straight-line, SYD sums the digits")
expect(_eval("=SLN(30000, 7500, 10)")).to_equal("2250")
expect(_eval("=SYD(30000, 7500, 10, 1)")).to_start_with("4090.909")
expect(_eval("=SYD(30000, 7500, 10, 10)")).to_start_with("409.09")
```

</details>

#### DDB double-declines and clamps at salvage

- DDB double-declines and clamps at salvage
   - Expected: _eval("=DDB(2400, 300, 10, 1)") equals `480`
   - Expected: _eval("=DDB(2400, 300, 10, 2)") equals `384`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DDB double-declines and clamps at salvage")
expect(_eval("=DDB(2400, 300, 10, 1)")).to_equal("480")
expect(_eval("=DDB(2400, 300, 10, 2)")).to_equal("384")
```

</details>

#### DB uses the 3-decimal fixed-declining rate (full first year)

- DB uses the 3-decimal fixed-declining rate (full first year)
   - Expected: _eval("=DB(1000000, 100000, 6, 1)") equals `319000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DB uses the 3-decimal fixed-declining rate (full first year)")
expect(_eval("=DB(1000000, 100000, 6, 1)")).to_equal("319000")
```

</details>

#### depreciation fails closed when period exceeds life

- depreciation fails closed when period exceeds life


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("depreciation fails closed when period exceeds life")
expect(_eval("=DDB(2400, 300, 10, 11)")).to_contain("#ERR")
expect(_eval("=DB(1000000, 100000, 6, 7)")).to_contain("#ERR")
expect(_eval("=SYD(30000, 7500, 10, 11)")).to_contain("#ERR")
```

</details>

### Calc financial — amortization

#### IPMT is the interest slice, PPMT the principal slice

- IPMT is the interest slice, PPMT the principal slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("IPMT is the interest slice, PPMT the principal slice")
expect(_eval("=IPMT(0.1/12, 1, 36, 8000)")).to_start_with("-66.666")
expect(_eval("=PPMT(0.1/12, 1, 36, 8000)")).to_start_with("-191.47")
```

</details>

#### CUMIPMT and CUMPRINC accumulate over a period window

- CUMIPMT and CUMPRINC accumulate over a period window


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CUMIPMT and CUMPRINC accumulate over a period window")
expect(_eval("=CUMIPMT(0.09/12, 360, 125000, 13, 24, 0)")).to_start_with("-11135.23")
expect(_eval("=CUMPRINC(0.09/12, 360, 125000, 13, 24, 0)")).to_start_with("-934.10")
```

</details>

#### ISPMT gives level-principal interest for a period

- ISPMT gives level-principal interest for a period


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ISPMT gives level-principal interest for a period")
expect(_eval("=ISPMT(0.1/12, 1, 36, 8000)")).to_start_with("-64.814")
```

</details>

#### amortization fails closed on an out-of-range period

- amortization fails closed on an out-of-range period


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("amortization fails closed on an out-of-range period")
expect(_eval("=IPMT(0.1/12, 40, 36, 8000)")).to_contain("#ERR")
expect(_eval("=CUMIPMT(0.09/12, 360, 125000, 24, 13, 0)")).to_contain("#ERR")
```

</details>

### Calc financial — solvers

#### RATE recovers the periodic rate via Newton's method

- RATE recovers the periodic rate via Newton's method


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RATE recovers the periodic rate via Newton's method")
expect(_eval("=RATE(48, -200, 8000)")).to_start_with("0.00770")
```

</details>

#### RATE fails closed when the annuity has no root

- RATE fails closed when the annuity has no root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RATE fails closed when the annuity has no root")
expect(_eval("=RATE(2, 1000, 1000)")).to_contain("#ERR")
```

</details>

#### IRR solves the NPV = 0 rate over a cashflow range

- IRR solves the NPV = 0 rate over a cashflow range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("IRR solves the NPV = 0 rate over a cashflow range")
expect(_eval("=IRR(A1:A6)")).to_start_with("0.0866")
```

</details>

#### MIRR blends finance and reinvestment rates

- MIRR blends finance and reinvestment rates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MIRR blends finance and reinvestment rates")
expect(_eval("=MIRR(C1:C6, 0.1, 0.12)")).to_start_with("0.12609")
```

</details>

### Calc financial — rate conversions

#### EFFECT and NOMINAL round-trip a compounding rate

- EFFECT and NOMINAL round-trip a compounding rate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EFFECT and NOMINAL round-trip a compounding rate")
expect(_eval("=EFFECT(0.0525, 4)")).to_start_with("0.05354")
expect(_eval("=NOMINAL(0.053543, 4)")).to_start_with("0.0525")
```

</details>

#### RRI and PDURATION invert compound growth

- RRI and PDURATION invert compound growth


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RRI and PDURATION invert compound growth")
expect(_eval("=RRI(96, 10000, 11000)")).to_start_with("0.00099")
expect(_eval("=PDURATION(0.025, 1000, 1500)")).to_start_with("16.42")
```

</details>

#### FVSCHEDULE compounds a principal through a rate range

- FVSCHEDULE compounds a principal through a rate range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FVSCHEDULE compounds a principal through a rate range")
expect(_eval("=FVSCHEDULE(1, D1:D3)")).to_start_with("1.3308")
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

- Canonical SPipe generation for source `75e015dbbb5b899b895d3b47555074f01e28a4ee46c7da25ff968e09944c9919`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75e015dbbb5b899b895d3b47555074f01e28a4ee46c7da25ff968e09944c9919`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75e015dbbb5b899b895d3b47555074f01e28a4ee46c7da25ff968e09944c9919`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_financial_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_financial_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_financial_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_financial_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_financial_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SLN is straight-line, SYD sums the digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_financial_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DDB double-declines and clamps at salvage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_financial_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DB uses the 3-decimal fixed-declining rate (full first year)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
