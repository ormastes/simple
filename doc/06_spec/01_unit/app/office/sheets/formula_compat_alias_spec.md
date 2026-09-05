# formula_compat_alias_spec

> Calc compatibility-alias spec (CARD 1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_compat_alias_spec

Calc compatibility-alias spec (CARD 1).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_compat_alias_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc compatibility-alias spec (CARD 1).

Proves Excel's modern dotted-name namespace on the pure-Simple formula engine:
  * the tokenizer keeps `.` inside a function name (NORM.DIST is ONE token), so a
    single expression may freely mix dotted and legacy spellings;
  * 21 pure aliases forward to the legacy implementation and return an identical
    value on a shared input (STDEV.S==STDEV, NORM.DIST==NORMDIST, ...);
  * genuinely-different dotted names carry their own semantics, hand-computed
    here: RANK.AVG averages tied ranks (2.5 for the middle of a two-way tie),
    CEILING.MATH/FLOOR.MATH follow the Excel-2013 negative-number/mode rules,
    CEILING.PRECISE/ISO.CEILING/FLOOR.PRECISE always round toward +/-inf, and
    NORM.INV/NORM.S.INV expose the Acklam inverse-normal helper.

Data range A1:A4 = [10, 20, 20, 30]; C1:C4 = [1, 2, 3, 4].

## Scenarios

### Calc compatibility aliases — dotted == legacy on shared input

#### range-based statistical aliases match their legacy base

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- range-based statistical aliases match their legacy base
   - Expected: _eval_data("=STDEV.S(A1:A4)") equals `_eval_data("=STDEV(A1:A4)")`
   - Expected: _eval_data("=STDEV.P(A1:A4)") equals `_eval_data("=STDEVP(A1:A4)")`
   - Expected: _eval_data("=VAR.S(A1:A4)") equals `_eval_data("=VAR(A1:A4)")`
   - Expected: _eval_data("=VAR.P(A1:A4)") equals `_eval_data("=VARP(A1:A4)")`
   - Expected: _eval_data("=MODE.SNGL(A1:A4)") equals `_eval_data("=MODE(A1:A4)")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range-based statistical aliases match their legacy base")
expect(_eval_data("=STDEV.S(A1:A4)")).to_equal(_eval_data("=STDEV(A1:A4)"))
expect(_eval_data("=STDEV.P(A1:A4)")).to_equal(_eval_data("=STDEVP(A1:A4)"))
expect(_eval_data("=VAR.S(A1:A4)")).to_equal(_eval_data("=VAR(A1:A4)"))
expect(_eval_data("=VAR.P(A1:A4)")).to_equal(_eval_data("=VARP(A1:A4)"))
expect(_eval_data("=MODE.SNGL(A1:A4)")).to_equal(_eval_data("=MODE(A1:A4)"))
```

</details>

#### rank/quantile aliases match their legacy base

- rank/quantile aliases match their legacy base
   - Expected: _eval_data("=RANK.EQ(20, A1:A4)") equals `_eval_data("=RANK(20, A1:A4)")`
   - Expected: _eval_data("=QUARTILE.INC(A1:A4, 1)") equals `_eval_data("=QUARTILE(A1:A4, 1)")`
   - Expected: _eval_data("=PERCENTILE.INC(A1:A4, 0.25)") equals `_eval_data("=PERCENTILE(A1:A4, 0.25)")`
   - Expected: _eval_data("=PERCENTRANK.INC(A1:A4, 20)") equals `_eval_data("=PERCENTRANK(A1:A4, 20)")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rank/quantile aliases match their legacy base")
expect(_eval_data("=RANK.EQ(20, A1:A4)")).to_equal(_eval_data("=RANK(20, A1:A4)"))
expect(_eval_data("=QUARTILE.INC(A1:A4, 1)")).to_equal(_eval_data("=QUARTILE(A1:A4, 1)"))
expect(_eval_data("=PERCENTILE.INC(A1:A4, 0.25)")).to_equal(_eval_data("=PERCENTILE(A1:A4, 0.25)"))
expect(_eval_data("=PERCENTRANK.INC(A1:A4, 20)")).to_equal(_eval_data("=PERCENTRANK(A1:A4, 20)"))
```

</details>

#### covariance alias matches on two ranges

- covariance alias matches on two ranges
   - Expected: _eval_data("=COVARIANCE.P(A1:A4, C1:C4)") equals `_eval_data("=COVAR(A1:A4, C1:C4)")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covariance alias matches on two ranges")
expect(_eval_data("=COVARIANCE.P(A1:A4, C1:C4)")).to_equal(_eval_data("=COVAR(A1:A4, C1:C4)"))
```

</details>

#### distribution aliases match their legacy base

- distribution aliases match their legacy base
   - Expected: _eval("=NORM.DIST(1, 0, 1, TRUE())") equals `_eval("=NORMDIST(1, 0, 1, TRUE())")`
   - Expected: _eval("=NORM.S.DIST(0.5)") equals `_eval("=NORMSDIST(0.5)")`
   - Expected: _eval("=BINOM.DIST(2, 5, 0.5, TRUE())") equals `_eval("=BINOMDIST(2, 5, 0.5, TRUE())")`
   - Expected: _eval("=NEGBINOM.DIST(10, 5, 0.25)") equals `_eval("=NEGBINOMDIST(10, 5, 0.25)")`
   - Expected: _eval("=HYPGEOM.DIST(1, 4, 8, 20)") equals `_eval("=HYPGEOMDIST(1, 4, 8, 20)")`
   - Expected: _eval("=POISSON.DIST(3, 2, TRUE())") equals `_eval("=POISSON(3, 2, TRUE())")`
   - Expected: _eval("=EXPON.DIST(1, 1, TRUE())") equals `_eval("=EXPONDIST(1, 1, TRUE())")`
   - Expected: _eval("=WEIBULL.DIST(1, 1, 1, TRUE())") equals `_eval("=WEIBULL(1, 1, 1, TRUE())")`
   - Expected: _eval("=LOGNORM.DIST(4, 3.5, 1.2)") equals `_eval("=LOGNORMDIST(4, 3.5, 1.2)")`
   - Expected: _eval("=CONFIDENCE.NORM(0.05, 2.5, 50)") equals `_eval("=CONFIDENCE(0.05, 2.5, 50)")`
   - Expected: _eval("=GAMMALN.PRECISE(4)") equals `_eval("=GAMMALN(4)")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distribution aliases match their legacy base")
expect(_eval("=NORM.DIST(1, 0, 1, TRUE())")).to_equal(_eval("=NORMDIST(1, 0, 1, TRUE())"))
expect(_eval("=NORM.S.DIST(0.5)")).to_equal(_eval("=NORMSDIST(0.5)"))
expect(_eval("=BINOM.DIST(2, 5, 0.5, TRUE())")).to_equal(_eval("=BINOMDIST(2, 5, 0.5, TRUE())"))
expect(_eval("=NEGBINOM.DIST(10, 5, 0.25)")).to_equal(_eval("=NEGBINOMDIST(10, 5, 0.25)"))
expect(_eval("=HYPGEOM.DIST(1, 4, 8, 20)")).to_equal(_eval("=HYPGEOMDIST(1, 4, 8, 20)"))
expect(_eval("=POISSON.DIST(3, 2, TRUE())")).to_equal(_eval("=POISSON(3, 2, TRUE())"))
expect(_eval("=EXPON.DIST(1, 1, TRUE())")).to_equal(_eval("=EXPONDIST(1, 1, TRUE())"))
expect(_eval("=WEIBULL.DIST(1, 1, 1, TRUE())")).to_equal(_eval("=WEIBULL(1, 1, 1, TRUE())"))
expect(_eval("=LOGNORM.DIST(4, 3.5, 1.2)")).to_equal(_eval("=LOGNORMDIST(4, 3.5, 1.2)"))
expect(_eval("=CONFIDENCE.NORM(0.05, 2.5, 50)")).to_equal(_eval("=CONFIDENCE(0.05, 2.5, 50)"))
expect(_eval("=GAMMALN.PRECISE(4)")).to_equal(_eval("=GAMMALN(4)"))
```

</details>

#### FORECAST.LINEAR aliases FORECAST, and legacy NORMINV/NORMSINV reach the dotted forms

- FORECAST.LINEAR aliases FORECAST, and legacy NORMINV/NORMSINV reach the dotted forms
   - Expected: _eval_data("=FORECAST.LINEAR(5, A1:A4, C1:C4)") equals `_eval_data("=FORECAST(5, A1:A4, C1:C4)")`
   - Expected: _eval("=NORMSINV(0.975)") equals `_eval("=NORM.S.INV(0.975)")`
   - Expected: _eval("=NORMINV(0.975, 10, 2)") equals `_eval("=NORM.INV(0.975, 10, 2)")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FORECAST.LINEAR aliases FORECAST, and legacy NORMINV/NORMSINV reach the dotted forms")
expect(_eval_data("=FORECAST.LINEAR(5, A1:A4, C1:C4)")).to_equal(_eval_data("=FORECAST(5, A1:A4, C1:C4)"))
expect(_eval("=NORMSINV(0.975)")).to_equal(_eval("=NORM.S.INV(0.975)"))
expect(_eval("=NORMINV(0.975, 10, 2)")).to_equal(_eval("=NORM.INV(0.975, 10, 2)"))
```

</details>

### Calc dotted names with genuinely-new semantics

#### RANK.AVG averages tied ranks (descending default)

- RANK.AVG averages tied ranks (descending default)
   - Expected: _eval_data("=RANK.AVG(20, A1:A4)") equals `2.5`
   - Expected: _eval_data("=RANK.AVG(10, A1:A4)") equals `4`
   - Expected: _eval_data("=RANK.AVG(30, A1:A4)") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RANK.AVG averages tied ranks (descending default)")
# [10,20,20,30]: 20 ranks EQ=2, tie group of 2 -> avg (2+3)/2 = 2.5
expect(_eval_data("=RANK.AVG(20, A1:A4)")).to_equal("2.5")
# 10 is the smallest -> rank 4 descending; 30 the largest -> rank 1
expect(_eval_data("=RANK.AVG(10, A1:A4)")).to_equal("4")
expect(_eval_data("=RANK.AVG(30, A1:A4)")).to_equal("1")
```

</details>

#### CEILING.MATH / FLOOR.MATH follow Excel-2013 negative + mode rules

- CEILING.MATH / FLOOR.MATH follow Excel-2013 negative + mode rules
   - Expected: _eval("=CEILING.MATH(-5.5)") equals `-5`
   - Expected: _eval("=FLOOR.MATH(-5.5)") equals `-6`
   - Expected: _eval("=CEILING.MATH(-5.5, 2, 1)") equals `-6`
   - Expected: _eval("=FLOOR.MATH(-5.5, 2, 1)") equals `-4`
   - Expected: _eval("=CEILING.MATH(6.7, 2)") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING.MATH / FLOOR.MATH follow Excel-2013 negative + mode rules")
expect(_eval("=CEILING.MATH(-5.5)")).to_equal("-5")
expect(_eval("=FLOOR.MATH(-5.5)")).to_equal("-6")
expect(_eval("=CEILING.MATH(-5.5, 2, 1)")).to_equal("-6")
expect(_eval("=FLOOR.MATH(-5.5, 2, 1)")).to_equal("-4")
expect(_eval("=CEILING.MATH(6.7, 2)")).to_equal("8")
```

</details>

#### CEILING.PRECISE / ISO.CEILING / FLOOR.PRECISE always round toward +/-inf

- CEILING.PRECISE / ISO.CEILING / FLOOR.PRECISE always round toward +/-inf
   - Expected: _eval("=CEILING.PRECISE(-4.1)") equals `-4`
   - Expected: _eval("=ISO.CEILING(-4.1)") equals `-4`
   - Expected: _eval("=FLOOR.PRECISE(-4.1)") equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING.PRECISE / ISO.CEILING / FLOOR.PRECISE always round toward +/-inf")
expect(_eval("=CEILING.PRECISE(-4.1)")).to_equal("-4")
expect(_eval("=ISO.CEILING(-4.1)")).to_equal("-4")
expect(_eval("=FLOOR.PRECISE(-4.1)")).to_equal("-5")
```

</details>

#### NORM.S.INV and NORM.INV expose the Acklam inverse-normal helper

- NORM.S.INV and NORM.INV expose the Acklam inverse-normal helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NORM.S.INV and NORM.INV expose the Acklam inverse-normal helper")
expect(_eval("=NORM.S.INV(0.975)")).to_start_with("1.95996")
expect(_eval("=NORM.INV(0.975, 10, 2)")).to_start_with("13.91992")
```

</details>

#### new-semantics domains fail closed with #ERR

- new-semantics domains fail closed with #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new-semantics domains fail closed with #ERR")
expect(_eval("=NORM.S.INV(0)")).to_contain("#ERR")
expect(_eval("=NORM.INV(0.5, 0, 0)")).to_contain("#ERR")
```

</details>

### Dotted-name tokenization proof

#### mixes dotted and legacy calls in a single expression

- mixes dotted and legacy calls in a single expression
   - Expected: _eval_data("=RANK.EQ(20, A1:A4) + RANK(20, A1:A4)") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixes dotted and legacy calls in a single expression")
# NORM.S.DIST(0) = 0.5 and NORMSDIST(0) = 0.5; the '.' must lex as part of
# the name for both to parse inside one expression -> ~1 (erf approx noise).
expect(_eval("=NORM.S.DIST(0) + NORMSDIST(0)")).to_start_with("1.0000000")
# A second mix: dotted RANK.EQ plus legacy RANK on the same value -> 2+2 = 4.
expect(_eval_data("=RANK.EQ(20, A1:A4) + RANK(20, A1:A4)")).to_equal("4")
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

- Canonical SPipe generation for source `201176f4151ba39e24b751faef318c08ff073f542fce29d3cab60a0c6bff24b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `201176f4151ba39e24b751faef318c08ff073f542fce29d3cab60a0c6bff24b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `201176f4151ba39e24b751faef318c08ff073f542fce29d3cab60a0c6bff24b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_compat_alias_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_compat_alias_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_compat_alias_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_compat_alias_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_compat_alias_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'range-based statistical aliases match their legacy base' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_compat_alias_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rank/quantile aliases match their legacy base' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_compat_alias_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covariance alias matches on two ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
