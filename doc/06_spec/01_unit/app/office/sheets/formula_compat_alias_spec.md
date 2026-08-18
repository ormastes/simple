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
| Updated | 2026-08-18 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_data("=STDEV.S(A1:A4)")).to_equal(_eval_data("=STDEV(A1:A4)"))
expect(_eval_data("=STDEV.P(A1:A4)")).to_equal(_eval_data("=STDEVP(A1:A4)"))
expect(_eval_data("=VAR.S(A1:A4)")).to_equal(_eval_data("=VAR(A1:A4)"))
expect(_eval_data("=VAR.P(A1:A4)")).to_equal(_eval_data("=VARP(A1:A4)"))
expect(_eval_data("=MODE.SNGL(A1:A4)")).to_equal(_eval_data("=MODE(A1:A4)"))
```

</details>

#### rank/quantile aliases match their legacy base

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_data("=RANK.EQ(20, A1:A4)")).to_equal(_eval_data("=RANK(20, A1:A4)"))
expect(_eval_data("=QUARTILE.INC(A1:A4, 1)")).to_equal(_eval_data("=QUARTILE(A1:A4, 1)"))
expect(_eval_data("=PERCENTILE.INC(A1:A4, 0.25)")).to_equal(_eval_data("=PERCENTILE(A1:A4, 0.25)"))
expect(_eval_data("=PERCENTRANK.INC(A1:A4, 20)")).to_equal(_eval_data("=PERCENTRANK(A1:A4, 20)"))
```

</details>

#### covariance alias matches on two ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_data("=COVARIANCE.P(A1:A4, C1:C4)")).to_equal(_eval_data("=COVAR(A1:A4, C1:C4)"))
```

</details>

#### distribution aliases match their legacy base

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_data("=FORECAST.LINEAR(5, A1:A4, C1:C4)")).to_equal(_eval_data("=FORECAST(5, A1:A4, C1:C4)"))
expect(_eval("=NORMSINV(0.975)")).to_equal(_eval("=NORM.S.INV(0.975)"))
expect(_eval("=NORMINV(0.975, 10, 2)")).to_equal(_eval("=NORM.INV(0.975, 10, 2)"))
```

</details>

### Calc dotted names with genuinely-new semantics

#### RANK.AVG averages tied ranks (descending default)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [10,20,20,30]: 20 ranks EQ=2, tie group of 2 -> avg (2+3)/2 = 2.5
expect(_eval_data("=RANK.AVG(20, A1:A4)")).to_equal("2.5")
# 10 is the smallest -> rank 4 descending; 30 the largest -> rank 1
expect(_eval_data("=RANK.AVG(10, A1:A4)")).to_equal("4")
expect(_eval_data("=RANK.AVG(30, A1:A4)")).to_equal("1")
```

</details>

#### CEILING.MATH / FLOOR.MATH follow Excel-2013 negative + mode rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CEILING.MATH(-5.5)")).to_equal("-5")
expect(_eval("=FLOOR.MATH(-5.5)")).to_equal("-6")
expect(_eval("=CEILING.MATH(-5.5, 2, 1)")).to_equal("-6")
expect(_eval("=FLOOR.MATH(-5.5, 2, 1)")).to_equal("-4")
expect(_eval("=CEILING.MATH(6.7, 2)")).to_equal("8")
```

</details>

#### CEILING.PRECISE / ISO.CEILING / FLOOR.PRECISE always round toward +/-inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CEILING.PRECISE(-4.1)")).to_equal("-4")
expect(_eval("=ISO.CEILING(-4.1)")).to_equal("-4")
expect(_eval("=FLOOR.PRECISE(-4.1)")).to_equal("-5")
```

</details>

#### NORM.S.INV and NORM.INV expose the Acklam inverse-normal helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NORM.S.INV(0.975)")).to_start_with("1.95996")
expect(_eval("=NORM.INV(0.975, 10, 2)")).to_start_with("13.91992")
```

</details>

#### new-semantics domains fail closed with #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NORM.S.INV(0)")).to_contain("#ERR")
expect(_eval("=NORM.INV(0.5, 0, 0)")).to_contain("#ERR")
```

</details>

### Dotted-name tokenization proof

#### mixes dotted and legacy calls in a single expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
