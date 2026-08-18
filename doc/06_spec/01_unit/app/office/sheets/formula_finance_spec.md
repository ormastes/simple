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
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc regression + financial functions spec — 20 additions (99 total).

SLOPE/INTERCEPT/CORREL/RSQ verified on an exact linear series; PMT/NPV/NPER
match Excel's closed forms; inverse-hyperbolics build on the LN series.

## Scenarios

### Calc regression pack

#### fits the exact line y = 2x

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SLOPE(B1:B3, A1:A3)")).to_equal("2")
expect(_eval("=INTERCEPT(B1:B3, A1:A3)")).to_equal("0")
expect(_eval("=CORREL(A1:A3, B1:B3)")).to_equal("1")
expect(_eval("=RSQ(A1:A3, B1:B3)")).to_equal("1")
```

</details>

#### population statistics use the n denominator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=STDEVP(A1:A3)")).to_start_with("0.81649")
expect(_eval("=VARP(A1:A3)")).to_start_with("0.66666")
expect(_eval("=DEVSQ(A1:A3)")).to_equal("2")
```

</details>

### Calc financial pack

#### PMT matches Excel's annuity formula

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PMT(0.01, 60, 10000)")).to_start_with("-222.444")
```

</details>

#### NPV discounts each period and NPER inverts the annuity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NPV(0.1, B1:B3)")).to_start_with("9.6318")
expect(_eval("=NPER(0.01, -100, 1000)")).to_start_with("10.588")
```

</details>

### Calc inverse trig/hyperbolic

#### ATAN2 handles quadrants, ATANH matches Fisher

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
