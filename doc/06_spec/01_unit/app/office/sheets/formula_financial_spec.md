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
| Updated | 2026-08-18 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SLN(30000, 7500, 10)")).to_equal("2250")
expect(_eval("=SYD(30000, 7500, 10, 1)")).to_start_with("4090.909")
expect(_eval("=SYD(30000, 7500, 10, 10)")).to_start_with("409.09")
```

</details>

#### DDB double-declines and clamps at salvage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DDB(2400, 300, 10, 1)")).to_equal("480")
expect(_eval("=DDB(2400, 300, 10, 2)")).to_equal("384")
```

</details>

#### DB uses the 3-decimal fixed-declining rate (full first year)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DB(1000000, 100000, 6, 1)")).to_equal("319000")
```

</details>

#### depreciation fails closed when period exceeds life

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DDB(2400, 300, 10, 11)")).to_contain("#ERR")
expect(_eval("=DB(1000000, 100000, 6, 7)")).to_contain("#ERR")
expect(_eval("=SYD(30000, 7500, 10, 11)")).to_contain("#ERR")
```

</details>

### Calc financial — amortization

#### IPMT is the interest slice, PPMT the principal slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IPMT(0.1/12, 1, 36, 8000)")).to_start_with("-66.666")
expect(_eval("=PPMT(0.1/12, 1, 36, 8000)")).to_start_with("-191.47")
```

</details>

#### CUMIPMT and CUMPRINC accumulate over a period window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CUMIPMT(0.09/12, 360, 125000, 13, 24, 0)")).to_start_with("-11135.23")
expect(_eval("=CUMPRINC(0.09/12, 360, 125000, 13, 24, 0)")).to_start_with("-934.10")
```

</details>

#### ISPMT gives level-principal interest for a period

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISPMT(0.1/12, 1, 36, 8000)")).to_start_with("-64.814")
```

</details>

#### amortization fails closed on an out-of-range period

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IPMT(0.1/12, 40, 36, 8000)")).to_contain("#ERR")
expect(_eval("=CUMIPMT(0.09/12, 360, 125000, 24, 13, 0)")).to_contain("#ERR")
```

</details>

### Calc financial — solvers

#### RATE recovers the periodic rate via Newton's method

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=RATE(48, -200, 8000)")).to_start_with("0.00770")
```

</details>

#### RATE fails closed when the annuity has no root

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=RATE(2, 1000, 1000)")).to_contain("#ERR")
```

</details>

#### IRR solves the NPV = 0 rate over a cashflow range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=IRR(A1:A6)")).to_start_with("0.0866")
```

</details>

#### MIRR blends finance and reinvestment rates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=MIRR(C1:C6, 0.1, 0.12)")).to_start_with("0.12609")
```

</details>

### Calc financial — rate conversions

#### EFFECT and NOMINAL round-trip a compounding rate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=EFFECT(0.0525, 4)")).to_start_with("0.05354")
expect(_eval("=NOMINAL(0.053543, 4)")).to_start_with("0.0525")
```

</details>

#### RRI and PDURATION invert compound growth

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=RRI(96, 10000, 11000)")).to_start_with("0.00099")
expect(_eval("=PDURATION(0.025, 1000, 1500)")).to_start_with("16.42")
```

</details>

#### FVSCHEDULE compounds a principal through a rate range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
