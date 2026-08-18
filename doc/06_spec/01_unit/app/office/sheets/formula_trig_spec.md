# formula_trig_spec

> Calc trigonometry/combinatorics spec — 15 additions (65 functions total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_trig_spec

Calc trigonometry/combinatorics spec — 15 additions (65 functions total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_trig_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc trigonometry/combinatorics spec — 15 additions (65 functions total).

SIN/COS/TAN/ASIN/ACOS/ATAN use pure-Simple series with range reduction;
verified against exact identities. Hyperbolics build on the EXP series.

## Scenarios

### Calc trigonometry

#### SIN/COS/TAN match identities

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SIN(PI() / 2)")).to_start_with("1")
expect(_eval("=COS(0)")).to_start_with("1")
expect(_eval("=TAN(PI() / 4)")).to_start_with("0.9999")
```

</details>

#### inverse functions return known angles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ATAN(1)")).to_start_with("0.78539")
expect(_eval("=ASIN(0.5)")).to_start_with("0.52359")
expect(_eval("=ACOS(0)")).to_start_with("1.57079")
```

</details>

#### hyperbolics build on EXP

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SINH(1)")).to_start_with("1.17520")
expect(_eval("=TANH(0)")).to_equal("0")
```

</details>

### Calc combinatorics and rounding

#### LOG with base, COMBIN, PERMUT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LOG(8, 2)")).to_equal("3")
expect(_eval("=COMBIN(5, 2)")).to_equal("10")
expect(_eval("=PERMUT(5, 2)")).to_equal("20")
```

</details>

#### QUOTIENT, MROUND, SQRTPI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=QUOTIENT(17, 5)")).to_equal("3")
expect(_eval("=MROUND(13, 5)")).to_equal("15")
expect(_eval("=SQRTPI(1)")).to_start_with("1.77245")
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
