# formula_math_spec

> Calc math/engineering functions spec — 15 additions toward Excel's set.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_math_spec

Calc math/engineering functions spec — 15 additions toward Excel's set.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_math_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc math/engineering functions spec — 15 additions toward Excel's set.

EXP/LN/LOG10 use pure-Simple series implementations; verified against known
values. GCD/LCM/FACT are integer-exact; EVEN/ODD/ROUNDUP round away from zero.

## Scenarios

### Calc math functions

#### EXP/LN/LOG10 match known values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=EXP(1)")).to_start_with("2.71828")
expect(_eval("=LN(2.718281828459045)")).to_equal("1")
expect(_eval("=LOG10(1000)")).to_equal("3")
```

</details>

#### PI/DEGREES/RADIANS convert angles

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DEGREES(PI())")).to_equal("180")
expect(_eval("=RADIANS(180)")).to_start_with("3.14159")
```

</details>

#### FACT/GCD/LCM are integer-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=FACT(5)")).to_equal("120")
expect(_eval("=GCD(12, 18)")).to_equal("6")
expect(_eval("=LCM(4, 6)")).to_equal("12")
```

</details>

#### SUMSQ/AVEDEV aggregate ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SUMSQ(A1:A2)")).to_equal("25")
expect(_eval("=AVEDEV(A1:A2)")).to_equal("0.5")
```

</details>

#### EVEN/ODD/ROUNDUP/ROUNDDOWN round correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=EVEN(3.1)")).to_equal("4")
expect(_eval("=ODD(4)")).to_equal("5")
expect(_eval("=ROUNDUP(2.1)")).to_equal("3")
expect(_eval("=ROUNDDOWN(2.9)")).to_equal("2")
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
