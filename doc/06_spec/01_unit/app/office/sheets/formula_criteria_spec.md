# formula_criteria_spec

> Calc criteria functions spec — COUNTIF/SUMIF/AVERAGEIF (102 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_criteria_spec

Calc criteria functions spec — COUNTIF/SUMIF/AVERAGEIF (102 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_criteria_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc criteria functions spec — COUNTIF/SUMIF/AVERAGEIF (102 total).

Excel-style criteria: comparison operators parse numerically; bare values
compare case-insensitively as text; SUMIF takes an optional parallel sum
range; AVERAGEIF fails closed on zero matches.

## Scenarios

### Calc criteria functions

#### COUNTIF counts text equality and numeric comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=COUNTIF(A1:A3, \"apple\")")).to_equal("2")
expect(_eval("=COUNTIF(A1:A3, \"APPLE\")")).to_equal("2")
expect(_eval("=COUNTIF(B1:B3, \">15\")")).to_equal("2")
expect(_eval("=COUNTIF(B1:B3, \"<=10\")")).to_equal("1")
```

</details>

#### SUMIF sums the parallel range where criteria match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SUMIF(A1:A3, \"apple\", B1:B3)")).to_equal("40")
expect(_eval("=SUMIF(B1:B3, \">=20\")")).to_equal("50")
expect(_eval("=SUMIF(A1:A3, \"<>apple\", B1:B3)")).to_equal("20")
```

</details>

#### AVERAGEIF averages matches and fails closed on none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=AVERAGEIF(B1:B3, \"<>20\")")).to_equal("20")
expect(_eval("=AVERAGEIF(B1:B3, \">99\")")).to_contain("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
