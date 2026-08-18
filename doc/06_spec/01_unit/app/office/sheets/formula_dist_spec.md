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
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc statistical distributions + DATEVALUE spec (136 total).

NORMSDIST uses Abramowitz-Stegun erf (|err| < 1.5e-7) — verified at the
textbook 1.96 -> 0.975 point; BINOMDIST exact on fair-coin cases; POISSON and
EXPONDIST against closed-form references; DATEVALUE parses ISO and US forms
into the same serial as DATE.

## Scenarios

### Calc distributions

#### NORMSDIST matches textbook points

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NORMSDIST(0)")).to_start_with("0.5000000")
expect(_eval("=NORMSDIST(1.96)")).to_start_with("0.97500")
```

</details>

#### BINOMDIST is exact on fair coins; POISSON and EXPONDIST match closed forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BINOMDIST(2, 5, 0.5, FALSE())")).to_equal("0.3125")
expect(_eval("=POISSON(2, 3, FALSE())")).to_start_with("0.22404")
expect(_eval("=EXPONDIST(1, 1, TRUE())")).to_start_with("0.63212")
```

</details>

#### cumulative flags switch pdf/cdf and domains fail closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NORMDIST(3, 3, 1, TRUE())")).to_start_with("0.5000000")
expect(_eval("=BINOMDIST(2, 5, 0.5, TRUE())")).to_equal("0.5")
expect(_eval("=NORMDIST(1, 0, 0, TRUE())")).to_contain("#ERR")
```

</details>

### Calc DATEVALUE

#### parses ISO and US date text to the DATE serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
