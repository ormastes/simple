# formula_text_fmt_spec

> Calc TEXT/FIXED/VALUE formatting spec (140 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_text_fmt_spec

Calc TEXT/FIXED/VALUE formatting spec (140 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_text_fmt_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc TEXT/FIXED/VALUE formatting spec (140 total).

Excel TEXT() format subset: decimal rounding, thousands grouping, percent,
and date patterns — each verified against Excel's exact output.

## Scenarios

### Calc TEXT formatting

#### rounds decimals and groups thousands like Excel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TEXT(1234.567, \"0.00\")")).to_equal("1234.57")
expect(_eval("=TEXT(1234567.891, \"#,##0.00\")")).to_equal("1,234,567.89")
expect(_eval("=TEXT(-1234.5, \"#,##0\")")).to_equal("-1,235")
```

</details>

#### formats percents and dates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TEXT(0.4275, \"0.0%\")")).to_equal("42.8%")
expect(_eval("=TEXT(DATE(2026, 7, 3), \"yyyy-mm-dd\")")).to_equal("2026-07-03")
expect(_eval("=TEXT(DATE(2026, 7, 3), \"mm/dd/yyyy\")")).to_equal("07/03/2026")
```

</details>

#### FIXED groups with chosen decimals; VALUE parses numeric text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=FIXED(1234.567, 1)")).to_equal("1,234.6")
expect(_eval("=VALUE(\"42.5\")")).to_equal("42.5")
expect(_eval("=VALUE(\"42.5\") + 0.5")).to_equal("43")
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
