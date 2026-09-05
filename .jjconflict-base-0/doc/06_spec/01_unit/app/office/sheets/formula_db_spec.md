# formula_db_spec

> Calc database functions spec — DSUM family (129 total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_db_spec

Calc database functions spec — DSUM family (129 total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_db_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc database functions spec — DSUM family (129 total).

Excel semantics: database range with a header row, criteria range with
header + condition rows (AND across columns), field by quoted header name or
1-based index. DGET requires exactly one match.

## Scenarios

### Calc database functions

#### aggregates rows matching the criteria range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DSUM(A1:C4, \"Sales\", E1:E2)")).to_equal("150")
expect(_eval("=DCOUNT(A1:C4, \"Sales\", E1:E2)")).to_equal("2")
expect(_eval("=DAVERAGE(A1:C4, 3, E1:E2)")).to_equal("75")
expect(_eval("=DMAX(A1:C4, \"Sales\", E1:E2)")).to_equal("100")
expect(_eval("=DMIN(A1:C4, \"Sales\", E1:E2)")).to_equal("50")
```

</details>

#### ANDs multiple criteria columns and DGET requires a unique match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DSUM(A1:C4, \"Sales\", E1:F2)")).to_equal("100")
expect(_eval("=DGET(A1:C4, \"Name\", E1:F2)")).to_equal("Ann")
expect(_eval("=DGET(A1:C4, \"Name\", E1:E2)")).to_contain("#ERR")
```

</details>

#### fails closed on unknown fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DSUM(A1:C4, \"Bogus\", E1:E2)")).to_contain("#ERR")
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
