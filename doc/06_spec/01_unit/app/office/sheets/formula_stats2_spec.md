# formula_stats2_spec

> Calc statistics batch 2 — 14 additions (79 functions total).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_stats2_spec

Calc statistics batch 2 — 14 additions (79 functions total).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_stats2_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc statistics batch 2 — 14 additions (79 functions total).

GEOMEAN/HARMEAN/FISHER build on the pure LN/EXP series; RANK is descending
1-based; PERCENTILE uses Excel's inclusive linear interpolation; SUMPRODUCT
is pairwise over equal-length ranges.

## Scenarios

### Calc statistics batch 2

#### GEOMEAN/HARMEAN/MODE over ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=GEOMEAN(A1:A4)")).to_start_with("4")
expect(_eval("=HARMEAN(A1, A2)")).to_start_with("2.66666")
expect(_eval("=MODE(A1:A4)")).to_equal("4")
```

</details>

#### RANK descending and PERCENTILE inclusive

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=RANK(4, A1:A4)")).to_equal("2")
expect(_eval("=RANK(8, A1:A4)")).to_equal("1")
expect(_eval("=PERCENTILE(A1:A4, 0.5)")).to_equal("4")
expect(_eval("=PERCENTILE(A1:A4, 1)")).to_equal("8")
```

</details>

#### SUMPRODUCT pairs ranges and fails closed on size mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=SUMPRODUCT(A1:A4, B1:B4)")).to_equal("118")
expect(_eval("=SUMPRODUCT(A1:A2, B1:B4)")).to_contain("#ERR")
```

</details>

#### engineering predicates and Fisher transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISEVEN(4)")).to_equal("TRUE")
expect(_eval("=ISODD(3)")).to_equal("TRUE")
expect(_eval("=DELTA(2, 2)")).to_equal("1")
expect(_eval("=GESTEP(5, 3)")).to_equal("1")
expect(_eval("=FISHER(0.5)")).to_start_with("0.54930")
expect(_eval("=TRUE()")).to_equal("TRUE")
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
