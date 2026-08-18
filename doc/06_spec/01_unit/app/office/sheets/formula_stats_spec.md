# formula_stats_spec

> Calc statistical functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_stats_spec

Calc statistical functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_stats_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc statistical functions spec.

MEDIAN / VAR / STDEV / LARGE / SMALL over ranges, matching Excel semantics
(sample variance, 1-based k). Evaluated through the real recalc path.

## Scenarios

### Calc statistics: MEDIAN/VAR/STDEV

#### computes the median of an even-sized range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _stats_sheet()
sh.set_value("B1", "=MEDIAN(A1:A4)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_equal("7")
```

</details>

#### computes sample variance (n-1) like Excel VAR

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _stats_sheet()
sh.set_value("B1", "=VAR(A1:A4)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_start_with("6.66666")
```

</details>

#### computes STDEV as sqrt of sample variance

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _stats_sheet()
sh.set_value("B1", "=STDEV(A1:A4)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_start_with("2.58198")
```

</details>

### Calc statistics: LARGE/SMALL

#### returns the k-th largest and smallest

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _stats_sheet()
sh.set_value("B1", "=LARGE(A1:A4, 2)")
sh.set_value("B2", "=SMALL(A1:A4, 1)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_equal("8")
expect(cell_display_text(sh.get_cell("B2"))).to_equal("4")
```

</details>

#### fails closed on k out of range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _stats_sheet()
sh.set_value("B1", "=LARGE(A1:A4, 9)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("B1"))).to_contain("#ERR")
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
