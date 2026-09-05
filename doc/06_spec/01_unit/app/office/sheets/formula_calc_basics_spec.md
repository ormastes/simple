# formula_calc_basics_spec

> Calc formula basics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_calc_basics_spec

Calc formula basics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_calc_basics_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc formula basics.

Proves the ordinary multiplication operator and the compact AVG function
alias through the real spreadsheet formula evaluator.

## Scenarios

### Calc multiplication and AVG

#### recalculates multiplication and both average spellings in a real sheet

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("Calc")
sheet.set_value("A1", "6")
sheet.set_value("A2", "8")
sheet.set_value("B1", "=A1*A2")
sheet.set_value("C1", "=AVG(A1:A2)")
sheet.set_value("D1", "=AVERAGE(A1:A2)")

sheet = recalculate_formula_cells(sheet)

expect(cell_display_text(sheet.get_cell("B1"))).to_equal("48")
expect(cell_display_text(sheet.get_cell("C1"))).to_equal("7")
expect(cell_display_text(sheet.get_cell("D1"))).to_equal("7")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
