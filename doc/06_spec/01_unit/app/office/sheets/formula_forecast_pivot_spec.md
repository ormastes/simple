# formula_forecast_pivot_spec

> Purpose and audience: spreadsheet-engine evidence for Office Calc

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_forecast_pivot_spec

Purpose and audience: spreadsheet-engine evidence for Office Calc

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_forecast_pivot_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: spreadsheet-engine evidence for Office Calc
engineers covering FORECAST.ETS seasonality detection, TREND/LINEST
prediction, and GETPIVOTDATA intersection lookups over rendered pivot
tables, including error propagation into cell display text.

## Scenarios

### FORECAST.ETS

#### detects no seasonality in linear trend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects no seasonality in linear trend


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects no seasonality in linear trend")
# values 10,12,14,16,18,20 on timeline 1..6: trend = 8 + 2t, no seasonality
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS(8, A1:A6, B1:B6)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("24")
```

</details>

#### predicts with zero residuals at t=8

- predicts with zero residuals at t=8


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("predicts with zero residuals at t=8")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS(8, A1:A6, B1:B6)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("24")
```

</details>

#### detects seasonality period=2 in alternating pattern

- detects seasonality period=2 in alternating pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects seasonality period=2 in alternating pattern")
# values 5,9,5,9,5,9,5,9 on timeline 1..8: period=2
var sh = Sheet.new("f")
sh.set_value("A1", "5")
sh.set_value("A2", "9")
sh.set_value("A3", "5")
sh.set_value("A4", "9")
sh.set_value("A5", "5")
sh.set_value("A6", "9")
sh.set_value("A7", "5")
sh.set_value("A8", "9")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("B7", "7")
sh.set_value("B8", "8")
sh.set_value("Z1", '=FORECAST.ETS(9, A1:A8, B1:B8)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("5")
```

</details>

#### accepts explicit seasonality parameter

- accepts explicit seasonality parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts explicit seasonality parameter")
var sh = Sheet.new("f")
sh.set_value("A1", "5")
sh.set_value("A2", "9")
sh.set_value("A3", "5")
sh.set_value("A4", "9")
sh.set_value("A5", "5")
sh.set_value("A6", "9")
sh.set_value("A7", "5")
sh.set_value("A8", "9")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("B7", "7")
sh.set_value("B8", "8")
sh.set_value("Z1", '=FORECAST.ETS(9, A1:A8, B1:B8, 2)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("5")
```

</details>

#### errors on mismatched values and timeline

- errors on mismatched values and timeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("errors on mismatched values and timeline")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("Z1", '=FORECAST.ETS(8, A1:A3, B1:B4)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_contain("#ERR")
```

</details>

#### errors on insufficient data

- errors on insufficient data


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("errors on insufficient data")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("B1", "1")
sh.set_value("Z1", '=FORECAST.ETS(5, A1:A1, B1:B1)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_contain("#ERR")
```

</details>

### FORECAST.ETS.CONFINT

#### returns 0 for zero residuals

- returns 0 for zero residuals


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns 0 for zero residuals")
# Linear fit with no residuals: confint = z * 0 = 0
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.CONFINT(8, A1:A6, B1:B6, 0.95)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("0")
```

</details>

#### supports confidence 0.90

- supports confidence 0.90


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("supports confidence 0.90")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.CONFINT(8, A1:A6, B1:B6, 0.90)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("0")
```

</details>

#### errors on unsupported confidence

- errors on unsupported confidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("errors on unsupported confidence")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("Z1", '=FORECAST.ETS.CONFINT(8, A1:A3, B1:B3, 0.85)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_contain("#ERR")
```

</details>

#### defaults to 0.95 confidence

- defaults to 0.95 confidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults to 0.95 confidence")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.CONFINT(8, A1:A6, B1:B6)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("0")
```

</details>

### FORECAST.ETS.SEASONALITY

#### returns 0 for linear data

- returns 0 for linear data
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns 0 for linear data")
# 10,12,14,16,18,20 has no seasonality
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.SEASONALITY(A1:A6, B1:B6)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("0")
```

</details>

#### detects period=2 in alternating pattern

- detects period=2 in alternating pattern
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("detects period=2 in alternating pattern")
# 5,9,5,9,5,9,5,9 should detect seasonality=2
var sh = Sheet.new("f")
sh.set_value("A1", "5")
sh.set_value("A2", "9")
sh.set_value("A3", "5")
sh.set_value("A4", "9")
sh.set_value("A5", "5")
sh.set_value("A6", "9")
sh.set_value("A7", "5")
sh.set_value("A8", "9")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("B7", "7")
sh.set_value("B8", "8")
sh.set_value("Z1", '=FORECAST.ETS.SEASONALITY(A1:A8, B1:B8)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("2")
```

</details>

#### errors on insufficient data

- errors on insufficient data


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("errors on insufficient data")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("Z1", '=FORECAST.ETS.SEASONALITY(A1:A2, B1:B2)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_contain("#ERR")
```

</details>

### FORECAST.ETS.STAT

#### returns 0 for alpha parameter (type 1)

- returns 0 for alpha parameter (type 1)
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns 0 for alpha parameter (type 1)")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.STAT(A1:A6, B1:B6, 1)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("0")
```

</details>

#### returns 0 for beta parameter (type 2)

- returns 0 for beta parameter (type 2)
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns 0 for beta parameter (type 2)")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.STAT(A1:A6, B1:B6, 2)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("0")
```

</details>

#### returns 0 for gamma parameter (type 3)

- returns 0 for gamma parameter (type 3)
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns 0 for gamma parameter (type 3)")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.STAT(A1:A6, B1:B6, 3)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("0")
```

</details>

#### returns step size (type 8)

- returns step size (type 8)
   - Expected: cell_display_text(sh.get_cell("Z1")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns step size (type 8)")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.STAT(A1:A6, B1:B6, 8)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("1")
```

</details>

#### returns RMSE (type 7) = 0 for perfect fit

- returns RMSE (type 7) = 0 for perfect fit


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns RMSE (type 7) = 0 for perfect fit")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.STAT(A1:A6, B1:B6, 7)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("0")
```

</details>

#### returns MAE (type 6) = 0 for perfect fit

- returns MAE (type 6) = 0 for perfect fit


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns MAE (type 6) = 0 for perfect fit")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("A4", "16")
sh.set_value("A5", "18")
sh.set_value("A6", "20")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("B4", "4")
sh.set_value("B5", "5")
sh.set_value("B6", "6")
sh.set_value("Z1", '=FORECAST.ETS.STAT(A1:A6, B1:B6, 6)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_start_with("0")
```

</details>

#### errors on unsupported type

- errors on unsupported type


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("errors on unsupported type")
var sh = Sheet.new("f")
sh.set_value("A1", "10")
sh.set_value("A2", "12")
sh.set_value("A3", "14")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("B3", "3")
sh.set_value("Z1", '=FORECAST.ETS.STAT(A1:A3, B1:B3, 99)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_contain("#ERR")
```

</details>

### GETPIVOTDATA

#### returns grand total with no field/item pairs

- returns grand total with no field/item pairs
   - Expected: cell_display_text(sh.get_cell("D1")) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns grand total with no field/item pairs")
var sh = Sheet.new("pivot_test")
# Build a simple pivot: Region/Product/Amount
# East, A, 10; East, B, 20; West, A, 30; West, B, 40
sh.set_value("A1", "Region")
sh.set_value("B1", "Product")
sh.set_value("C1", "Amount")
sh.set_value("A2", "East")
sh.set_value("B2", "A")
sh.set_value("C2", "10")
sh.set_value("A3", "East")
sh.set_value("B3", "B")
sh.set_value("C3", "20")
sh.set_value("A4", "West")
sh.set_value("B4", "A")
sh.set_value("C4", "30")
sh.set_value("A5", "West")
sh.set_value("B5", "B")
sh.set_value("C5", "40")

# Create pivot: rows by Region, cols by Product, values are Amount (SUM)
val pivot_grid = pivot_build(sh, "A1:C5", 0, 1, 2, "sum")
# Render the pivot INTO the same sheet, offset to start at E1, so the
# source table at A1:C5 survives alongside it (pivot_to_sheet always
# renders at A1 into a brand-new sheet, which would both discard the
# source data and place the grid under A1 instead of E1 — inlined
# here to keep both, per the "no 2D array params into helpers" rule).
var pr = 0
while pr < pivot_grid.len():
    val prow = pivot_grid[pr]
    var pc = 0
    while pc < prow.len():
        val letter = _pivot_col_letter(pc)
        # Overwrite the structural top-left header cell ("Row/Col")
        # with the real value-field name so GETPIVOTDATA can
        # validate data_field against it (bug:
        # getpivotdata_data_field_not_validated_2026-07-04.md).
        val cell_text = if pr == 0 and pc == 0: "Amount" else: prow[pc]
        sh.set_value("{letter}{pr + 1}", cell_text)
        pc = pc + 1
    pr = pr + 1

# Now test GETPIVOTDATA on the rendered pivot
sh.set_value("D1", '=GETPIVOTDATA("Amount", E1)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("100")
```

</details>

#### returns row total for one field/item pair

- returns row total for one field/item pair
   - Expected: cell_display_text(sh.get_cell("D1")) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns row total for one field/item pair")
var sh = Sheet.new("pivot_test2")
sh.set_value("A1", "Region")
sh.set_value("B1", "Product")
sh.set_value("C1", "Amount")
sh.set_value("A2", "East")
sh.set_value("B2", "A")
sh.set_value("C2", "10")
sh.set_value("A3", "East")
sh.set_value("B3", "B")
sh.set_value("C3", "20")
sh.set_value("A4", "West")
sh.set_value("B4", "A")
sh.set_value("C4", "30")
sh.set_value("A5", "West")
sh.set_value("B5", "B")
sh.set_value("C5", "40")

val pivot_grid = pivot_build(sh, "A1:C5", 0, 1, 2, "sum")
var pr = 0
while pr < pivot_grid.len():
    val prow = pivot_grid[pr]
    var pc = 0
    while pc < prow.len():
        val letter = _pivot_col_letter(pc)
        # Overwrite the structural top-left header cell ("Row/Col")
        # with the real value-field name so GETPIVOTDATA can
        # validate data_field against it (bug:
        # getpivotdata_data_field_not_validated_2026-07-04.md).
        val cell_text = if pr == 0 and pc == 0: "Amount" else: prow[pc]
        sh.set_value("{letter}{pr + 1}", cell_text)
        pc = pc + 1
    pr = pr + 1

# East row total should be 30
sh.set_value("D1", '=GETPIVOTDATA("Amount", E1, "Region", "East")')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("30")
```

</details>

#### returns intersection for two field/item pairs

- returns intersection for two field/item pairs
   - Expected: cell_display_text(sh.get_cell("D1")) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns intersection for two field/item pairs")
var sh = Sheet.new("pivot_test3")
sh.set_value("A1", "Region")
sh.set_value("B1", "Product")
sh.set_value("C1", "Amount")
sh.set_value("A2", "East")
sh.set_value("B2", "A")
sh.set_value("C2", "10")
sh.set_value("A3", "East")
sh.set_value("B3", "B")
sh.set_value("C3", "20")
sh.set_value("A4", "West")
sh.set_value("B4", "A")
sh.set_value("C4", "30")
sh.set_value("A5", "West")
sh.set_value("B5", "B")
sh.set_value("C5", "40")

val pivot_grid = pivot_build(sh, "A1:C5", 0, 1, 2, "sum")
var pr = 0
while pr < pivot_grid.len():
    val prow = pivot_grid[pr]
    var pc = 0
    while pc < prow.len():
        val letter = _pivot_col_letter(pc)
        # Overwrite the structural top-left header cell ("Row/Col")
        # with the real value-field name so GETPIVOTDATA can
        # validate data_field against it (bug:
        # getpivotdata_data_field_not_validated_2026-07-04.md).
        val cell_text = if pr == 0 and pc == 0: "Amount" else: prow[pc]
        sh.set_value("{letter}{pr + 1}", cell_text)
        pc = pc + 1
    pr = pr + 1

# East + A intersection should be 10
sh.set_value("D1", '=GETPIVOTDATA("Amount", E1, "Region", "East", "Product", "A")')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("10")
```

</details>

#### errors on field/item not found

- errors on field/item not found


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("errors on field/item not found")
var sh = Sheet.new("pivot_test4")
sh.set_value("A1", "Region")
sh.set_value("B1", "Product")
sh.set_value("C1", "Amount")
sh.set_value("A2", "East")
sh.set_value("B2", "A")
sh.set_value("C2", "10")

val pivot_grid = pivot_build(sh, "A1:C2", 0, 1, 2, "sum")
var pr = 0
while pr < pivot_grid.len():
    val prow = pivot_grid[pr]
    var pc = 0
    while pc < prow.len():
        val letter = _pivot_col_letter(pc)
        # Overwrite the structural top-left header cell ("Row/Col")
        # with the real value-field name so GETPIVOTDATA can
        # validate data_field against it (bug:
        # getpivotdata_data_field_not_validated_2026-07-04.md).
        val cell_text = if pr == 0 and pc == 0: "Amount" else: prow[pc]
        sh.set_value("{letter}{pr + 1}", cell_text)
        pc = pc + 1
    pr = pr + 1

# Request non-existent region
sh.set_value("D1", '=GETPIVOTDATA("Amount", E1, "Region", "North")')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_contain("#ERR")
```

</details>

#### errors on unknown data_field instead of returning the grand total

- errors on unknown data_field instead of returning the grand total
   - Expected: cell_display_text(sh.get_cell("D2")) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("errors on unknown data_field instead of returning the grand total")
var sh = Sheet.new("pivot_test5")
sh.set_value("A1", "Region")
sh.set_value("B1", "Product")
sh.set_value("C1", "Amount")
sh.set_value("A2", "East")
sh.set_value("B2", "A")
sh.set_value("C2", "10")
sh.set_value("A3", "East")
sh.set_value("B3", "B")
sh.set_value("C3", "20")
sh.set_value("A4", "West")
sh.set_value("B4", "A")
sh.set_value("C4", "30")
sh.set_value("A5", "West")
sh.set_value("B5", "B")
sh.set_value("C5", "40")

val pivot_grid = pivot_build(sh, "A1:C5", 0, 1, 2, "sum")
var pr = 0
while pr < pivot_grid.len():
    val prow = pivot_grid[pr]
    var pc = 0
    while pc < prow.len():
        val letter = _pivot_col_letter(pc)
        val cell_text = if pr == 0 and pc == 0: "Amount" else: prow[pc]
        sh.set_value("{letter}{pr + 1}", cell_text)
        pc = pc + 1
    pr = pr + 1

# Grand total (for reference) is 100, but "NoSuchField" is not the
# pivot's value field -- must #ERR, never silently fall back to it.
sh.set_value("D1", '=GETPIVOTDATA("NoSuchField", E1)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_contain("#ERR")
# A case-insensitive match on the real field still works.
sh.set_value("D2", '=GETPIVOTDATA("amount", E1)')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D2"))).to_equal("100")
```

</details>

#### returns intersection on the second value column of a wider cross-tab

- returns intersection on the second value column of a wider cross-tab
   - Expected: cell_display_text(sh.get_cell("D1")) equals `20`
   - Expected: cell_display_text(sh.get_cell("D2")) equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns intersection on the second value column of a wider cross-tab")
var sh = Sheet.new("pivot_test6")
sh.set_value("A1", "Region")
sh.set_value("B1", "Product")
sh.set_value("C1", "Amount")
sh.set_value("A2", "East")
sh.set_value("B2", "A")
sh.set_value("C2", "10")
sh.set_value("A3", "East")
sh.set_value("B3", "B")
sh.set_value("C3", "20")
sh.set_value("A4", "East")
sh.set_value("B4", "C")
sh.set_value("C4", "5")
sh.set_value("A5", "West")
sh.set_value("B5", "A")
sh.set_value("C5", "30")
sh.set_value("A6", "West")
sh.set_value("B6", "B")
sh.set_value("C6", "40")
sh.set_value("A7", "West")
sh.set_value("B7", "C")
sh.set_value("C7", "15")

# 3 product columns (A, B, C) push the rendered grid to E:I --
# beyond the old E-H cap this spec's render helper used to clobber.
val pivot_grid = pivot_build(sh, "A1:C7", 0, 1, 2, "sum")
var pr = 0
while pr < pivot_grid.len():
    val prow = pivot_grid[pr]
    var pc = 0
    while pc < prow.len():
        val letter = _pivot_col_letter(pc)
        val cell_text = if pr == 0 and pc == 0: "Amount" else: prow[pc]
        sh.set_value("{letter}{pr + 1}", cell_text)
        pc = pc + 1
    pr = pr + 1

# Header row E1:I1 = Amount, A, B, C, Grand Total. Second value
# column (Product B) intersected with East = 20.
sh.set_value("D1", '=GETPIVOTDATA("Amount", E1, "Region", "East", "Product", "B")')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("20")
# And West/B = 40, to pin down the column isn't just falling
# through to the first data column.
sh.set_value("D2", '=GETPIVOTDATA("Amount", E1, "Region", "West", "Product", "B")')
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D2"))).to_equal("40")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f661bd74cb94b481f509f86452da9ab8fa5e7a4a3fbe9638c5a5f4dab508700f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f661bd74cb94b481f509f86452da9ab8fa5e7a4a3fbe9638c5a5f4dab508700f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f661bd74cb94b481f509f86452da9ab8fa5e7a4a3fbe9638c5a5f4dab508700f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_forecast_pivot_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_forecast_pivot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_forecast_pivot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_forecast_pivot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_forecast_pivot_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects no seasonality in linear trend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_forecast_pivot_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'predicts with zero residuals at t=8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_forecast_pivot_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects seasonality period=2 in alternating pattern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
