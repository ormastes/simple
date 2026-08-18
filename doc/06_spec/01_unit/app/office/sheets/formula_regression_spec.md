# formula_regression_spec

> Calc regression spec for LINEST, TREND, GROWTH, PROB, RANDARRAY.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_regression_spec

Calc regression spec for LINEST, TREND, GROWTH, PROB, RANDARRAY.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_regression_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc regression spec for LINEST, TREND, GROWTH, PROB, RANDARRAY.

LINEST(known_ys, [known_xs]) -> [slope, intercept] spilled horizontally.
Least-squares linear regression: y = slope*x + intercept.
known_xs defaults to 1,2,...,n if omitted.

TREND(known_ys, [known_xs], [new_xs]) -> predicted values via linear fit.
Fits via LINEST, predicts y = slope*x + intercept at new_xs.
new_xs defaults to known_xs if omitted.

GROWTH(known_ys, [known_xs], [new_xs]) -> exponential predictions.
Fits ln(y) linearly, predicts exp(slope*x + intercept).
All y must be > 0.

PROB(x_range, prob_range, lower_limit, [upper_limit]) -> sum of probabilities.
Sums P(x) where lower ≤ x ≤ upper (upper omitted → x == lower exactly).
All probs must be in [0,1], sum must equal 1 (within 1e-9).

RANDARRAY([rows], [cols], [min], [max], [integer]) -> random array.
Defaults: rows=1, cols=1, min=0, max=1, integer=FALSE.
Spills a grid of random values.

Ground truths (hand-computed):
- x=[1..5], y=[3,5,7,10,12]: x̄=3, ȳ=7.4, Σ(x-x̄)(y-ȳ)=23, Σ(x-x̄)²=10
  → slope=2.3, intercept=0.5
- TREND([3,5,7,10,12],[1,2,3,4,5],6) = 2.3*6+0.5 = 14.3
- y=[2,4,8,16], x=[1..4]: ln(y)=[ln(2), 2ln(2), 3ln(2), 4ln(2)] = linear with m=ln(2), b=0
  → GROWTH at x=5 = exp(ln(2)*5) = 2^5 = 32
- PROB([0,1,2,3], [0.2,0.3,0.1,0.4], 1, 3) = 0.3+0.1+0.4 = 0.8
- PROB([0,1,2,3], [0.2,0.3,0.1,0.4], 2, 2) = 0.1

## Scenarios

### LINEST

#### LINEST: basic slope and intercept

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("D1", "=LINEST(A1:A5, B1:B5)")
sh = recalculate_formula_cells(sh)
val slope = cell_display_text(sh.get_cell("D1"))
val intercept = cell_display_text(sh.get_cell("E1"))
expect(slope).to_start_with("2.3")
expect(intercept).to_start_with("0.5")
```

</details>

#### LINEST: omitted known_xs defaults to 1..n

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("D1", "=LINEST(A1:A5)")
sh = recalculate_formula_cells(sh)
val slope = cell_display_text(sh.get_cell("D1"))
val intercept = cell_display_text(sh.get_cell("E1"))
expect(slope).to_start_with("2.3")
expect(intercept).to_start_with("0.5")
```

</details>

#### LINEST: mismatched ranges returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("D1", "=LINEST(A1:A5, B1:B3)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

#### LINEST: n<2 returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "5")
sh.set_value("B1", "1")
sh.set_value("D1", "=LINEST(A1, B1)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

#### LINEST: 2-arg form stays a single row (no stats requested)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("D1", "=LINEST(A1:A5, B1:B5)")
sh = recalculate_formula_cells(sh)
val row2_slope_col = cell_display_text(sh.get_cell("D2"))
expect(row2_slope_col).to_equal("")
```

</details>

#### LINEST: 3-arg form (const) stays a single row

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("D1", "=LINEST(A1:A5, B1:B5, TRUE)")
sh = recalculate_formula_cells(sh)
val slope = cell_display_text(sh.get_cell("D1"))
val intercept = cell_display_text(sh.get_cell("E1"))
val row2 = cell_display_text(sh.get_cell("D2"))
expect(slope).to_start_with("2.3")
expect(intercept).to_start_with("0.5")
expect(row2).to_equal("")
```

</details>

#### LINEST: stats=TRUE spills the 3-row form with hand-verified stats

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# x=1..5, y=[3,5,7,10,12]; hand anchors (doc-verified, see
# writing_calc_functions.md ground-truth discipline):
#   se_y=0.3162278, se_slope=0.1, se_intercept=0.331662,
#   r2=0.9943609
var sh = _setup_linest_data()
sh.set_value("D1", "=LINEST(A1:A5, B1:B5, TRUE, TRUE)")
sh = recalculate_formula_cells(sh)
val slope = cell_display_text(sh.get_cell("D1"))
val intercept = cell_display_text(sh.get_cell("E1"))
val se_slope = cell_display_text(sh.get_cell("D2"))
val se_intercept = cell_display_text(sh.get_cell("E2"))
val r2 = cell_display_text(sh.get_cell("D3"))
val se_y = cell_display_text(sh.get_cell("E3"))
expect(slope).to_start_with("2.3")
expect(intercept).to_start_with("0.5")
expect(se_slope).to_start_with("0.1")
expect(se_intercept).to_start_with("0.331662")
expect(r2).to_start_with("0.994360")
expect(se_y).to_start_with("0.316227")
```

</details>

### TREND

#### TREND: single new_x prediction

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("D1", "=TREND(A1:A5, B1:B5, 6)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_start_with("14.3")
```

</details>

#### TREND: range of new_xs

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("C1", "6")
sh.set_value("C2", "7")
sh.set_value("D1", "=TREND(A1:A5, B1:B5, C1:C2)")
sh = recalculate_formula_cells(sh)
val pred6 = cell_display_text(sh.get_cell("D1")).to_f64()
val pred7 = cell_display_text(sh.get_cell("E1")).to_f64()
expect(pred6).to_be_greater_than(14.2)
expect(pred6).to_be_less_than(14.4)
expect(pred7).to_be_greater_than(16.5)
expect(pred7).to_be_less_than(16.7)
```

</details>

#### TREND: omitted new_xs predicts at known_xs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("D1", "=TREND(A1:A5, B1:B5)")
sh = recalculate_formula_cells(sh)
val pred1 = cell_display_text(sh.get_cell("D1"))
expect(pred1).to_start_with("2.8")
```

</details>

#### TREND: bad fit returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_linest_data()
sh.set_value("D1", "=TREND(A1:A3, B1:B1, 10)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

### GROWTH

#### GROWTH: exponential prediction at single point

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_growth_data()
sh.set_value("D1", "=GROWTH(A1:A4, B1:B4, 5)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1")).to_f64()
expect(result).to_be_greater_than(31.5)
expect(result).to_be_less_than(32.5)
```

</details>

#### GROWTH: range of new_xs

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_growth_data()
sh.set_value("C1", "5")
sh.set_value("C2", "6")
sh.set_value("D1", "=GROWTH(A1:A4, B1:B4, C1:C2)")
sh = recalculate_formula_cells(sh)
val pred5 = cell_display_text(sh.get_cell("D1")).to_f64()
val pred6 = cell_display_text(sh.get_cell("E1")).to_f64()
expect(pred5).to_be_greater_than(31.5)
expect(pred5).to_be_less_than(32.5)
expect(pred6).to_be_greater_than(63.5)
expect(pred6).to_be_less_than(64.5)
```

</details>

#### GROWTH: negative y returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "-2")
sh.set_value("A2", "4")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("D1", "=GROWTH(A1:A2, B1:B2, 3)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

#### GROWTH: zero y returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "0")
sh.set_value("A2", "4")
sh.set_value("B1", "1")
sh.set_value("B2", "2")
sh.set_value("D1", "=GROWTH(A1:A2, B1:B2, 3)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

### PROB

#### PROB: range [lower, upper]

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_prob_data()
sh.set_value("D1", "=PROB(A1:A4, B1:B4, 1, 3)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_start_with("0.8")
```

</details>

#### PROB: single point (upper omitted)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_prob_data()
sh.set_value("D1", "=PROB(A1:A4, B1:B4, 2)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_start_with("0.1")
```

</details>

#### PROB: mismatched ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _setup_prob_data()
sh.set_value("D1", "=PROB(A1:A2, B1:B4, 1)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

#### PROB: probabilities don't sum to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "0")
sh.set_value("A2", "1")
sh.set_value("B1", "0.4")
sh.set_value("B2", "0.4")
sh.set_value("D1", "=PROB(A1:A2, B1:B2, 0, 1)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

#### PROB: probability out of [0,1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "0")
sh.set_value("A2", "1")
sh.set_value("B1", "1.5")
sh.set_value("B2", "0.5")
sh.set_value("D1", "=PROB(A1:A2, B1:B2, 0, 1)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

#### PROB: requires 3+ arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("D1", "=PROB(A1:A2)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

### RANDARRAY

#### RANDARRAY: default 1x1 [0,1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("D1", "=RANDARRAY()")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
val num = result.to_f64()
expect(num).to_be_greater_than(0.0)
expect(num).to_be_less_than(1.0)
```

</details>

#### RANDARRAY: custom dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("D1", "=RANDARRAY(2, 3)")
sh = recalculate_formula_cells(sh)
val r1c1 = cell_display_text(sh.get_cell("D1"))
val r1c2 = cell_display_text(sh.get_cell("E1"))
val r1c3 = cell_display_text(sh.get_cell("F1"))
val r2c1 = cell_display_text(sh.get_cell("D2"))
assert_not_equal(r1c1, "#ERR")
assert_not_equal(r1c2, "#ERR")
assert_not_equal(r1c3, "#ERR")
assert_not_equal(r2c1, "#ERR")
```

</details>

#### RANDARRAY: custom min/max

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("D1", "=RANDARRAY(1, 1, 10, 20)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
val num = result.to_f64()
expect(num).to_be_greater_than(10.0)
expect(num).to_be_less_than(20.0)
```

</details>

#### RANDARRAY: integer mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("D1", "=RANDARRAY(1, 3, 1, 10, TRUE)")
sh = recalculate_formula_cells(sh)
val c1 = cell_display_text(sh.get_cell("D1")).to_f64()
val c2 = cell_display_text(sh.get_cell("E1")).to_f64()
val c3 = cell_display_text(sh.get_cell("F1")).to_f64()
expect(c1).to_equal(c1.to_i64().to_f64())
expect(c2).to_equal(c2.to_i64().to_f64())
expect(c3).to_equal(c3.to_i64().to_f64())
```

</details>

#### RANDARRAY: rows < 1 errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("D1", "=RANDARRAY(0, 1)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

#### RANDARRAY: cols < 1 errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("D1", "=RANDARRAY(1, 0)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

#### RANDARRAY: min > max errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("D1", "=RANDARRAY(1, 1, 20, 10)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("D1"))
expect(result).to_contain("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
