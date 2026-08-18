# formula_lambda_helpers_spec

> Calc lambda helper functions: MAP, REDUCE, SCAN, BYROW, BYCOL, MAKEARRAY, ISOMITTED.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_lambda_helpers_spec

Calc lambda helper functions: MAP, REDUCE, SCAN, BYROW, BYCOL, MAKEARRAY, ISOMITTED.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_lambda_helpers_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc lambda helper functions: MAP, REDUCE, SCAN, BYROW, BYCOL, MAKEARRAY, ISOMITTED.

These functions enable higher-order array operations via immediate LAMBDA invocation.
Ground truths computed by hand and verified against expected math.

## Scenarios

### MAP basic

#### MAP(1:3, LAMBDA(x, x*2)) with A1:A3=[1,2,3] spills to C1:C3

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("C1", "=MAP(A1:A3, LAMBDA(x, x*2))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C1"))).to_equal("2")
expect(cell_display_text(sh.get_cell("C2"))).to_equal("4")
expect(cell_display_text(sh.get_cell("C3"))).to_equal("6")
```

</details>

#### MAP with string transformation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "hello")
sh.set_value("A2", "world")
sh.set_value("C1", "=MAP(A1:A2, LAMBDA(x, UPPER(x)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C1"))).to_equal("HELLO")
expect(cell_display_text(sh.get_cell("C2"))).to_equal("WORLD")
```

</details>

### REDUCE basic

#### REDUCE(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("Z1", "=REDUCE(0, A1:A3, LAMBDA(a, b, a+b))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("6")
```

</details>

#### REDUCE(10, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] = 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("Z1", "=REDUCE(10, A1:A3, LAMBDA(a, b, a+b))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("16")
```

</details>

### SCAN basic

#### SCAN(0, A1:A3, LAMBDA(a, b, a+b)) with [1,2,3] spills [1,3,6]

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("C1", "=SCAN(0, A1:A3, LAMBDA(a, b, a+b))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C1"))).to_equal("1")
expect(cell_display_text(sh.get_cell("C2"))).to_equal("3")
expect(cell_display_text(sh.get_cell("C3"))).to_equal("6")
```

</details>

### BYROW basic

#### BYROW(A1:B2, LAMBDA(r, SUM(r))) with [[1,2],[3,4]] spills [3,7] down

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("B1", "2")
sh.set_value("A2", "3")
sh.set_value("B2", "4")
sh.set_value("D1", "=BYROW(A1:B2, LAMBDA(r, SUM(r)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("3")
expect(cell_display_text(sh.get_cell("D2"))).to_equal("7")
```

</details>

#### BYROW(A1:B2, LAMBDA(r, PRODUCT(r))) with [[1,2],[3,4]] spills [2,12] down (general F(r) body, not just AGG)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("B1", "2")
sh.set_value("A2", "3")
sh.set_value("B2", "4")
sh.set_value("D1", "=BYROW(A1:B2, LAMBDA(r, PRODUCT(r)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("2")
expect(cell_display_text(sh.get_cell("D2"))).to_equal("12")
```

</details>

### BYCOL basic

#### BYCOL(A1:B2, LAMBDA(c, SUM(c))) with [[1,2],[3,4]] spills [4,6] across

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("B1", "2")
sh.set_value("A2", "3")
sh.set_value("B2", "4")
sh.set_value("D1", "=BYCOL(A1:B2, LAMBDA(c, SUM(c)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("4")
expect(cell_display_text(sh.get_cell("E1"))).to_equal("6")
```

</details>

#### BYCOL(A1:B2, LAMBDA(c, MEDIAN(c))) with [[1,2],[3,4]] spills [2,3] across (general F(c) body, not just AGG)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("B1", "2")
sh.set_value("A2", "3")
sh.set_value("B2", "4")
sh.set_value("D1", "=BYCOL(A1:B2, LAMBDA(c, MEDIAN(c)))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("D1"))).to_equal("2")
expect(cell_display_text(sh.get_cell("E1"))).to_equal("3")
```

</details>

### MAKEARRAY basic

#### MAKEARRAY(2, 3, LAMBDA(r, c, r*c)) spills [[1,2,3],[2,4,6]]

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("C1", "=MAKEARRAY(2, 3, LAMBDA(r, c, r*c))")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("C1"))).to_equal("1")
expect(cell_display_text(sh.get_cell("D1"))).to_equal("2")
expect(cell_display_text(sh.get_cell("E1"))).to_equal("3")
expect(cell_display_text(sh.get_cell("C2"))).to_equal("2")
expect(cell_display_text(sh.get_cell("D2"))).to_equal("4")
expect(cell_display_text(sh.get_cell("E2"))).to_equal("6")
```

</details>

### ISOMITTED basic

#### LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5) = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("Z1", "=LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("5")
```

</details>

#### LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5, 3) = 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("Z1", "=LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5, 3)")
sh = recalculate_formula_cells(sh)
expect(cell_display_text(sh.get_cell("Z1"))).to_equal("8")
```

</details>

### Error domains

#### MAP without LAMBDA argument returns #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("Z1", "=MAP(A1, 42)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("Z1"))
assert_true(result.starts_with("#"))
```

</details>

#### REDUCE with no range returns #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("Z1", "=REDUCE(0, \"\", LAMBDA(a, b, a+b))")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("Z1"))
assert_true(result.starts_with("#"))
```

</details>

#### MAKEARRAY with negative rows returns #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ground-truth correction: Excel's MAKEARRAY raises #CALC! for
# rows < 1 (rows/cols must be positive integers) — it does NOT
# silently return empty. This evaluator's array-path fails closed
# ([]) for rows<1, which falls back to the scalar dispatch and
# naturally yields "#ERR: Unknown function: MAKEARRAY" (the same
# fallback every array-only function gets on a malformed call).
var sh = Sheet.new("f")
sh.set_value("Z1", "=MAKEARRAY(-1, 2, LAMBDA(r, c, r))")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("Z1"))
assert_true(result.starts_with("#"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
