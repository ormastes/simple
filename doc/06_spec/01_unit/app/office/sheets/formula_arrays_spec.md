# formula_arrays_spec

> Calc dynamic-array (spill) formulas spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_arrays_spec

Calc dynamic-array (spill) formulas spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_arrays_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc dynamic-array (spill) formulas spec.

Excel-style dynamic arrays: a formula whose result is a 2D range writes its
top-left value in its own cell and spills the rest into the adjacent rectangle.
If a target cell holds a value that is not the one being written, the origin
shows #SPILL! and nothing spills. Recalculation is idempotent (a prior identical
spill never blocks its own origin). Every expected value below is hand-computed.

## Scenarios

### Calc dynamic arrays — spill

#### SEQUENCE(3) spills three rows down

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=SEQUENCE(3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "A3")).to_equal("3")
```

</details>

#### SEQUENCE(2,2,10,5) fills the exact 2x2 grid row-major

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=SEQUENCE(2,2,10,5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("10")
expect(_disp(sh, "B1")).to_equal("15")
expect(_disp(sh, "A2")).to_equal("20")
expect(_disp(sh, "B2")).to_equal("25")
```

</details>

#### TRANSPOSE of a 2x3 range yields a 3x2 range

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "1")
sh.set_value("E1", "2")
sh.set_value("F1", "3")
sh.set_value("D2", "4")
sh.set_value("E2", "5")
sh.set_value("F2", "6")
sh.set_value("A1", "=TRANSPOSE(D1:F2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("4")
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "B2")).to_equal("5")
expect(_disp(sh, "A3")).to_equal("3")
expect(_disp(sh, "B3")).to_equal("6")
```

</details>

#### UNIQUE keeps distinct values in first-seen order

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "b")
sh.set_value("D2", "a")
sh.set_value("D3", "b")
sh.set_value("D4", "c")
sh.set_value("D5", "a")
sh.set_value("A1", "=UNIQUE(D1:D5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("b")
expect(_disp(sh, "A2")).to_equal("a")
expect(_disp(sh, "A3")).to_equal("c")
expect(_disp(sh, "A4")).to_equal("")
```

</details>

#### SORT ascending orders a numeric column

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "30")
sh.set_value("D2", "10")
sh.set_value("D3", "20")
sh.set_value("A1", "=SORT(D1:D3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("10")
expect(_disp(sh, "A2")).to_equal("20")
expect(_disp(sh, "A3")).to_equal("30")
```

</details>

#### SORT descending reverses the order

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "30")
sh.set_value("D2", "10")
sh.set_value("D3", "20")
sh.set_value("A1", "=SORT(D1:D3,1,FALSE)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("30")
expect(_disp(sh, "A2")).to_equal("20")
expect(_disp(sh, "A3")).to_equal("10")
```

</details>

#### FILTER keeps rows matching a >10 criteria

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "5")
sh.set_value("D2", "15")
sh.set_value("D3", "25")
sh.set_value("D4", "8")
sh.set_value("A1", "=FILTER(D1:D4,1,\">10\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("15")
expect(_disp(sh, "A2")).to_equal("25")
expect(_disp(sh, "A3")).to_equal("")
```

</details>

#### shows #SPILL! when a target cell is occupied

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A2", "X")
sh.set_value("A1", "=SEQUENCE(3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#SPILL!")
expect(_disp(sh, "A2")).to_equal("X")
expect(_disp(sh, "A3")).to_equal("")
```

</details>

#### recalculation is idempotent for a spilled formula

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=SEQUENCE(3)")
sh = recalculate_formula_cells(sh)
val a1 = _disp(sh, "A1")
val a2 = _disp(sh, "A2")
val a3 = _disp(sh, "A3")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal(a1)
expect(_disp(sh, "A2")).to_equal(a2)
expect(_disp(sh, "A3")).to_equal(a3)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "A3")).to_equal("3")
```

</details>

#### recalculation is idempotent for a blocked #SPILL!

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A2", "X")
sh.set_value("A1", "=SEQUENCE(3)")
sh = recalculate_formula_cells(sh)
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#SPILL!")
expect(_disp(sh, "A2")).to_equal("X")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
