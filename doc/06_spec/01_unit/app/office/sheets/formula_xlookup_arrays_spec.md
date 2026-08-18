# formula_xlookup_arrays_spec

> Calc Excel-365 lookup + array-manipulation spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_xlookup_arrays_spec

Calc Excel-365 lookup + array-manipulation spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_xlookup_arrays_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc Excel-365 lookup + array-manipulation spec.

Scalar lookups (XLOOKUP/XMATCH/LOOKUP) evaluate through the scalar formula path
and cache a single display value. Array-manipulation functions
(CHOOSECOLS/CHOOSEROWS/TAKE/DROP/VSTACK/HSTACK/TOCOL/TOROW) evaluate to a 2D
grid: the top-left value stays in the formula's own cell and the rest spills into
the adjacent rectangle. Every expected value below is hand-computed against
Excel semantics.

## Scenarios

### Calc Excel-365 lookups — scalar

#### XLOOKUP finds an exact needle and returns the aligned value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XLOOKUP(\"banana\",A1:A3,B1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("20")
```

</details>

#### XLOOKUP returns the if_not_found value when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XLOOKUP(\"kiwi\",A1:A3,B1:B3,\"none\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("none")
```

</details>

#### XLOOKUP with no if_not_found yields an error when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XLOOKUP(\"kiwi\",A1:A3,B1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### XMATCH returns the 1-based position of an exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XMATCH(\"cherry\",A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("3")
```

</details>

#### XMATCH yields an error when the needle is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=XMATCH(\"kiwi\",A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### LOOKUP returns the result aligned to the largest value <= needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=LOOKUP(25,B1:B3,A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("banana")
```

</details>

#### LOOKUP errors when the needle precedes the first value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _labels(sh)
sh.set_value("D1", "=LOOKUP(5,B1:B3,A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

### Calc Excel-365 array manipulation — spill

#### CHOOSECOLS keeps the named columns in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=CHOOSECOLS(H1:J2,1,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("3")
expect(_disp(sh, "A2")).to_equal("4")
expect(_disp(sh, "B2")).to_equal("6")
```

</details>

#### CHOOSEROWS with a negative index takes the last row

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=CHOOSEROWS(H1:J2,-1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("4")
expect(_disp(sh, "B1")).to_equal("5")
expect(_disp(sh, "C1")).to_equal("6")
```

</details>

#### CHOOSECOLS fails closed with #ERR on an out-of-range index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=CHOOSECOLS(H1:J2,9)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

#### TAKE keeps the first rows and columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TAKE(H1:J2,1,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "A2")).to_equal("")
```

</details>

#### TAKE with a negative row count takes from the end

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TAKE(H1:J2,-1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("4")
expect(_disp(sh, "B1")).to_equal("5")
expect(_disp(sh, "C1")).to_equal("6")
```

</details>

#### TAKE fails closed with #ERR on a zero count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TAKE(H1:J2,0)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

#### DROP removes the first row

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=DROP(H1:J2,1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("4")
expect(_disp(sh, "B1")).to_equal("5")
expect(_disp(sh, "C1")).to_equal("6")
expect(_disp(sh, "A2")).to_equal("")
```

</details>

#### DROP fails closed with #ERR when it would remove every row

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=DROP(H1:J2,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

#### VSTACK stacks vertically and pads ragged widths with #N/A

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("I1", "2")
sh.set_value("H2", "4")
sh.set_value("I2", "5")
sh.set_value("J2", "6")
sh.set_value("A1", "=VSTACK(H1:I1,H2:J2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "C1")).to_equal("#N/A")
expect(_disp(sh, "A2")).to_equal("4")
expect(_disp(sh, "B2")).to_equal("5")
expect(_disp(sh, "C2")).to_equal("6")
```

</details>

#### HSTACK places grids side by side

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("H2", "4")
sh.set_value("I1", "2")
sh.set_value("I2", "5")
sh.set_value("A1", "=HSTACK(H1:H2,I1:I2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "A2")).to_equal("4")
expect(_disp(sh, "B2")).to_equal("5")
```

</details>

#### TOCOL flattens the grid row-major into one column

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TOCOL(H1:J2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "A3")).to_equal("3")
expect(_disp(sh, "A4")).to_equal("4")
expect(_disp(sh, "A5")).to_equal("5")
expect(_disp(sh, "A6")).to_equal("6")
```

</details>

#### TOROW flattens the grid row-major into one row

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TOROW(H1:J2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "C1")).to_equal("3")
expect(_disp(sh, "D1")).to_equal("4")
expect(_disp(sh, "E1")).to_equal("5")
expect(_disp(sh, "F1")).to_equal("6")
```

</details>

#### spill for an array function is idempotent

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh = _grid(sh)
sh.set_value("A1", "=TOCOL(H1:J2)")
sh = recalculate_formula_cells(sh)
val a1 = _disp(sh, "A1")
val a6 = _disp(sh, "A6")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal(a1)
expect(_disp(sh, "A6")).to_equal(a6)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "A6")).to_equal("6")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
