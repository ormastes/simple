# formula_matrix_spec

> Calc matrix + sum-combination + math/text-niche spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_matrix_spec

Calc matrix + sum-combination + math/text-niche spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_matrix_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc matrix + sum-combination + math/text-niche spec.

Array-returning matrix functions (MMULT/MINVERSE/MUNIT) evaluate to a 2D grid:
the top-left value stays in the formula's own cell and the rest spills into the
adjacent rectangle (via recalculate_formula_cells). MDETERM is a scalar routed
through the raw-range path so the square shape survives. The sum-combination and
math/text niche functions are scalar. Every expected value is hand-computed
against Excel semantics.

## Scenarios

### Calc matrix functions — spill

<details>
<summary>Advanced: MMULT computes the matrix product</summary>

#### MMULT computes the matrix product

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("I1", "2")
sh.set_value("H2", "3")
sh.set_value("I2", "4")
sh.set_value("K1", "5")
sh.set_value("L1", "6")
sh.set_value("K2", "7")
sh.set_value("L2", "8")
sh.set_value("A1", "=MMULT(H1:I2,K1:L2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("19")
expect(_disp(sh, "B1")).to_equal("22")
expect(_disp(sh, "A2")).to_equal("43")
expect(_disp(sh, "B2")).to_equal("50")
```

</details>


</details>

#### MMULT fails closed with #ERR on a dimension mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("I1", "2")
sh.set_value("H2", "3")
sh.set_value("I2", "4")
sh.set_value("K1", "5")
sh.set_value("L1", "6")
sh.set_value("M1", "7")
sh.set_value("A1", "=MMULT(H1:I2,K1:M1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_contain("#ERR")
```

</details>

<details>
<summary>Advanced: MINVERSE inverts a 2x2 matrix</summary>

#### MINVERSE inverts a 2x2 matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "4")
sh.set_value("I1", "7")
sh.set_value("H2", "2")
sh.set_value("I2", "6")
sh.set_value("A1", "=MINVERSE(H1:I2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("0.6")
expect(_disp(sh, "B1")).to_equal("-0.7")
expect(_disp(sh, "A2")).to_equal("-0.2")
expect(_disp(sh, "B2")).to_equal("0.4")
```

</details>


</details>

<details>
<summary>Advanced: MINVERSE fails closed with #ERR on a singular matrix</summary>

#### MINVERSE fails closed with #ERR on a singular matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("I1", "2")
sh.set_value("H2", "2")
sh.set_value("I2", "4")
sh.set_value("A1", "=MINVERSE(H1:I2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_contain("#ERR")
```

</details>


</details>

<details>
<summary>Advanced: MUNIT builds the identity matrix</summary>

#### MUNIT builds the identity matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=MUNIT(2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("0")
expect(_disp(sh, "A2")).to_equal("0")
expect(_disp(sh, "B2")).to_equal("1")
```

</details>


</details>

### Calc MDETERM — scalar

<details>
<summary>Advanced: MDETERM of a 2x2 matrix</summary>

#### MDETERM of a 2x2 matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "3")
sh.set_value("I1", "8")
sh.set_value("H2", "4")
sh.set_value("I2", "6")
sh.set_value("A1", "=MDETERM(H1:I2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("-14")
```

</details>


</details>

<details>
<summary>Advanced: MDETERM of a 3x3 matrix</summary>

#### MDETERM of a 3x3 matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("I1", "2")
sh.set_value("J1", "3")
sh.set_value("H2", "4")
sh.set_value("I2", "5")
sh.set_value("J2", "6")
sh.set_value("H3", "7")
sh.set_value("I3", "8")
sh.set_value("J3", "10")
sh.set_value("A1", "=MDETERM(H1:J3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("-3")
```

</details>


</details>

### Calc sum-of-products combinations — scalar

#### SUMX2MY2 sums x^2 - y^2

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "2")
sh.set_value("H2", "3")
sh.set_value("I1", "1")
sh.set_value("I2", "2")
sh.set_value("A1", "=SUMX2MY2(H1:H2,I1:I2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("8")
```

</details>

#### SUMX2PY2 sums x^2 + y^2

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "2")
sh.set_value("H2", "3")
sh.set_value("I1", "1")
sh.set_value("I2", "2")
sh.set_value("A1", "=SUMX2PY2(H1:H2,I1:I2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("18")
```

</details>

#### SUMXMY2 sums (x - y)^2

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "2")
sh.set_value("H2", "3")
sh.set_value("I1", "1")
sh.set_value("I2", "2")
sh.set_value("A1", "=SUMXMY2(H1:H2,I1:I2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("2")
```

</details>

### Calc math niche — scalar

#### FACTDOUBLE of an even n

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=FACTDOUBLE(6)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("48")
```

</details>

#### FACTDOUBLE of an odd n

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=FACTDOUBLE(7)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("105")
```

</details>

#### FACTDOUBLE fails closed with #ERR on a negative n

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=FACTDOUBLE(-1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_contain("#ERR")
```

</details>

#### MULTINOMIAL computes (sum)! / product of factorials

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=MULTINOMIAL(2,3,4)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1260")
```

</details>

#### SERIESSUM evaluates a power series

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("H1", "1")
sh.set_value("H2", "1")
sh.set_value("H3", "1")
sh.set_value("A1", "=SERIESSUM(2,0,1,H1:H3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("7")
```

</details>

### Calc text niche — Roman numerals

#### ROMAN uses the classic subtractive form (499)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=ROMAN(499)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("CDXCIX")
```

</details>

#### ROMAN of a four-figure year

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=ROMAN(2026)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("MMXXVI")
```

</details>

#### ROMAN fails closed with #ERR outside 1..3999

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=ROMAN(4000)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_contain("#ERR")
```

</details>

#### ARABIC inverts a Roman numeral

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=ARABIC(\"MMXXVI\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("2026")
```

</details>

#### ARABIC is case-insensitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=ARABIC(\"cdxcix\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("499")
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
