# formula_avariants_spec

> Calc stat A-variants + EXC percentiles + CRITBINOM + array remainder spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_avariants_spec

Calc stat A-variants + EXC percentiles + CRITBINOM + array remainder spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_avariants_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc stat A-variants + EXC percentiles + CRITBINOM + array remainder spec.

The *A statistics (AVERAGEA/MAXA/MINA/STDEVA/VARA/STDEVPA/VARPA) read raw typed
cells: text counts as 0, TRUE=1/FALSE=0, empty cells are skipped. Ground truth
for cells [10, "x", TRUE, 20] is the value set {10, 0, 1, 20}: AVERAGEA=31/4=7.75,
MAXA=20, MINA=0, sample VARA=Sum((x-7.75)^2)/3=260.75/3=86.916666..,
STDEVA=sqrt(86.916666)=9.322910.., population VARPA=260.75/4=65.1875,
STDEVPA=sqrt(65.1875)=8.073877.. (all hand-verified).

Exclusive percentiles use position = p*(n+1), 1-based, #ERR when the position
falls outside [1, n]: PERCENTILE.EXC([1,2,3,4],0.4)=2 (pos 2.0);
QUARTILE.EXC of the 11-value Excel-documented set at q=1 = 15 (pos 3.0);
PERCENTRANK.EXC([1,2,3,4],2)=2/(4+1)=0.4. CRITBINOM(6,0.5,0.75)=4 (first k with
binomial CDF>=0.75: CDF(3)=0.65625, CDF(4)=0.890625).

Array-returning functions spill a 2D grid: MODE.MULT (all repeated values, first
seen order, down one column), SORTBY, WRAPROWS, WRAPCOLS, EXPAND.

## Scenarios

### Calc stat A-variants — text=0, bool=1/0, empty skipped

#### AVERAGEA averages {10,0,1,20} = 7.75 (text is 0, TRUE is 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=AVERAGEA(A1:A4)")).to_equal("7.75")
```

</details>

#### MAXA of {10,0,1,20} is 20

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=MAXA(A1:A4)")).to_equal("20")
```

</details>

#### MINA of {10,0,1,20} is 0 (text counts as 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=MINA(A1:A4)")).to_equal("0")
```

</details>

#### VARA sample variance of {10,0,1,20} is 86.9166..

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VARA(A1:A4)")).to_start_with("86.9166")
```

</details>

#### STDEVA is sqrt of VARA = 9.3229..

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=STDEVA(A1:A4)")).to_start_with("9.3229")
```

</details>

#### VARPA population variance of {10,0,1,20} is 65.1875

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VARPA(A1:A4)")).to_equal("65.1875")
```

</details>

#### STDEVPA is sqrt of VARPA = 8.0738..

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=STDEVPA(A1:A4)")).to_start_with("8.0738")
```

</details>

#### AVERAGEA skips the blank A5, still 7.75

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=AVERAGEA(A1:A5)")).to_equal("7.75")
```

</details>

#### VARA needs 2+ values, fails closed on a single cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VARA(A1:A1)")).to_contain("#ERR")
```

</details>

### Calc exclusive percentiles — position p*(n+1)

#### PERCENTILE.EXC([1,2,3,4],0.4) lands exactly on the 2nd value = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PERCENTILE.EXC(B1:B4,0.4)")).to_equal("2")
```

</details>

#### QUARTILE.EXC of the documented 11-value set at q=1 = 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=QUARTILE.EXC(C1:C11,1)")).to_equal("15")
```

</details>

#### PERCENTRANK.EXC([1,2,3,4],2) = 2/(4+1) = 0.4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PERCENTRANK.EXC(B1:B4,2)")).to_start_with("0.4")
```

</details>

#### PERCENTILE.EXC rejects k<=0 as a domain error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PERCENTILE.EXC(B1:B4,0)")).to_contain("#ERR")
```

</details>

#### QUARTILE.EXC rejects q=4 (position n+1 is out of range)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=QUARTILE.EXC(B1:B4,4)")).to_contain("#ERR")
```

</details>

#### PERCENTRANK.EXC rejects a value below the minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=PERCENTRANK.EXC(B1:B4,0)")).to_contain("#ERR")
```

</details>

### Calc CRITBINOM — smallest k with CDF >= alpha

#### CRITBINOM(6,0.5,0.75) = 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CRITBINOM(6,0.5,0.75)")).to_equal("4")
```

</details>

#### CRITBINOM rejects a probability above 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CRITBINOM(6,1.5,0.75)")).to_contain("#ERR")
```

</details>

### Calc MODE.MULT — all modes spilled down a column

#### MODE.MULT of [1,2,2,3,3,4] spills [2,3] in first-seen order

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("m")
sh.set_value("H1", "1")
sh.set_value("H2", "2")
sh.set_value("H3", "2")
sh.set_value("H4", "3")
sh.set_value("H5", "3")
sh.set_value("H6", "4")
sh.set_value("A1", "=MODE.MULT(H1:H6)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("2")
expect(_disp(sh, "A2")).to_equal("3")
```

</details>

#### MODE.MULT fails closed with #ERR when nothing repeats

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("m")
sh.set_value("H1", "1")
sh.set_value("H2", "2")
sh.set_value("H3", "3")
sh.set_value("A1", "=MODE.MULT(H1:H3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

### Calc SORTBY — rows reordered by a parallel key column

#### SORTBY([a,b,c] by [3,1,2]) ascending spills [b,c,a]

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("sb")
sh.set_value("H1", "a")
sh.set_value("H2", "b")
sh.set_value("H3", "c")
sh.set_value("I1", "3")
sh.set_value("I2", "1")
sh.set_value("I3", "2")
sh.set_value("A1", "=SORTBY(H1:H3,I1:I3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("b")
expect(_disp(sh, "A2")).to_equal("c")
expect(_disp(sh, "A3")).to_equal("a")
```

</details>

### Calc WRAPROWS / WRAPCOLS — wrap a vector into a grid

#### WRAPROWS([1..5],2) fills rows of 2, padding the last with #N/A

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("wr")
sh.set_value("H1", "1")
sh.set_value("H2", "2")
sh.set_value("H3", "3")
sh.set_value("H4", "4")
sh.set_value("H5", "5")
sh.set_value("A1", "=WRAPROWS(H1:H5,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("2")
expect(_disp(sh, "A2")).to_equal("3")
expect(_disp(sh, "B2")).to_equal("4")
expect(_disp(sh, "A3")).to_equal("5")
expect(_disp(sh, "B3")).to_equal("#N/A")
```

</details>

#### WRAPCOLS([1..5],2) fills columns of 2, padding the last with #N/A

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("wc")
sh.set_value("H1", "1")
sh.set_value("H2", "2")
sh.set_value("H3", "3")
sh.set_value("H4", "4")
sh.set_value("H5", "5")
sh.set_value("A1", "=WRAPCOLS(H1:H5,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("1")
expect(_disp(sh, "B1")).to_equal("3")
expect(_disp(sh, "C1")).to_equal("5")
expect(_disp(sh, "A2")).to_equal("2")
expect(_disp(sh, "B2")).to_equal("4")
expect(_disp(sh, "C2")).to_equal("#N/A")
```

</details>

### Calc EXPAND — grow a grid, padding new cells

#### EXPAND of a 1x2 range to 2x3 pads new cells with #N/A

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("ex")
sh.set_value("H1", "a")
sh.set_value("I1", "b")
sh.set_value("A1", "=EXPAND(H1:I1,2,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("a")
expect(_disp(sh, "B1")).to_equal("b")
expect(_disp(sh, "C1")).to_equal("#N/A")
expect(_disp(sh, "A2")).to_equal("#N/A")
expect(_disp(sh, "B2")).to_equal("#N/A")
expect(_disp(sh, "C2")).to_equal("#N/A")
```

</details>

#### EXPAND fails closed with #ERR when shrinking below the source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("ex")
sh.set_value("H1", "a")
sh.set_value("I1", "b")
sh.set_value("A1", "=EXPAND(H1:I1,1,1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
