# formula_subtotal_fin_spec

> Calc SUBTOTAL/AGGREGATE aggregation + dated-financial tail spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_subtotal_fin_spec

Calc SUBTOTAL/AGGREGATE aggregation + dated-financial tail spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_subtotal_fin_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc SUBTOTAL/AGGREGATE aggregation + dated-financial tail spec.

Ground truths (all probe-verified against external references BEFORE writing):
  * SUBTOTAL(9,{1,2,3}) = 6 ; SUBTOTAL(1,{2,4,6}) = 4 ; SUBTOTAL(4,...) = max
    (Excel semantics; 101-111 behave like 1-11 — no hidden-rows model).
  * AGGREGATE(9, 6, {1,#N/A,3}) = 4 — option 6 skips error cells; option 0
    propagates them; other options are unmodeled and #ERR.
  * XNPV(0.09, {-10000,2750,4250,3250,2750}, {2008-01-01,2008-03-01,
    2008-10-30,2009-02-15,2009-04-01}) = 2086.647602 (Excel doc example,
    published rounded as 2086.65; day offsets 0/60/303/411/456 over 365).
  * XIRR(same values/dates) = 0.37336253 (Excel doc: 0.373363).
  * VDB(2400,300,120,0,1) = 40 and VDB(2400,300,10,0,1) = 480 (Excel doc);
    VDB(2400,300,120,6,18) = 396.3049 (Excel doc: 396.31);
    VDB(10000,0,5,0,5) = 10000 — the straight-line switch fully depreciates
    (per-year 4000/2400/1440/1080/1080, switch in year 4);
    VDB(10000,0,5,0,5,2,1) = 9222.4 — no_switch leaves 10000*0.6^5 = 777.6.
  * FREQUENCY({79,85,78,85,50,81,95,88,97},{70,79,89}) spills 1/2/4/2
    (Excel doc example).
  * ERROR.TYPE: one generic error kind here -> 2; #N/A stays distinguishable
    -> 7; ERROR.TYPE of a non-error is #ERR (Excel returns #N/A).

## Scenarios

### Calc SUBTOTAL

#### SUBTOTAL(9, range) sums the range

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("Z1", "=SUBTOTAL(9,A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_equal("6")
```

</details>

#### SUBTOTAL(1, range) averages the range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval123("=SUBTOTAL(1,A1:A3)")).to_equal("4")
```

</details>

#### SUBTOTAL(4, range) is the maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval123("=SUBTOTAL(4,A1:A3)")).to_equal("6")
```

</details>

#### SUBTOTAL(104, range) behaves like 4 when no rows are hidden

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval123("=SUBTOTAL(104,A1:A3)")).to_equal("6")
```

</details>

#### SUBTOTAL(7, range) is the sample standard deviation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval123("=SUBTOTAL(7,A1:A3)")).to_equal("2")
```

</details>

#### SUBTOTAL rejects function_num outside 1-11/101-111

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval123("=SUBTOTAL(12,A1:A3)")).to_contain("#ERR")
expect(_eval123("=SUBTOTAL(0,A1:A3)")).to_contain("#ERR")
```

</details>

### Calc SUBTOTAL: 101-111 honor Sheet row visibility

#### SUBTOTAL(9,...) includes hidden rows: sum = 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("A4", "4")
sh.set_value("A5", "5")
sh.hide_row(2)
sh.hide_row(4)
sh.set_value("Z1", "=SUBTOTAL(9,A1:A5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_equal("15")
```

</details>

#### SUBTOTAL(109,...) skips hidden rows: sum = 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("A4", "4")
sh.set_value("A5", "5")
sh.hide_row(2)
sh.hide_row(4)
sh.set_value("Z1", "=SUBTOTAL(109,A1:A5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_equal("9")
```

</details>

#### SUBTOTAL(101,...) averages only the visible values: (1+3+5)/3 = 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("A4", "4")
sh.set_value("A5", "5")
sh.hide_row(2)
sh.hide_row(4)
sh.set_value("Z1", "=SUBTOTAL(101,A1:A5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_equal("3")
```

</details>

### Calc AGGREGATE

#### AGGREGATE option 6 ignores error cells (SUM over 1,#N/A,3 = 4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_err_range("=AGGREGATE(9,6,A1:A3)")).to_equal("4")
```

</details>

#### AGGREGATE option 0 propagates errors in the range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_err_range("=AGGREGATE(9,0,A1:A3)")).to_contain("#ERR")
```

</details>

#### AGGREGATE option 6 average skips the error cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_err_range("=AGGREGATE(1,6,A1:A3)")).to_equal("2")
```

</details>

#### AGGREGATE rejects unmodeled options and function_nums

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_err_range("=AGGREGATE(9,3,A1:A3)")).to_contain("#ERR")
expect(_eval_err_range("=AGGREGATE(14,6,A1:A3)")).to_contain("#ERR")
```

</details>

### Calc AGGREGATE: options 5/7 honor Sheet row visibility

#### AGGREGATE(9,5,...) sums only the visible rows: 1+3+5 = 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("A4", "4")
sh.set_value("A5", "5")
sh.hide_row(2)
sh.hide_row(4)
sh.set_value("Z1", "=AGGREGATE(9,5,A1:A5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_equal("9")
```

</details>

#### AGGREGATE(1,5,...) averages only the visible rows: (1+3+5)/3 = 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.set_value("A4", "4")
sh.set_value("A5", "5")
sh.hide_row(2)
sh.hide_row(4)
sh.set_value("Z1", "=AGGREGATE(1,5,A1:A5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_equal("3")
```

</details>

#### AGGREGATE(9,7,...) ignores both a hidden row and an error cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "=NA()")
sh.set_value("A3", "3")
sh.set_value("A4", "4")
sh.set_value("A5", "5")
sh.hide_row(4)
sh.set_value("Z1", "=AGGREGATE(9,7,A1:A5)")
sh = recalculate_formula_cells(sh)
# Visible, non-error cells: 1, 3, 5 -> sum 9 (row 4's "4" is hidden,
# row 2's #N/A is ignored by option 7's error-skip).
expect(_disp(sh, "Z1")).to_equal("9")
```

</details>

#### AGGREGATE(9,0,...) with a hidden row still includes it (option 0 = default)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "1")
sh.set_value("A2", "2")
sh.set_value("A3", "3")
sh.hide_row(2)
sh.set_value("Z1", "=AGGREGATE(9,0,A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_equal("6")
```

</details>

### Calc AGGREGATE k-forms 12-19 (data 3,5,7,10,12; n=5)

#### 12 MEDIAN({3,5,7,10,12}) = 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(12,0,A1:A5)")).to_equal("7")
```

</details>

#### 13 MODE.SNGL({3,5,7,10,12}) = 3 (all-unique tie-break: first element)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(13,0,A1:A5)")).to_equal("3")
```

</details>

#### 14 LARGE({3,5,7,10,12}, 2) = 10 (2nd largest)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(14,0,A1:A5,2)")).to_equal("10")
```

</details>

#### 15 SMALL({3,5,7,10,12}, 2) = 5 (2nd smallest)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(15,0,A1:A5,2)")).to_equal("5")
```

</details>

#### 16 PERCENTILE.INC({3,5,7,10,12}, 0.25) = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(16,0,A1:A5,0.25)")).to_equal("5")
```

</details>

#### 17 QUARTILE.INC({3,5,7,10,12}, 1) = 5 (Q1 matches PERCENTILE.INC 0.25)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(17,0,A1:A5,1)")).to_equal("5")
```

</details>

#### 18 PERCENTILE.EXC({3,5,7,10,12}, 0.25) = 4 (rank=0.25*6=1.5 -> 3+0.5*(5-3))

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(18,0,A1:A5,0.25)")).to_equal("4")
```

</details>

#### 19 QUARTILE.EXC({3,5,7,10,12}, 1) = 4 (k=1/4=0.25, same rank as above)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(19,0,A1:A5,1)")).to_equal("4")
```

</details>

#### 18 PERCENTILE.EXC #ERRs when k is outside (1/(n+1), n/(n+1)) = (0.1667, 0.8333)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(18,0,A1:A5,0.9)")).to_contain("#ERR")
expect(_eval_kform("=AGGREGATE(18,0,A1:A5,0.05)")).to_contain("#ERR")
```

</details>

#### 19 QUARTILE.EXC #ERRs for quart=4 (k=1.0, out of open interval)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(19,0,A1:A5,4)")).to_contain("#ERR")
```

</details>

#### 14 LARGE #ERRs when k is out of range (0 or > n)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval_kform("=AGGREGATE(14,0,A1:A5,0)")).to_contain("#ERR")
expect(_eval_kform("=AGGREGATE(14,0,A1:A5,6)")).to_contain("#ERR")
```

</details>

### Calc XNPV / XIRR

#### XNPV matches the Excel documentation example

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _xfin_sheet()
sh.set_value("Z1", "=XNPV(0.09,A1:A5,B1:B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_start_with("2086.647")
```

</details>

#### XNPV rejects incongruent ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _xfin_sheet()
sh.set_value("Z1", "=XNPV(0.09,A1:A5,B1:B4)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_contain("#ERR")
```

</details>

#### XIRR matches the Excel documentation example

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _xfin_sheet()
sh.set_value("Z1", "=XIRR(A1:A5,B1:B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_start_with("0.373362")
```

</details>

#### XIRR accepts (and ignores) a guess argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _xfin_sheet()
sh.set_value("Z1", "=XIRR(A1:A5,B1:B5,0.1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_start_with("0.373362")
```

</details>

#### XIRR errors when the cashflows never change sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = _xfin_sheet()
sh.set_value("A1", "10000")
sh.set_value("Z1", "=XIRR(A1:A5,B1:B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_contain("#ERR")
```

</details>

### Calc VDB

#### VDB first month of the Excel doc example is 40

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VDB(2400,300,120,0,1)")).to_equal("40")
```

</details>

#### VDB first year of the Excel doc example is 480

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VDB(2400,300,10,0,1)")).to_equal("480")
```

</details>

#### VDB months 6-18 of the Excel doc example is 396.31

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VDB(2400,300,120,6,18)")).to_start_with("396.30")
```

</details>

#### VDB straight-line switch fully depreciates to a zero salvage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VDB(10000,0,5,0,5)")).to_equal("10000")
expect(_eval("=VDB(10000,0,5,3,5)")).to_equal("2160")
```

</details>

#### VDB no_switch keeps pure declining balance (residual remains)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VDB(10000,0,5,0,5,2,1)")).to_start_with("9222.4")
```

</details>

#### VDB rejects an end period before the start period

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=VDB(2400,300,10,4,2)")).to_contain("#ERR")
```

</details>

### Calc FREQUENCY (array spill)

#### FREQUENCY spills bins+1 counts down a column (Excel doc example)

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("A1", "79")
sh.set_value("A2", "85")
sh.set_value("A3", "78")
sh.set_value("A4", "85")
sh.set_value("A5", "50")
sh.set_value("A6", "81")
sh.set_value("A7", "95")
sh.set_value("A8", "88")
sh.set_value("A9", "97")
sh.set_value("C1", "70")
sh.set_value("C2", "79")
sh.set_value("C3", "89")
sh.set_value("E1", "=FREQUENCY(A1:A9,C1:C3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "E1")).to_equal("1")
expect(_disp(sh, "E2")).to_equal("2")
expect(_disp(sh, "E3")).to_equal("4")
expect(_disp(sh, "E4")).to_equal("2")
```

</details>

### Calc ERROR.TYPE

#### ERROR.TYPE of #N/A is 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ERROR.TYPE(NA())")).to_equal("7")
```

</details>

#### ERROR.TYPE of a generic error cell is 2 (single error kind)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("B1", "=LOG(0)")
sh.set_value("Z1", "=ERROR.TYPE(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "Z1")).to_equal("2")
```

</details>

#### ERROR.TYPE of a non-error is an error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ERROR.TYPE(5)")).to_contain("#ERR")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
