# formula_ref2_spec

> Calc reference/lookup tail spec: OFFSET, INDIRECT, AREAS, HYPERLINK.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_ref2_spec

Calc reference/lookup tail spec: OFFSET, INDIRECT, AREAS, HYPERLINK.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_ref2_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc reference/lookup tail spec: OFFSET, INDIRECT, AREAS, HYPERLINK.

OFFSET and INDIRECT live on TWO paths: the scalar formula path returns the
single referenced value (FormulaVal targets re-evaluate, empty targets report
0, per the CELL("contents") convention), and evaluate_formula_array spills the
referenced rectangle when OFFSET's height/width exceed 1 or INDIRECT's text is
a range like "A1:B2".

CEILING (documented, not faked): the generic numeric argument collector only
accepts literal REF:REF tokens or scalar expressions, so an array function
nested inside SUM — e.g. =SUM(OFFSET(A1,0,0,2,2)) — CANNOT deliver its grid.
In scalar context a height/width > 1 OFFSET yields its grid's TOP-LEFT value
(implicit-intersection-like), so the nested form totals 10 where Excel gives
100; that degradation is asserted below as documented behavior. The supported
equivalent — spill the OFFSET grid, then SUM over the spilled range — totals
100 and is asserted too (the top-left scalar convention is what lets the
range SUM re-evaluate the spill-origin cell correctly).

All expected values hand-checked against Excel semantics on the fixture
A1=10, A2=20, B1=30, B2=40.

## Scenarios

### OFFSET — scalar path

#### shifts down one row: OFFSET(A1,1,0) = 20

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,1,0)")).to_equal("20")
```

</details>

#### shifts right one column: OFFSET(A1,0,1) = 30

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,0,1)")).to_equal("30")
```

</details>

#### shifts diagonally: OFFSET(A1,1,1) = 40

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,1,1)")).to_equal("40")
```

</details>

#### zero shift returns the reference itself: OFFSET(A1,0,0) = 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,0,0)")).to_equal("10")
```

</details>

#### uses the top-left corner of a range reference: OFFSET(A1:B2,1,1) = 40

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1:B2,1,1)")).to_equal("40")
```

</details>

#### re-evaluates a formula target like CELL contents

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("A3", "=A1+A2")
sh.set_value("D1", "=OFFSET(A3,0,0)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("30")
```

</details>

#### reports 0 for an empty target cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,5,0)")).to_equal("0")
```

</details>

#### fails closed above row 1: OFFSET(A1,-1,0) = #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,-1,0)")).to_contain("#ERR")
```

</details>

#### fails closed left of column A: OFFSET(A1,0,-1) = #ERR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,0,-1)")).to_contain("#ERR")
```

</details>

#### fails closed on height < 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,0,0,0,1)")).to_contain("#ERR")
```

</details>

#### fails closed on width < 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,0,0,1,0)")).to_contain("#ERR")
```

</details>

#### fails closed when rows/cols are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=OFFSET(A1,1)")).to_contain("#ERR")
```

</details>

### OFFSET — array path (spills)

#### OFFSET(A1,0,0,2,2) spills the 2x2 rectangle

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=OFFSET(A1,0,0,2,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("10")
expect(_disp(sh, "E1")).to_equal("30")
expect(_disp(sh, "D2")).to_equal("20")
expect(_disp(sh, "E2")).to_equal("40")
```

</details>

#### OFFSET(A1,1,0,1,2) spills the shifted 1x2 row

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=OFFSET(A1,1,0,1,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("20")
expect(_disp(sh, "E1")).to_equal("40")
```

</details>

#### SUM over the spilled OFFSET grid totals 100 (supported form of SUM(OFFSET(...)))

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=OFFSET(A1,0,0,2,2)")
sh = recalculate_formula_cells(sh)
sh.set_value("G1", "=SUM(D1:E2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "G1")).to_equal("100")
```

</details>

#### CEILING: nested SUM(OFFSET(...,2,2)) degrades to the grid's top-left (Excel: 100)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=SUM(OFFSET(A1,0,0,2,2))")).to_equal("10")
```

</details>

#### CEILING: grid OFFSET in a scalar expression yields the top-left value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=\"[\"&OFFSET(A1,0,0,2,2)&\"]\"")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("[10]")
```

</details>

### INDIRECT

#### resolves a literal reference string: INDIRECT(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=INDIRECT(\"B2\")")).to_equal("40")
```

</details>

#### resolves a concatenated reference: INDIRECT(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=INDIRECT(\"A\"&\"1\")")).to_equal("10")
```

</details>

#### resolves a reference stored in another cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("C1", "B1")
sh.set_value("D1", "=INDIRECT(C1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("30")
```

</details>

#### fails closed on unparseable text: INDIRECT(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=INDIRECT(\"nonsense\")")).to_contain("#ERR")
```

</details>

#### range form spills the referenced rectangle

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh = _base(sh)
sh.set_value("D1", "=INDIRECT(\"A1:B2\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("10")
expect(_disp(sh, "E1")).to_equal("30")
expect(_disp(sh, "D2")).to_equal("20")
expect(_disp(sh, "E2")).to_equal("40")
```

</details>

### AREAS and HYPERLINK

#### AREAS of a range is 1 (single-area model)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=AREAS(A1:B2)")).to_equal("1")
```

</details>

#### AREAS of a single cell is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=AREAS(A1)")).to_equal("1")
```

</details>

#### AREAS without a reference fails closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=AREAS()")).to_contain("#ERR")
```

</details>

#### HYPERLINK returns the friendly text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=HYPERLINK(\"http://x.test\",\"Click\")")).to_equal("Click")
```

</details>

#### HYPERLINK without friendly text returns the url

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval1("=HYPERLINK(\"http://x.test\")")).to_equal("http://x.test")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
