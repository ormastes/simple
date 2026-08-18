# formula_text2_spec

> Calc text / reference / info tail spec (CARD 5).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_text2_spec

Calc text / reference / info tail spec (CARD 5).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_text2_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc text / reference / info tail spec (CARD 5).

Scalar text (TEXTBEFORE/TEXTAFTER/ARRAYTOTEXT/VALUETOTEXT), reference
(ADDRESS/ROWS/COLUMNS/ROW/COLUMN), and info (FORMULATEXT/ISFORMULA/SHEET/
SHEETS/NA/TYPE) functions evaluate through the scalar formula path and cache a
single display value. TEXTSPLIT is array-returning: it evaluates to a 2D grid
whose top-left stays in the formula cell and the rest spills into the adjacent
rectangle (like CHOOSECOLS). Bare ROW()/COLUMN() resolve via the recalc
origin cell since CARD 14; with-arg forms unchanged. Historic note: they
failed closed with
#ERR — threading the formula's origin cell into the evaluator is deferred to
CARD 14. Every expected value is hand-computed against Excel semantics.

## Scenarios

### Calc text tail — TEXTBEFORE / TEXTAFTER

#### TEXTBEFORE returns the text before the first delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTBEFORE(\"red-blue-green\",\"-\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("red")
```

</details>

#### TEXTAFTER with instance 2 returns text after the second delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTAFTER(\"red-blue-green\",\"-\",2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("green")
```

</details>

#### TEXTAFTER defaults to instance 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTAFTER(\"red-blue-green\",\"-\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("blue-green")
```

</details>

#### TEXTBEFORE with a negative instance counts delimiters from the end

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTBEFORE(\"a-b-c\",\"-\",-1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("a-b")
```

</details>

#### TEXTBEFORE fails closed with #ERR when the delimiter is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTBEFORE(\"abc\",\"-\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### TEXTAFTER fails closed with #ERR when the delimiter is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTAFTER(\"abc\",\"-\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

### Calc text tail — ARRAYTOTEXT / VALUETOTEXT

#### ARRAYTOTEXT joins a range's display texts with comma-space

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "apple")
sh.set_value("A2", "banana")
sh.set_value("A3", "cherry")
sh.set_value("D1", "=ARRAYTOTEXT(A1:A3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("apple, banana, cherry")
```

</details>

#### VALUETOTEXT renders a number as its display text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=VALUETOTEXT(5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("5")
```

</details>

#### VALUETOTEXT renders text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=VALUETOTEXT(\"x\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("x")
```

</details>

#### VALUETOTEXT renders a boolean as TRUE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=VALUETOTEXT(TRUE())")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("TRUE")
```

</details>

### Calc text tail — TEXTSPLIT (spill)

#### TEXTSPLIT with column and row delimiters spills a 2D grid

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=TEXTSPLIT(\"a,b;c,d\",\",\",\";\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("a")
expect(_disp(sh, "B1")).to_equal("b")
expect(_disp(sh, "A2")).to_equal("c")
expect(_disp(sh, "B2")).to_equal("d")
```

</details>

#### TEXTSPLIT with only a column delimiter spills across one row

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("A1", "=TEXTSPLIT(\"a,b,c\",\",\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "A1")).to_equal("a")
expect(_disp(sh, "B1")).to_equal("b")
expect(_disp(sh, "C1")).to_equal("c")
```

</details>

### Calc reference tail — ADDRESS

#### ADDRESS defaults to a fully-absolute A1 reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(2,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("$C$2")
```

</details>

#### ADDRESS with abs 4 yields a fully-relative reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(2,3,4)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("C2")
```

</details>

#### ADDRESS with abs 2 fixes the row only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(2,3,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("C$2")
```

</details>

#### ADDRESS with abs 3 fixes the column only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(2,3,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("$C2")
```

</details>

#### ADDRESS with a1 FALSE yields an R1C1 reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(5,4,1,FALSE())")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("R5C4")
```

</details>

#### ADDRESS fails closed with #ERR on a non-positive row

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(0,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

### Calc reference tail — ROWS / COLUMNS / ROW / COLUMN

#### ROWS counts the rows spanned by a range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ROWS(A1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("3")
```

</details>

#### COLUMNS counts the columns spanned by a range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=COLUMNS(A1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("2")
```

</details>

#### ROW returns the 1-based row of a reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ROW(B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("5")
```

</details>

#### COLUMN returns the 1-based column of a reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=COLUMN(B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("2")
```

</details>

#### ROWS of a single cell is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ROWS(B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### bare ROW() resolves via the origin cell (CARD 14 behavior)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=ROW()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### bare COLUMN() resolves via the origin cell (CARD 14 behavior)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=COLUMN()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("4")
```

</details>

### Calc info tail — FORMULATEXT / ISFORMULA

#### FORMULATEXT returns the referenced cell's formula text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("B1", "=1+2")
sh.set_value("D1", "=FORMULATEXT(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("=1+2")
```

</details>

#### FORMULATEXT fails closed with #ERR on a non-formula cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("B1", "hello")
sh.set_value("D1", "=FORMULATEXT(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### ISFORMULA is TRUE for a formula cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("B1", "=1+2")
sh.set_value("D1", "=ISFORMULA(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("TRUE")
```

</details>

#### ISFORMULA is FALSE for a plain value cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("B1", "hello")
sh.set_value("D1", "=ISFORMULA(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("FALSE")
```

</details>

### Calc info tail — SHEET / SHEETS / NA / TYPE

#### SHEET is 1 in the single-sheet model

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=SHEET()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### SHEETS is 1 in the single-sheet model

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=SHEETS()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### NA yields the #N/A error value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=NA()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#N/A")
```

</details>

#### TYPE of a number is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TYPE(5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### TYPE of text is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TYPE(\"x\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("2")
```

</details>

#### TYPE of a boolean is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TYPE(TRUE())")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("4")
```

</details>

#### TYPE of an error value is 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("s")
sh.set_value("D1", "=TYPE(NA())")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("16")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
