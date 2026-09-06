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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TEXTBEFORE returns the text before the first delimiter
   - Expected: _disp(sh, "D1") equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTBEFORE returns the text before the first delimiter")
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTBEFORE(\"red-blue-green\",\"-\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("red")
```

</details>

#### TEXTAFTER with instance 2 returns text after the second delimiter

- TEXTAFTER with instance 2 returns text after the second delimiter
   - Expected: _disp(sh, "D1") equals `green`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTAFTER with instance 2 returns text after the second delimiter")
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTAFTER(\"red-blue-green\",\"-\",2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("green")
```

</details>

#### TEXTAFTER defaults to instance 1

- TEXTAFTER defaults to instance 1
   - Expected: _disp(sh, "D1") equals `blue-green`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTAFTER defaults to instance 1")
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTAFTER(\"red-blue-green\",\"-\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("blue-green")
```

</details>

#### TEXTBEFORE with a negative instance counts delimiters from the end

- TEXTBEFORE with a negative instance counts delimiters from the end
   - Expected: _disp(sh, "D1") equals `a-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTBEFORE with a negative instance counts delimiters from the end")
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTBEFORE(\"a-b-c\",\"-\",-1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("a-b")
```

</details>

#### TEXTBEFORE fails closed with #ERR when the delimiter is absent

- TEXTBEFORE fails closed with #ERR when the delimiter is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTBEFORE fails closed with #ERR when the delimiter is absent")
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTBEFORE(\"abc\",\"-\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### TEXTAFTER fails closed with #ERR when the delimiter is absent

- TEXTAFTER fails closed with #ERR when the delimiter is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTAFTER fails closed with #ERR when the delimiter is absent")
var sh = Sheet.new("s")
sh.set_value("D1", "=TEXTAFTER(\"abc\",\"-\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

### Calc text tail — ARRAYTOTEXT / VALUETOTEXT

#### ARRAYTOTEXT joins a range's display texts with comma-space

- ARRAYTOTEXT joins a range's display texts with comma-space
   - Expected: _disp(sh, "D1") equals `apple, banana, cherry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ARRAYTOTEXT joins a range's display texts with comma-space")
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

- VALUETOTEXT renders a number as its display text
   - Expected: _disp(sh, "D1") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VALUETOTEXT renders a number as its display text")
var sh = Sheet.new("s")
sh.set_value("D1", "=VALUETOTEXT(5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("5")
```

</details>

#### VALUETOTEXT renders text unchanged

- VALUETOTEXT renders text unchanged
   - Expected: _disp(sh, "D1") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VALUETOTEXT renders text unchanged")
var sh = Sheet.new("s")
sh.set_value("D1", "=VALUETOTEXT(\"x\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("x")
```

</details>

#### VALUETOTEXT renders a boolean as TRUE

- VALUETOTEXT renders a boolean as TRUE
   - Expected: _disp(sh, "D1") equals `TRUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VALUETOTEXT renders a boolean as TRUE")
var sh = Sheet.new("s")
sh.set_value("D1", "=VALUETOTEXT(TRUE())")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("TRUE")
```

</details>

### Calc text tail — TEXTSPLIT (spill)

#### TEXTSPLIT with column and row delimiters spills a 2D grid

- TEXTSPLIT with column and row delimiters spills a 2D grid
   - Expected: _disp(sh, "A1") equals `a`
   - Expected: _disp(sh, "B1") equals `b`
   - Expected: _disp(sh, "A2") equals `c`
   - Expected: _disp(sh, "B2") equals `d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTSPLIT with column and row delimiters spills a 2D grid")
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

- TEXTSPLIT with only a column delimiter spills across one row
   - Expected: _disp(sh, "A1") equals `a`
   - Expected: _disp(sh, "B1") equals `b`
   - Expected: _disp(sh, "C1") equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TEXTSPLIT with only a column delimiter spills across one row")
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

- ADDRESS defaults to a fully-absolute A1 reference
   - Expected: _disp(sh, "D1") equals `$C$2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADDRESS defaults to a fully-absolute A1 reference")
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(2,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("$C$2")
```

</details>

#### ADDRESS with abs 4 yields a fully-relative reference

- ADDRESS with abs 4 yields a fully-relative reference
   - Expected: _disp(sh, "D1") equals `C2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADDRESS with abs 4 yields a fully-relative reference")
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(2,3,4)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("C2")
```

</details>

#### ADDRESS with abs 2 fixes the row only

- ADDRESS with abs 2 fixes the row only
   - Expected: _disp(sh, "D1") equals `C$2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADDRESS with abs 2 fixes the row only")
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(2,3,2)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("C$2")
```

</details>

#### ADDRESS with abs 3 fixes the column only

- ADDRESS with abs 3 fixes the column only
   - Expected: _disp(sh, "D1") equals `$C2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADDRESS with abs 3 fixes the column only")
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(2,3,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("$C2")
```

</details>

#### ADDRESS with a1 FALSE yields an R1C1 reference

- ADDRESS with a1 FALSE yields an R1C1 reference
   - Expected: _disp(sh, "D1") equals `R5C4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADDRESS with a1 FALSE yields an R1C1 reference")
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(5,4,1,FALSE())")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("R5C4")
```

</details>

#### ADDRESS fails closed with #ERR on a non-positive row

- ADDRESS fails closed with #ERR on a non-positive row


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADDRESS fails closed with #ERR on a non-positive row")
var sh = Sheet.new("s")
sh.set_value("D1", "=ADDRESS(0,3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

### Calc reference tail — ROWS / COLUMNS / ROW / COLUMN

#### ROWS counts the rows spanned by a range

- ROWS counts the rows spanned by a range
   - Expected: _disp(sh, "D1") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROWS counts the rows spanned by a range")
var sh = Sheet.new("s")
sh.set_value("D1", "=ROWS(A1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("3")
```

</details>

#### COLUMNS counts the columns spanned by a range

- COLUMNS counts the columns spanned by a range
   - Expected: _disp(sh, "D1") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COLUMNS counts the columns spanned by a range")
var sh = Sheet.new("s")
sh.set_value("D1", "=COLUMNS(A1:B3)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("2")
```

</details>

#### ROW returns the 1-based row of a reference

- ROW returns the 1-based row of a reference
   - Expected: _disp(sh, "D1") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROW returns the 1-based row of a reference")
var sh = Sheet.new("s")
sh.set_value("D1", "=ROW(B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("5")
```

</details>

#### COLUMN returns the 1-based column of a reference

- COLUMN returns the 1-based column of a reference
   - Expected: _disp(sh, "D1") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("COLUMN returns the 1-based column of a reference")
var sh = Sheet.new("s")
sh.set_value("D1", "=COLUMN(B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("2")
```

</details>

#### ROWS of a single cell is 1

- ROWS of a single cell is 1
   - Expected: _disp(sh, "D1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROWS of a single cell is 1")
var sh = Sheet.new("s")
sh.set_value("D1", "=ROWS(B5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### bare ROW() resolves via the origin cell (CARD 14 behavior)

- bare ROW() resolves via the origin cell (CARD 14 behavior)
   - Expected: _disp(sh, "D1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare ROW() resolves via the origin cell (CARD 14 behavior)")
var sh = Sheet.new("s")
sh.set_value("D1", "=ROW()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### bare COLUMN() resolves via the origin cell (CARD 14 behavior)

- bare COLUMN() resolves via the origin cell (CARD 14 behavior)
   - Expected: _disp(sh, "D1") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare COLUMN() resolves via the origin cell (CARD 14 behavior)")
var sh = Sheet.new("s")
sh.set_value("D1", "=COLUMN()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("4")
```

</details>

### Calc info tail — FORMULATEXT / ISFORMULA

#### FORMULATEXT returns the referenced cell's formula text

- FORMULATEXT returns the referenced cell's formula text
   - Expected: _disp(sh, "D1") equals `=1+2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FORMULATEXT returns the referenced cell's formula text")
var sh = Sheet.new("s")
sh.set_value("B1", "=1+2")
sh.set_value("D1", "=FORMULATEXT(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("=1+2")
```

</details>

#### FORMULATEXT fails closed with #ERR on a non-formula cell

- FORMULATEXT fails closed with #ERR on a non-formula cell


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FORMULATEXT fails closed with #ERR on a non-formula cell")
var sh = Sheet.new("s")
sh.set_value("B1", "hello")
sh.set_value("D1", "=FORMULATEXT(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#ERR")
```

</details>

#### ISFORMULA is TRUE for a formula cell

- ISFORMULA is TRUE for a formula cell
   - Expected: _disp(sh, "D1") equals `TRUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ISFORMULA is TRUE for a formula cell")
var sh = Sheet.new("s")
sh.set_value("B1", "=1+2")
sh.set_value("D1", "=ISFORMULA(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("TRUE")
```

</details>

#### ISFORMULA is FALSE for a plain value cell

- ISFORMULA is FALSE for a plain value cell
   - Expected: _disp(sh, "D1") equals `FALSE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ISFORMULA is FALSE for a plain value cell")
var sh = Sheet.new("s")
sh.set_value("B1", "hello")
sh.set_value("D1", "=ISFORMULA(B1)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("FALSE")
```

</details>

### Calc info tail — SHEET / SHEETS / NA / TYPE

#### SHEET is 1 in the single-sheet model

- SHEET is 1 in the single-sheet model
   - Expected: _disp(sh, "D1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHEET is 1 in the single-sheet model")
var sh = Sheet.new("s")
sh.set_value("D1", "=SHEET()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### SHEETS is 1 in the single-sheet model

- SHEETS is 1 in the single-sheet model
   - Expected: _disp(sh, "D1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHEETS is 1 in the single-sheet model")
var sh = Sheet.new("s")
sh.set_value("D1", "=SHEETS()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### NA yields the #N/A error value

- NA yields the #N/A error value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NA yields the #N/A error value")
var sh = Sheet.new("s")
sh.set_value("D1", "=NA()")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_contain("#N/A")
```

</details>

#### TYPE of a number is 1

- TYPE of a number is 1
   - Expected: _disp(sh, "D1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TYPE of a number is 1")
var sh = Sheet.new("s")
sh.set_value("D1", "=TYPE(5)")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("1")
```

</details>

#### TYPE of text is 2

- TYPE of text is 2
   - Expected: _disp(sh, "D1") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TYPE of text is 2")
var sh = Sheet.new("s")
sh.set_value("D1", "=TYPE(\"x\")")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("2")
```

</details>

#### TYPE of a boolean is 4

- TYPE of a boolean is 4
   - Expected: _disp(sh, "D1") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TYPE of a boolean is 4")
var sh = Sheet.new("s")
sh.set_value("D1", "=TYPE(TRUE())")
sh = recalculate_formula_cells(sh)
expect(_disp(sh, "D1")).to_equal("4")
```

</details>

#### TYPE of an error value is 16

- TYPE of an error value is 16
   - Expected: _disp(sh, "D1") equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TYPE of an error value is 16")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bdfec933632fb8862e09e2092f67e6381d44ad61e90ae8161a9b4e7f0332c842`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bdfec933632fb8862e09e2092f67e6381d44ad61e90ae8161a9b4e7f0332c842`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bdfec933632fb8862e09e2092f67e6381d44ad61e90ae8161a9b4e7f0332c842`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_text2_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_text2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_text2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_text2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_text2_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TEXTBEFORE returns the text before the first delimiter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_text2_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TEXTAFTER with instance 2 returns text after the second delimiter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_text2_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TEXTAFTER defaults to instance 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
