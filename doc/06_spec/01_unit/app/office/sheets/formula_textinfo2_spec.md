# formula_textinfo2_spec

> Calc text/info fill-in spec (textinfo2 batch).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_textinfo2_spec

Calc text/info fill-in spec (textinfo2 batch).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_textinfo2_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc text/info fill-in spec (textinfo2 batch).

Ground truth is pinned to published Excel documentation examples:
  * DOLLAR(1234.567, 2) = "$1,234.57" ; DOLLAR(-1234.567, -2) = "($1,200)"
    (negative decimals round to the LEFT of the decimal point, i.e. to a
    multiple of 10^2) ; DOLLAR(-0.123, 4) = "($0.1230)" ;
    DOLLAR(99.888) = "$99.89"  (all four are the MS docs worked examples;
    negatives render parenthesized).
  * UNICHAR(65) = "A" ; UNICODE(" ") = 32 and UNICODE("A") = 65 (MS docs).
    Runtime probe: char_from_code covers only 9/10/13 and 32..126 (codes
    >126 return ""), so UNICHAR fails closed outside that range.
  * CONCAT over a range concatenates every cell: CONCAT of [a,b,c] = "abc".
  * ISNONTEXT(5) = TRUE, ISNONTEXT("x") = FALSE ; ISLOGICAL(TRUE) = TRUE,
    ISLOGICAL(1) = FALSE (MS docs semantics).
  * CELL("address", B2) = "$B$2" ; CELL("row", B2) = 2 ; CELL("col", B2) = 2 ;
    CELL("contents", B2) = the cell's value; a range uses its top-left cell.
    Only these four info_types are implemented — others are #ERR.
  * INFO("numfile") = 1 and INFO("recalc") = "Automatic" — honest
    single-sheet stubs on the SHEET()/SHEETS() precedent; other types #ERR.
  * LENB/LEFTB/RIGHTB/MIDB alias LEN/LEFT/RIGHT/MID: the runtime's len() and
    slice() are byte-based (probe: "é".len() == 2), which IS the B forms'
    byte semantics, so the aliases are exact.

## Scenarios

### Calc DOLLAR

#### formats with default 2 decimals and thousands grouping

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DOLLAR(1234.567)")).to_equal("$1,234.57")
```

</details>

#### rounds left of the decimal point for negative decimals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DOLLAR(-1234.567,-2)")).to_equal("($1,200)")
```

</details>

#### keeps requested trailing decimals on a negative value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DOLLAR(-0.123,4)")).to_equal("($0.1230)")
```

</details>

#### rounds half away from zero on display

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DOLLAR(99.888)")).to_equal("$99.89")
```

</details>

### Calc UNICHAR / UNICODE

#### UNICHAR(65) is A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=UNICHAR(65)")).to_equal("A")
```

</details>

#### UNICODE returns the first codepoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=UNICODE(\"A\")")).to_equal("65")
```

</details>

#### UNICODE of a space is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=UNICODE(\" \")")).to_equal("32")
```

</details>

#### UNICHAR fails closed outside the runtime-supported range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=UNICHAR(0)")).to_contain("#ERR")
expect(_eval("=UNICHAR(200)")).to_contain("#ERR")
```

</details>

#### UNICODE of an empty string errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=UNICODE(\"\")")).to_contain("#ERR")
```

</details>

### Calc CONCAT range expansion

#### concatenates every cell of a range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run(_abc_sheet(), "=CONCAT(A1:A3)")).to_equal("abc")
```

</details>

#### mixes ranges and scalars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run(_abc_sheet(), "=CONCAT(A1:A3,\"!\")")).to_equal("abc!")
```

</details>

### Calc ISNONTEXT / ISLOGICAL

#### ISNONTEXT is TRUE for numbers and FALSE for text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISNONTEXT(5)")).to_equal("TRUE")
expect(_eval("=ISNONTEXT(\"x\")")).to_equal("FALSE")
```

</details>

#### ISNONTEXT is TRUE for booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISNONTEXT(TRUE)")).to_equal("TRUE")
```

</details>

#### ISLOGICAL detects booleans only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=ISLOGICAL(TRUE)")).to_equal("TRUE")
expect(_eval("=ISLOGICAL(1)")).to_equal("FALSE")
expect(_eval("=ISLOGICAL(\"TRUE\")")).to_equal("FALSE")
```

</details>

### Calc CELL

#### address of B2 is $B$2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run(_abc_sheet(), "=CELL(\"address\",B2)")).to_equal("$B$2")
```

</details>

#### row and col of B2 are 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run(_abc_sheet(), "=CELL(\"row\",B2)")).to_equal("2")
expect(_run(_abc_sheet(), "=CELL(\"col\",B2)")).to_equal("2")
```

</details>

#### contents reads the referenced cell's value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run(_abc_sheet(), "=CELL(\"contents\",B2)")).to_equal("7")
```

</details>

#### a range argument uses its top-left cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run(_abc_sheet(), "=CELL(\"address\",B2:C5)")).to_equal("$B$2")
```

</details>

#### unsupported info_types and a missing reference fail closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run(_abc_sheet(), "=CELL(\"format\",B2)")).to_contain("#ERR")
expect(_eval("=CELL(\"row\")")).to_contain("#ERR")
```

</details>

### Calc INFO

#### reports the single-file, auto-recalc model honestly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=INFO(\"numfile\")")).to_equal("1")
expect(_eval("=INFO(\"recalc\")")).to_equal("Automatic")
```

</details>

#### fails closed on other info types

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=INFO(\"osversion\")")).to_contain("#ERR")
```

</details>

### Calc byte-form text aliases

#### LENB counts bytes like LEN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LENB(\"abc\")")).to_equal("3")
```

</details>

#### LEFTB / RIGHTB / MIDB slice by bytes like the base forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=LEFTB(\"abcdef\",3)")).to_equal("abc")
expect(_eval("=RIGHTB(\"abcdef\",2)")).to_equal("ef")
expect(_eval("=MIDB(\"abcdef\",2,3)")).to_equal("bcd")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
