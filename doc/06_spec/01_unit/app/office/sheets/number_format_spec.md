# number_format_spec

> Office sheets number-format-code spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# number_format_spec

Office sheets number-format-code spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/number_format_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets number-format-code spec.

Hand-verified cases for `format_number` (Excel Format-Cells number-code
subset: fixed decimals, thousands grouping, percent, generic currency
prefix, scientific notation, date serials, "@" text passthrough, general
fallback, negative numbers), the `sheet_set_number_format` registry helper,
and the `cell_display_formatted` end-to-end display path.

## Scenarios

### format_number: fixed decimals

#### rounds 1234.567 to two decimals

- rounds 1234.567 to two decimals
   - Expected: format_number(1234.567, "0.00") equals `1234.57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds 1234.567 to two decimals")
# 1234.567 * 100 = 123456.7 -> +0.5 -> 123457.2 -> floor -> 1234.57
expect(format_number(1234.567, "0.00")).to_equal("1234.57")
```

</details>

#### rounds to three decimals

- rounds to three decimals
   - Expected: format_number(1234.5, "0.000") equals `1234.500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds to three decimals")
expect(format_number(1234.5, "0.000")).to_equal("1234.500")
```

</details>

#### rounds to a whole number with no decimal point

- rounds to a whole number with no decimal point
   - Expected: format_number(1234.5, "0") equals `1235`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds to a whole number with no decimal point")
expect(format_number(1234.5, "0")).to_equal("1235")
```

</details>

### format_number: thousands grouping
_"#,##0"-style codes._

#### groups thousands with two decimals

- groups thousands with two decimals
   - Expected: format_number(1234.567, "#,##0.00") equals `1,234.57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("groups thousands with two decimals")
expect(format_number(1234.567, "#,##0.00")).to_equal("1,234.57")
```

</details>

#### groups millions with no decimals, rounding up

- groups millions with no decimals, rounding up
   - Expected: format_number(1234567.891, "#,##0") equals `1,234,568`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("groups millions with no decimals, rounding up")
# 1234567.891 -> +0.5 -> 1234568.391 -> floor -> 1,234,568
expect(format_number(1234567.891, "#,##0")).to_equal("1,234,568")
```

</details>

### format_number: percent
_"0%"-style codes: value * 100 with a trailing '%'._

#### formats a percentage with one decimal

- formats a percentage with one decimal
   - Expected: format_number(0.4567, "0.0%") equals `45.7%`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats a percentage with one decimal")
# 0.4567 * 100 = 45.67 -> round half up to 1 decimal -> 45.7%
expect(format_number(0.4567, "0.0%")).to_equal("45.7%")
```

</details>

#### formats a percentage with no decimals

- formats a percentage with no decimals
   - Expected: format_number(0.5, "0%") equals `50%`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats a percentage with no decimals")
expect(format_number(0.5, "0%")).to_equal("50%")
```

</details>

### format_number: currency / generic literal prefix

#### formats dollars with a currency prefix

- formats dollars with a currency prefix
   - Expected: format_number(1234.5, "$#,##0.00") equals `$1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats dollars with a currency prefix")
expect(format_number(1234.5, "$#,##0.00")).to_equal("$1,234.50")
```

</details>

#### keeps a multi-character literal prefix

- keeps a multi-character literal prefix
   - Expected: format_number(1234.5, "USD #,##0.00") equals `USD 1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a multi-character literal prefix")
expect(format_number(1234.5, "USD #,##0.00")).to_equal("USD 1,234.50")
```

</details>

### format_number: scientific notation
_"0.00E+00"-style codes: mantissa in [1,10) + 2-digit signed exponent._

#### formats 12345.6789 in scientific notation

- formats 12345.6789 in scientific notation
   - Expected: format_number(12345.6789, "0.00E+00") equals `1.23E+04`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats 12345.6789 in scientific notation")
# 12345.6789 = 1.23456789e4 -> mantissa rounds to 1.23, exponent 4
expect(format_number(12345.6789, "0.00E+00")).to_equal("1.23E+04")
```

</details>

### format_number: dates

#### formats an Excel date serial as yyyy-mm-dd

- formats an Excel date serial as yyyy-mm-dd
   - Expected: format_number(45107.0, "yyyy-mm-dd") equals `2023-06-30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats an Excel date serial as yyyy-mm-dd")
expect(format_number(45107.0, "yyyy-mm-dd")).to_equal("2023-06-30")
```

</details>

#### formats the same serial as mm/dd/yyyy

- formats the same serial as mm/dd/yyyy
   - Expected: format_number(45107.0, "mm/dd/yyyy") equals `06/30/2023`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats the same serial as mm/dd/yyyy")
expect(format_number(45107.0, "mm/dd/yyyy")).to_equal("06/30/2023")
```

</details>

#### formats the same serial as dd.mm.yyyy

- formats the same serial as dd.mm.yyyy
   - Expected: format_number(45107.0, "dd.mm.yyyy") equals `30.06.2023`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats the same serial as dd.mm.yyyy")
expect(format_number(45107.0, "dd.mm.yyyy")).to_equal("30.06.2023")
```

</details>

### format_number: negative numbers
_A plain '-' prefix ahead of the formatted magnitude._

#### prefixes a minus sign for a negative grouped value

- prefixes a minus sign for a negative grouped value
   - Expected: format_number(-1234.5, "#,##0.00") equals `-1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefixes a minus sign for a negative grouped value")
expect(format_number(-1234.5, "#,##0.00")).to_equal("-1,234.50")
```

</details>

#### prefixes a minus sign ahead of a currency literal

- prefixes a minus sign ahead of a currency literal
   - Expected: format_number(-1234.5, "$#,##0.00") equals `-$1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefixes a minus sign ahead of a currency literal")
expect(format_number(-1234.5, "$#,##0.00")).to_equal("-$1,234.50")
```

</details>

### format_number: fallbacks
_"@"/'' and unknown codes never error the display path._

#### falls back to general for an empty code

- falls back to general for an empty code
   - Expected: format_number(42.0, "") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to general for an empty code")
expect(format_number(42.0, "")).to_equal("42")
```

</details>

#### trims a whole-number value under general display

- trims a whole-number value under general display
   - Expected: format_number(3.0, "") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims a whole-number value under general display")
expect(format_number(3.0, "")).to_equal("3")
```

</details>

#### keeps a fractional value under general display

- keeps a fractional value under general display
   - Expected: format_number(3.5, "") equals `3.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a fractional value under general display")
expect(format_number(3.5, "")).to_equal("3.5")
```

</details>

#### falls back to general for an unrecognized code

- falls back to general for an unrecognized code
   - Expected: format_number(42.5, "???") equals `42.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to general for an unrecognized code")
expect(format_number(42.5, "???")).to_equal("42.5")
```

</details>

### sheet_set_number_format: registry
_Sets only the number-format code, preserving existing bold/bg/fg._

#### sets a number format on a cell with no prior format

- sets a number format on a cell with no prior format
   - Expected: spec.num_fmt equals `0.00`
   - Expected: spec.bold is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets a number format on a cell with no prior format")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "B2", "0.00")
val spec = formats_get(formats, "B2")
expect(spec.num_fmt).to_equal("0.00")
expect(spec.bold).to_equal(false)
```

</details>

#### preserves existing bold/bg/fg when only the number format changes

- preserves existing bold/bg/fg when only the number format changes
   - Expected: spec.num_fmt equals `#,##0.00`
   - Expected: spec.bold is true
   - Expected: spec.bg equals `#ffe4b5`
   - Expected: spec.fg equals `#7a2e00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves existing bold/bg/fg when only the number format changes")
var formats = empty_sheet_formats()
formats = formats_set(formats, "B2", FormatSpec(num_fmt: "0", bold: true, bg: "#ffe4b5", fg: "#7a2e00"))
formats = sheet_set_number_format(formats, "B2", "#,##0.00")
val spec = formats_get(formats, "B2")
expect(spec.num_fmt).to_equal("#,##0.00")
expect(spec.bold).to_equal(true)
expect(spec.bg).to_equal("#ffe4b5")
expect(spec.fg).to_equal("#7a2e00")
```

</details>

### cell_display_formatted: end-to-end display

#### formats a plain numeric cell with a set number format

- formats a plain numeric cell with a set number format
   - Expected: cell_display_formatted(sheet, formats, "A1") equals `1234.57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats a plain numeric cell with a set number format")
var sheet = Sheet.new("S1")
sheet.set_value("A1", "1234.567")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "A1", "0.00")
expect(cell_display_formatted(sheet, formats, "A1")).to_equal("1234.57")
```

</details>

#### formats a formula cell's numeric result

- formats a formula cell's numeric result
   - Expected: cell_display_formatted(sheet, formats, "B3") equals `5.00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats a formula cell's numeric result")
var sheet = Sheet.new("S1")
sheet.set_value("B1", "2")
sheet.set_value("B2", "3")
sheet.set_value("B3", "=B1+B2")
sheet = recalculate_formula_cells(sheet)
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "B3", "0.00")
expect(cell_display_formatted(sheet, formats, "B3")).to_equal("5.00")
```

</details>

#### passes a text cell through unchanged regardless of any code

- passes a text cell through unchanged regardless of any code
   - Expected: cell_display_formatted(sheet, formats, "C1") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes a text cell through unchanged regardless of any code")
var sheet = Sheet.new("S1")
sheet.set_value("C1", "hello")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "C1", "@")
expect(cell_display_formatted(sheet, formats, "C1")).to_equal("hello")
```

</details>

#### falls back to plain display when no format is set

- falls back to plain display when no format is set
   - Expected: cell_display_formatted(sheet, formats, "D1") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to plain display when no format is set")
var sheet = Sheet.new("S1")
sheet.set_value("D1", "42")
val formats = empty_sheet_formats()
expect(cell_display_formatted(sheet, formats, "D1")).to_equal("42")
```

</details>

### format_number: multi-section codes -- 2 sections (positive+zero / negative)

#### uses section 1 for a positive value

- uses section 1 for a positive value
   - Expected: format_number(1234.5, "#,##0.00;-#,##0.00") equals `1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses section 1 for a positive value")
expect(format_number(1234.5, "#,##0.00;-#,##0.00")).to_equal("1,234.50")
```

</details>

#### uses section 1 for a zero value (positive+zero share section 1)

- uses section 1 for a zero value (positive+zero share section 1)
   - Expected: format_number(0.0, "#,##0.00;(#,##0.00)") equals `0.00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses section 1 for a zero value (positive+zero share section 1)")
expect(format_number(0.0, "#,##0.00;(#,##0.00)")).to_equal("0.00")
```

</details>

#### applies section 2's own literal minus to the absolute value

- applies section 2's own literal minus to the absolute value
   - Expected: format_number(-1234.5, "#,##0.00;-#,##0.00") equals `-1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies section 2's own literal minus to the absolute value")
expect(format_number(-1234.5, "#,##0.00;-#,##0.00")).to_equal("-1,234.50")
```

</details>

#### wraps a negative value in parentheses per the parenthesized negative section

- wraps a negative value in parentheses per the parenthesized negative section
   - Expected: format_number(-1234.5, "#,##0.00;(#,##0.00)") equals `(1,234.50)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps a negative value in parentheses per the parenthesized negative section")
# Hand-verified: Excel's classic accounting negative style.
expect(format_number(-1234.5, "#,##0.00;(#,##0.00)")).to_equal("(1,234.50)")
```

</details>

### format_number: multi-section codes -- 3 sections (positive/negative/zero)

#### uses section 1 for a positive value

- uses section 1 for a positive value
   - Expected: format_number(1234.5, "#,##0.00;(#,##0.00);\"-\"") equals `1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses section 1 for a positive value")
expect(format_number(1234.5, "#,##0.00;(#,##0.00);\"-\"")).to_equal("1,234.50")
```

</details>

#### uses section 2 (parens) for a negative value

- uses section 2 (parens) for a negative value
   - Expected: format_number(-1234.5, "#,##0.00;(#,##0.00);\"-\"") equals `(1,234.50)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses section 2 (parens) for a negative value")
expect(format_number(-1234.5, "#,##0.00;(#,##0.00);\"-\"")).to_equal("(1,234.50)")
```

</details>

#### uses section 3 (a quoted literal) for a zero value

- uses section 3 (a quoted literal) for a zero value
   - Expected: format_number(0.0, "#,##0.00;(#,##0.00);\"-\"") equals `-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses section 3 (a quoted literal) for a zero value")
# Hand-verified: a common accounting idiom -- render zero as a dash.
expect(format_number(0.0, "#,##0.00;(#,##0.00);\"-\"")).to_equal("-")
```

</details>

### format_number: multi-section codes -- 4 sections (+ text, numeric side)

#### still uses section 1 for a positive value when a 4th section is present

- still uses section 1 for a positive value when a 4th section is present
   - Expected: format_number(1234.5, "#,##0.00;(#,##0.00);\"-\";\"txt\"") equals `1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still uses section 1 for a positive value when a 4th section is present")
expect(format_number(1234.5, "#,##0.00;(#,##0.00);\"-\";\"txt\"")).to_equal("1,234.50")
```

</details>

### format_text_with_code: the text (4th) section

#### substitutes '@' with the text value

- substitutes '@' with the text value
   - Expected: format_text_with_code("abc", "#,##0.00;(#,##0.00);\"-\";\"Value: \"@") equals `Value: abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("substitutes '@' with the text value")
expect(format_text_with_code("abc", "#,##0.00;(#,##0.00);\"-\";\"Value: \"@")).to_equal("Value: abc")
```

</details>

#### substitutes '@' with no surrounding literal

- substitutes '@' with no surrounding literal
   - Expected: format_text_with_code("hello", "0;0;0;@") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("substitutes '@' with no surrounding literal")
expect(format_text_with_code("hello", "0;0;0;@")).to_equal("hello")
```

</details>

#### passes text through unchanged when the code has fewer than 4 sections

- passes text through unchanged when the code has fewer than 4 sections
   - Expected: format_text_with_code("hi", "0.00") equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes text through unchanged when the code has fewer than 4 sections")
expect(format_text_with_code("hi", "0.00")).to_equal("hi")
```

</details>

### format_number: color tags are stripped and ignored

#### strips a [Red] tag ahead of a negative section's literal minus

- strips a [Red] tag ahead of a negative section's literal minus
   - Expected: format_number(-1234.5, "#,##0.00;[Red]-#,##0.00") equals `-1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips a [Red] tag ahead of a negative section's literal minus")
expect(format_number(-1234.5, "#,##0.00;[Red]-#,##0.00")).to_equal("-1,234.50")
```

</details>

#### strips a [Blue] tag ahead of the positive section

- strips a [Blue] tag ahead of the positive section
   - Expected: format_number(1234.5, "[Blue]#,##0.00;-#,##0.00") equals `1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips a [Blue] tag ahead of the positive section")
expect(format_number(1234.5, "[Blue]#,##0.00;-#,##0.00")).to_equal("1,234.50")
```

</details>

### format_number: quote-aware section splitting

#### does not split on a ';' that appears inside a quoted literal

- does not split on a ';' that appears inside a quoted literal
   - Expected: format_number(1234.5, "\"x;y\"0.00;-0.00") equals `x;y1234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not split on a ';' that appears inside a quoted literal")
# If splitting were quote-BLIND this would wrongly become 3
# sections ("x, "\"x", "y\"0.00", "-0.00") instead of 2.
expect(format_number(1234.5, "\"x;y\"0.00;-0.00")).to_equal("x;y1234.50")
```

</details>

### format_number: dates -- dd/mm vs mm/dd distinction

#### renders dd/mm/yyyy with the day first

- renders dd/mm/yyyy with the day first
   - Expected: format_number(45107.0, "dd/mm/yyyy") equals `30/06/2023`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders dd/mm/yyyy with the day first")
expect(format_number(45107.0, "dd/mm/yyyy")).to_equal("30/06/2023")
```

</details>

#### renders mm/dd/yyyy with the month first (unchanged regression)

- renders mm/dd/yyyy with the month first (unchanged regression)
   - Expected: format_number(45107.0, "mm/dd/yyyy") equals `06/30/2023`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders mm/dd/yyyy with the month first (unchanged regression)")
expect(format_number(45107.0, "mm/dd/yyyy")).to_equal("06/30/2023")
```

</details>

#### renders a 2-digit year

- renders a 2-digit year
   - Expected: format_number(45107.0, "dd/mm/yy") equals `30/06/23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a 2-digit year")
expect(format_number(45107.0, "dd/mm/yy")).to_equal("30/06/23")
```

</details>

#### renders single-digit day/month with no zero-padding

- renders single-digit day/month with no zero-padding
   - Expected: format_number(45082.0, "d/m/yyyy") equals `5/6/2023`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders single-digit day/month with no zero-padding")
# Serial 45082 = 2023-06-05 (25 days before serial 45107's 2023-06-30).
expect(format_number(45082.0, "d/m/yyyy")).to_equal("5/6/2023")
```

</details>

### format_number: dates -- month names

#### renders the abbreviated month name (mmm)

- renders the abbreviated month name (mmm)
   - Expected: format_number(45107.0, "dd-mmm-yyyy") equals `30-Jun-2023`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders the abbreviated month name (mmm)")
expect(format_number(45107.0, "dd-mmm-yyyy")).to_equal("30-Jun-2023")
```

</details>

#### renders the full month name (mmmm)

- renders the full month name (mmmm)
   - Expected: format_number(45107.0, "mmmm dd, yyyy") equals `June 30, 2023`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders the full month name (mmmm)")
expect(format_number(45107.0, "mmmm dd, yyyy")).to_equal("June 30, 2023")
```

</details>

### format_number: thousands-scaling commas

#### scales by one million with two trailing commas

- scales by one million with two trailing commas
   - Expected: format_number(12345678.0, "0.0,,") equals `12.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scales by one million with two trailing commas")
# Hand-verified: 12,345,678 / 1,000,000 = 12.345678 -> 1 decimal -> 12.3
expect(format_number(12345678.0, "0.0,,")).to_equal("12.3")
```

</details>

#### scales by one thousand with a single trailing comma, still grouped

- scales by one thousand with a single trailing comma, still grouped
   - Expected: format_number(12345678.0, "#,##0,") equals `12,346`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scales by one thousand with a single trailing comma, still grouped")
# 12,345,678 / 1,000 = 12345.678 -> round to int -> 12,346
expect(format_number(12345678.0, "#,##0,")).to_equal("12,346")
```

</details>

#### does not confuse a mid-pattern grouping comma with a scaling comma

- does not confuse a mid-pattern grouping comma with a scaling comma
   - Expected: format_number(1234.5, "#,##0.00") equals `1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not confuse a mid-pattern grouping comma with a scaling comma")
expect(format_number(1234.5, "#,##0.00")).to_equal("1,234.50")
```

</details>

### format_number: '?' digit placeholder

#### extends the digit run without changing the rendered value

- extends the digit run without changing the rendered value
   - Expected: format_number(1234.5, "#,##0.0?") equals `1,234.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extends the digit run without changing the rendered value")
expect(format_number(1234.5, "#,##0.0?")).to_equal("1,234.5")
```

</details>

### format_number: quoted literal suffix/prefix

#### renders a quoted literal unit suffix

- renders a quoted literal unit suffix
   - Expected: format_number(1.5, "0.00 \"kg\"") equals `1.50 kg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a quoted literal unit suffix")
expect(format_number(1.5, "0.00 \"kg\"")).to_equal("1.50 kg")
```

</details>

#### renders a quoted literal currency prefix

- renders a quoted literal currency prefix
   - Expected: format_number(1234.5, "\"USD \"#,##0.00") equals `USD 1,234.50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a quoted literal currency prefix")
expect(format_number(1234.5, "\"USD \"#,##0.00")).to_equal("USD 1,234.50")
```

</details>

### cell_display_formatted: text cells with a 4-section code

#### applies the text section to a text cell's display

- applies the text section to a text cell's display
   - Expected: cell_display_formatted(sheet, formats, "E1") equals `Hi world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies the text section to a text cell's display")
var sheet = Sheet.new("S1")
sheet.set_value("E1", "world")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "E1", "0;0;0;\"Hi \"@")
expect(cell_display_formatted(sheet, formats, "E1")).to_equal("Hi world")
```

</details>

#### leaves a text cell unchanged when the code has fewer than 4 sections

- leaves a text cell unchanged when the code has fewer than 4 sections
   - Expected: cell_display_formatted(sheet, formats, "F1") equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a text cell unchanged when the code has fewer than 4 sections")
var sheet = Sheet.new("S1")
sheet.set_value("F1", "world")
var formats = empty_sheet_formats()
formats = sheet_set_number_format(formats, "F1", "0.00")
expect(cell_display_formatted(sheet, formats, "F1")).to_equal("world")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
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

- Canonical SPipe generation for source `c192d1b9ec7a6bb64b163e2448b4d8b7d51368886bb8eff869e70dd3abb6c5b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c192d1b9ec7a6bb64b163e2448b4d8b7d51368886bb8eff869e70dd3abb6c5b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c192d1b9ec7a6bb64b163e2448b4d8b7d51368886bb8eff869e70dd3abb6c5b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/number_format_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/number_format_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/number_format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/number_format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/number_format_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rounds 1234.567 to two decimals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/number_format_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rounds to three decimals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/number_format_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rounds to a whole number with no decimal point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
