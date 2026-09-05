# Formula Locale Text Specification

> Tests covering ASC function (full-width to half-width ASCII conversion), JIS / DBCS function (half-width to full-width ASCII conversion), BAHTTEXT function (Thai number text conversion), PHONETIC function (returns cell display text), EUROCONVERT function (fixed legacy euro rates), Regression: existing text functions still work.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formula Locale Text Specification

## Scenarios

### ASC function (full-width to half-width ASCII conversion)

#### should convert full-width ASCII characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=ASC(\"ＡＢＣ\")")
expect(result).to_equal("ABC")
```

</details>

#### should convert full-width space U+3000 to half-width space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=ASC(\"Ａ　Ｂ\")")
expect(result).to_equal("A B")
```

</details>

#### should convert full-width digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=ASC(\"１２３\")")
expect(result).to_equal("123")
```

</details>

#### should handle mixed full-width and pass-through

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=ASC(\"ＡＢＣ　１２３\")")
expect(result).to_equal("ABC 123")
```

</details>

#### should pass through characters outside the conversion range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=ASC(\"Hello\")")
expect(result).to_equal("Hello")
```

</details>

### JIS / DBCS function (half-width to full-width ASCII conversion)

#### should convert half-width ASCII to full-width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=JIS(\"ABC\")")
expect(result).to_equal("ＡＢＣ")
```

</details>

#### should alias DBCS to same behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=DBCS(\"ABC\")")
expect(result).to_equal("ＡＢＣ")
```

</details>

#### should convert half-width digits to full-width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=JIS(\"123\")")
expect(result).to_equal("１２３")
```

</details>

#### should convert half-width space to full-width space U+3000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=JIS(\"A B\")")
expect(result).to_equal("Ａ　Ｂ")
```

</details>

#### should pass through characters outside the conversion range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=JIS(\"日本語\")")
expect(result).to_equal("日本語")
```

</details>

### BAHTTEXT function (Thai number text conversion)

#### should convert whole baht amount with no satang

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(1234)")
expect(result).to_equal("หนึ่งพันสองร้อยสามสิบสี่บาทถ้วน")
```

</details>

#### should handle 21 with special ยี่สิบเอ็ด (not ยี่สิบหนึ่ง)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(21)")
expect(result).to_equal("ยี่สิบเอ็ดบาทถ้วน")
```

</details>

#### should handle 10 as สิบ alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(10)")
expect(result).to_equal("สิบบาทถ้วน")
```

</details>

#### should handle 11 as สิบเอ็ด

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(11)")
expect(result).to_equal("สิบเอ็ดบาทถ้วน")
```

</details>

#### should convert satang (decimal places)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(10.50)")
expect(result).to_equal("สิบบาทห้าสิบสตางค์")
```

</details>

#### should handle negative amounts with ลบ prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(-5)")
expect(result).to_equal("ลบห้าบาทถ้วน")
```

</details>

#### should handle large millions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(2000000)")
expect(result).to_equal("สองล้านบาทถ้วน")
```

</details>

#### should handle zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(0)")
expect(result).to_equal("ศูนย์บาทถ้วน")
```

</details>

#### should use เอ็ด for units 1 after hundreds (101)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(101)")
expect(result).to_equal("หนึ่งร้อยเอ็ดบาทถ้วน")
```

</details>

#### should use เอ็ด for units 1 after thousands (1001)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(1001)")
expect(result).to_equal("หนึ่งพันเอ็ดบาทถ้วน")
```

</details>

#### should spell multi-digit millions counts (12000000)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(12000000)")
expect(result).to_equal("สิบสองล้านบาทถ้วน")
```

</details>

#### should round to 2 decimals not truncate (1.999)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=BAHTTEXT(1.999)")
expect(result).to_equal("สองบาทถ้วน")
```

</details>

### PHONETIC function (returns cell display text)

#### should return the referenced cell text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("f")
sh.set_value("B1", "hello")
sh.set_value("C1", "=PHONETIC(B1)")
sh = recalculate_formula_cells(sh)
val result = cell_display_text(sh.get_cell("C1"))
expect(result).to_equal("hello")
```

</details>

#### should error with no arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=PHONETIC()")
expect(result).to_start_with("#ERR")
```

</details>

### EUROCONVERT function (fixed legacy euro rates)

#### should convert DEM to EUR correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=EUROCONVERT(100, \"DEM\", \"EUR\")")
# 100 / 1.95583 = 51.1291881...
expect(result).to_start_with("51.129")
```

</details>

#### should convert EUR to FRF

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=EUROCONVERT(1, \"EUR\", \"FRF\")")
val num = result.to_f64()
# 1 / 1 * 6.55957 = 6.55957
assert_true(num >= 6.559 and num <= 6.560)
```

</details>

#### should convert DEM to FRF via triangulation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=EUROCONVERT(100, \"DEM\", \"FRF\")")
val num = result.to_f64()
# 100 / 1.95583 * 6.55957 = 335.3854...
assert_true(num >= 335.38 and num <= 335.39)
```

</details>

#### should be case-insensitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=EUROCONVERT(1, \"eur\", \"frF\")")
val num = result.to_f64()
assert_true(num >= 6.559 and num <= 6.560)
```

</details>

#### should return error for unknown currency code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=EUROCONVERT(1, \"XXX\", \"EUR\")")
expect(result).to_start_with("#ERR")
```

</details>

#### should return error for unknown target code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=EUROCONVERT(1, \"EUR\", \"XXX\")")
expect(result).to_start_with("#ERR")
```

</details>

#### should convert ITL to ESP

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=EUROCONVERT(100, \"ITL\", \"ESP\")")
val num = result.to_f64()
# 100 / 1936.27 * 166.386 = 8.5931...
assert_true(num >= 8.59 and num <= 8.60)
```

</details>

#### should require three arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=EUROCONVERT(100, \"DEM\")")
expect(result).to_start_with("#ERR")
```

</details>

### Regression: existing text functions still work

#### PROPER should still work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=PROPER(\"hello WORLD\")")
expect(result).to_equal("Hello World")
```

</details>

#### CLEAN should still work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=CLEAN(\"ABC\")")
expect(result).to_equal("ABC")
```

</details>

#### UNICHAR should still work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=UNICHAR(65)")
expect(result).to_equal("A")
```

</details>

#### UPPER should still work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _eval("=UPPER(\"hello\")")
expect(result).to_equal("HELLO")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_locale_text_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ASC function (full-width to half-width ASCII conversion), JIS / DBCS function (half-width to full-width ASCII conversion), BAHTTEXT function (Thai number text conversion), PHONETIC function (returns cell display text), EUROCONVERT function (fixed legacy euro rates), Regression: existing text functions still work.
- ASC function (full-width to half-width ASCII conversion)
- JIS / DBCS function (half-width to full-width ASCII conversion)
- BAHTTEXT function (Thai number text conversion)
- PHONETIC function (returns cell display text)
- EUROCONVERT function (fixed legacy euro rates)
- Regression: existing text functions still work

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
