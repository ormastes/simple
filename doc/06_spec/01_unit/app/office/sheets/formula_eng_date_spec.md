# formula_eng_date_spec

> Calc engineering / number-base / date-niche functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_eng_date_spec

Calc engineering / number-base / date-niche functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_eng_date_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Calc engineering / number-base / date-niche functions spec.

Number bases (DEC2BIN/BIN2DEC/DEC2HEX/HEX2DEC/DEC2OCT/OCT2DEC/BASE/DECIMAL),
bitwise ops (BITAND/BITOR/BITXOR/BITLSHIFT/BITRSHIFT), significance rounding
(CEILING/FLOOR/TRUNC/INT), and date-niche functions built on the Hinnant
civil<->serial helpers (EOMONTH/WEEKNUM/NETWORKDAYS/WORKDAY/DATEDIF). Every
expected value is verified against Excel semantics, including fail-closed #ERR
domains. Number-base outputs route through the text-function path; bitwise/
math/date route through the numeric dispatch (DATEDIF's text unit forces it
onto the text path but it still returns a number).

## Scenarios

### Calc number bases — DEC2* conversions (text out)

#### DEC2BIN / DEC2OCT / DEC2HEX render integers in the target radix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DEC2BIN(9)")).to_equal("1001")
expect(_eval("=DEC2OCT(8)")).to_equal("10")
expect(_eval("=DEC2HEX(255)")).to_equal("FF")
expect(_eval("=DEC2BIN(0)")).to_equal("0")
```

</details>

#### DEC2* fail closed on negative or fractional input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two's-complement negatives are intentionally unsupported: #ERR.
expect(_eval("=DEC2BIN(-1)")).to_contain("#ERR")
expect(_eval("=DEC2HEX(2.5)")).to_contain("#ERR")
```

</details>

### Calc number bases — *2DEC conversions (number out)

#### BIN2DEC / OCT2DEC / HEX2DEC parse digit strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BIN2DEC(\"1001\")")).to_equal("9")
expect(_eval("=OCT2DEC(\"10\")")).to_equal("8")
expect(_eval("=HEX2DEC(\"FF\")")).to_equal("255")
expect(_eval("=HEX2DEC(\"ff\")")).to_equal("255")
```

</details>

#### *2DEC fail closed on out-of-radix digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BIN2DEC(\"1201\")")).to_contain("#ERR")
expect(_eval("=HEX2DEC(\"GG\")")).to_contain("#ERR")
```

</details>

### Calc number bases — BASE / DECIMAL (arbitrary radix)

#### BASE renders with an optional zero-pad minimum length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BASE(255, 16)")).to_equal("FF")
expect(_eval("=BASE(7, 2, 8)")).to_equal("00000111")
```

</details>

#### DECIMAL inverts BASE for a given radix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DECIMAL(\"FF\", 16)")).to_equal("255")
expect(_eval("=DECIMAL(\"111\", 2)")).to_equal("7")
```

</details>

#### BASE / DECIMAL fail closed on bad radix or digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BASE(10, 1)")).to_contain("#ERR")
expect(_eval("=BASE(10, 37)")).to_contain("#ERR")
expect(_eval("=DECIMAL(\"12\", 2)")).to_contain("#ERR")
```

</details>

### Calc bitwise ops

#### BITAND / BITOR / BITXOR operate on non-negative integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BITAND(13, 25)")).to_equal("9")
expect(_eval("=BITOR(13, 25)")).to_equal("29")
expect(_eval("=BITXOR(13, 25)")).to_equal("20")
```

</details>

#### BITLSHIFT / BITRSHIFT shift by the given count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BITLSHIFT(4, 2)")).to_equal("16")
expect(_eval("=BITRSHIFT(13, 2)")).to_equal("3")
```

</details>

#### bitwise ops fail closed on negative or fractional input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=BITAND(-1, 3)")).to_contain("#ERR")
expect(_eval("=BITOR(2.5, 3)")).to_contain("#ERR")
expect(_eval("=BITLSHIFT(-4, 2)")).to_contain("#ERR")
```

</details>

### Calc significance rounding

#### CEILING rounds away from zero to a multiple of significance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CEILING(2.5, 1)")).to_equal("3")
expect(_eval("=CEILING(-2.5, -1)")).to_equal("-3")
```

</details>

#### FLOOR rounds toward zero to a multiple of significance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=FLOOR(3.7, 2)")).to_equal("2")
expect(_eval("=FLOOR(-2.5, -1)")).to_equal("-2")
```

</details>

#### CEILING / FLOOR fail closed on sign mismatch (positive num, negative sig)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=CEILING(2.5, -1)")).to_contain("#ERR")
expect(_eval("=FLOOR(2.5, -1)")).to_contain("#ERR")
```

</details>

#### TRUNC and INT drop the fraction (INT floors, TRUNC toward zero)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=TRUNC(-8.9)")).to_equal("-8")
expect(_eval("=TRUNC(3.14159, 2)")).to_equal("3.14")
expect(_eval("=INT(-8.9)")).to_equal("-9")
expect(_eval("=INT(8.9)")).to_equal("8")
```

</details>

### Calc date-niche functions

#### EOMONTH returns the last day of the shifted month

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=YEAR(EOMONTH(DATE(2026, 1, 15), 1))")).to_equal("2026")
expect(_eval("=MONTH(EOMONTH(DATE(2026, 1, 15), 1))")).to_equal("2")
expect(_eval("=DAY(EOMONTH(DATE(2026, 1, 15), 1))")).to_equal("28")
```

</details>

#### WEEKNUM (system 1) puts Jan 1 in week 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=WEEKNUM(DATE(2026, 1, 1))")).to_equal("1")
```

</details>

#### NETWORKDAYS counts inclusive Mon-Fri working days

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=NETWORKDAYS(DATE(2026, 7, 1), DATE(2026, 7, 10))")).to_equal("8")
```

</details>

#### WORKDAY skips weekends when advancing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=YEAR(WORKDAY(DATE(2026, 7, 3), 1))")).to_equal("2026")
expect(_eval("=MONTH(WORKDAY(DATE(2026, 7, 3), 1))")).to_equal("7")
expect(_eval("=DAY(WORKDAY(DATE(2026, 7, 3), 1))")).to_equal("6")
```

</details>

#### DATEDIF measures whole years / months / days

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"Y\")")).to_equal("2")
expect(_eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"M\")")).to_equal("29")
expect(_eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"D\")")).to_equal("900")
```

</details>

#### DATEDIF fails closed on an unknown unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"Q\")")).to_contain("#ERR")
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
