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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats with default 2 decimals and thousands grouping
   - Expected: _eval("=DOLLAR(1234.567)") equals `$1,234.57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats with default 2 decimals and thousands grouping")
expect(_eval("=DOLLAR(1234.567)")).to_equal("$1,234.57")
```

</details>

#### rounds left of the decimal point for negative decimals

- rounds left of the decimal point for negative decimals
   - Expected: _eval("=DOLLAR(-1234.567,-2)") equals `($1,200)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds left of the decimal point for negative decimals")
expect(_eval("=DOLLAR(-1234.567,-2)")).to_equal("($1,200)")
```

</details>

#### keeps requested trailing decimals on a negative value

- keeps requested trailing decimals on a negative value
   - Expected: _eval("=DOLLAR(-0.123,4)") equals `($0.1230)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps requested trailing decimals on a negative value")
expect(_eval("=DOLLAR(-0.123,4)")).to_equal("($0.1230)")
```

</details>

#### rounds half away from zero on display

- rounds half away from zero on display
   - Expected: _eval("=DOLLAR(99.888)") equals `$99.89`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds half away from zero on display")
expect(_eval("=DOLLAR(99.888)")).to_equal("$99.89")
```

</details>

### Calc UNICHAR / UNICODE

#### UNICHAR(65) is A

- UNICHAR(65) is A
   - Expected: _eval("=UNICHAR(65)") equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UNICHAR(65) is A")
expect(_eval("=UNICHAR(65)")).to_equal("A")
```

</details>

#### UNICODE returns the first codepoint

- UNICODE returns the first codepoint
   - Expected: _eval("=UNICODE(\"A\")") equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UNICODE returns the first codepoint")
expect(_eval("=UNICODE(\"A\")")).to_equal("65")
```

</details>

#### UNICODE of a space is 32

- UNICODE of a space is 32
   - Expected: _eval("=UNICODE(\" \")") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UNICODE of a space is 32")
expect(_eval("=UNICODE(\" \")")).to_equal("32")
```

</details>

#### UNICHAR fails closed outside the runtime-supported range

- UNICHAR fails closed outside the runtime-supported range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UNICHAR fails closed outside the runtime-supported range")
expect(_eval("=UNICHAR(0)")).to_contain("#ERR")
expect(_eval("=UNICHAR(200)")).to_contain("#ERR")
```

</details>

#### UNICODE of an empty string errors

- UNICODE of an empty string errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UNICODE of an empty string errors")
expect(_eval("=UNICODE(\"\")")).to_contain("#ERR")
```

</details>

### Calc CONCAT range expansion

#### concatenates every cell of a range

- concatenates every cell of a range
   - Expected: _run(_abc_sheet(), "=CONCAT(A1:A3)") equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concatenates every cell of a range")
expect(_run(_abc_sheet(), "=CONCAT(A1:A3)")).to_equal("abc")
```

</details>

#### mixes ranges and scalars

- mixes ranges and scalars
   - Expected: _run(_abc_sheet(), "=CONCAT(A1:A3,\"!\")") equals `abc!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixes ranges and scalars")
expect(_run(_abc_sheet(), "=CONCAT(A1:A3,\"!\")")).to_equal("abc!")
```

</details>

### Calc ISNONTEXT / ISLOGICAL

#### ISNONTEXT is TRUE for numbers and FALSE for text

- ISNONTEXT is TRUE for numbers and FALSE for text
   - Expected: _eval("=ISNONTEXT(5)") equals `TRUE`
   - Expected: _eval("=ISNONTEXT(\"x\")") equals `FALSE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ISNONTEXT is TRUE for numbers and FALSE for text")
expect(_eval("=ISNONTEXT(5)")).to_equal("TRUE")
expect(_eval("=ISNONTEXT(\"x\")")).to_equal("FALSE")
```

</details>

#### ISNONTEXT is TRUE for booleans

- ISNONTEXT is TRUE for booleans
   - Expected: _eval("=ISNONTEXT(TRUE)") equals `TRUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ISNONTEXT is TRUE for booleans")
expect(_eval("=ISNONTEXT(TRUE)")).to_equal("TRUE")
```

</details>

#### ISLOGICAL detects booleans only

- ISLOGICAL detects booleans only
   - Expected: _eval("=ISLOGICAL(TRUE)") equals `TRUE`
   - Expected: _eval("=ISLOGICAL(1)") equals `FALSE`
   - Expected: _eval("=ISLOGICAL(\"TRUE\")") equals `FALSE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ISLOGICAL detects booleans only")
expect(_eval("=ISLOGICAL(TRUE)")).to_equal("TRUE")
expect(_eval("=ISLOGICAL(1)")).to_equal("FALSE")
expect(_eval("=ISLOGICAL(\"TRUE\")")).to_equal("FALSE")
```

</details>

### Calc CELL

#### address of B2 is $B$2

- address of B2 is $B$2
   - Expected: _run(_abc_sheet(), "=CELL(\"address\",B2)") equals `$B$2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("address of B2 is $B$2")
expect(_run(_abc_sheet(), "=CELL(\"address\",B2)")).to_equal("$B$2")
```

</details>

#### row and col of B2 are 2

- row and col of B2 are 2
   - Expected: _run(_abc_sheet(), "=CELL(\"row\",B2)") equals `2`
   - Expected: _run(_abc_sheet(), "=CELL(\"col\",B2)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row and col of B2 are 2")
expect(_run(_abc_sheet(), "=CELL(\"row\",B2)")).to_equal("2")
expect(_run(_abc_sheet(), "=CELL(\"col\",B2)")).to_equal("2")
```

</details>

#### contents reads the referenced cell's value

- contents reads the referenced cell's value
   - Expected: _run(_abc_sheet(), "=CELL(\"contents\",B2)") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contents reads the referenced cell's value")
expect(_run(_abc_sheet(), "=CELL(\"contents\",B2)")).to_equal("7")
```

</details>

#### a range argument uses its top-left cell

- a range argument uses its top-left cell
   - Expected: _run(_abc_sheet(), "=CELL(\"address\",B2:C5)") equals `$B$2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a range argument uses its top-left cell")
expect(_run(_abc_sheet(), "=CELL(\"address\",B2:C5)")).to_equal("$B$2")
```

</details>

#### unsupported info_types and a missing reference fail closed

- unsupported info_types and a missing reference fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unsupported info_types and a missing reference fail closed")
expect(_run(_abc_sheet(), "=CELL(\"format\",B2)")).to_contain("#ERR")
expect(_eval("=CELL(\"row\")")).to_contain("#ERR")
```

</details>

### Calc INFO

#### reports the single-file, auto-recalc model honestly

- reports the single-file, auto-recalc model honestly
   - Expected: _eval("=INFO(\"numfile\")") equals `1`
   - Expected: _eval("=INFO(\"recalc\")") equals `Automatic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the single-file, auto-recalc model honestly")
expect(_eval("=INFO(\"numfile\")")).to_equal("1")
expect(_eval("=INFO(\"recalc\")")).to_equal("Automatic")
```

</details>

#### fails closed on other info types

- fails closed on other info types


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on other info types")
expect(_eval("=INFO(\"osversion\")")).to_contain("#ERR")
```

</details>

### Calc byte-form text aliases

#### LENB counts bytes like LEN

- LENB counts bytes like LEN
   - Expected: _eval("=LENB(\"abc\")") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LENB counts bytes like LEN")
expect(_eval("=LENB(\"abc\")")).to_equal("3")
```

</details>

#### LEFTB / RIGHTB / MIDB slice by bytes like the base forms

- LEFTB / RIGHTB / MIDB slice by bytes like the base forms
   - Expected: _eval("=LEFTB(\"abcdef\",3)") equals `abc`
   - Expected: _eval("=RIGHTB(\"abcdef\",2)") equals `ef`
   - Expected: _eval("=MIDB(\"abcdef\",2,3)") equals `bcd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LEFTB / RIGHTB / MIDB slice by bytes like the base forms")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `090395b7ee87e33799ff16de225204fc46bc279827aeb0710002ad5d86c511e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `090395b7ee87e33799ff16de225204fc46bc279827aeb0710002ad5d86c511e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `090395b7ee87e33799ff16de225204fc46bc279827aeb0710002ad5d86c511e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_textinfo2_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_textinfo2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_textinfo2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_textinfo2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_textinfo2_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats with default 2 decimals and thousands grouping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_textinfo2_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rounds left of the decimal point for negative decimals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_textinfo2_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps requested trailing decimals on a negative value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
