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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- DEC2BIN / DEC2OCT / DEC2HEX render integers in the target radix
   - Expected: _eval("=DEC2BIN(9)") equals `1001`
   - Expected: _eval("=DEC2OCT(8)") equals `10`
   - Expected: _eval("=DEC2HEX(255)") equals `FF`
   - Expected: _eval("=DEC2BIN(0)") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DEC2BIN / DEC2OCT / DEC2HEX render integers in the target radix")
expect(_eval("=DEC2BIN(9)")).to_equal("1001")
expect(_eval("=DEC2OCT(8)")).to_equal("10")
expect(_eval("=DEC2HEX(255)")).to_equal("FF")
expect(_eval("=DEC2BIN(0)")).to_equal("0")
```

</details>

#### DEC2* fail closed on negative or fractional input

- DEC2* fail closed on negative or fractional input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DEC2* fail closed on negative or fractional input")
# Two's-complement negatives are intentionally unsupported: #ERR.
expect(_eval("=DEC2BIN(-1)")).to_contain("#ERR")
expect(_eval("=DEC2HEX(2.5)")).to_contain("#ERR")
```

</details>

### Calc number bases — *2DEC conversions (number out)

#### BIN2DEC / OCT2DEC / HEX2DEC parse digit strings

- BIN2DEC / OCT2DEC / HEX2DEC parse digit strings
   - Expected: _eval("=BIN2DEC(\"1001\")") equals `9`
   - Expected: _eval("=OCT2DEC(\"10\")") equals `8`
   - Expected: _eval("=HEX2DEC(\"FF\")") equals `255`
   - Expected: _eval("=HEX2DEC(\"ff\")") equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BIN2DEC / OCT2DEC / HEX2DEC parse digit strings")
expect(_eval("=BIN2DEC(\"1001\")")).to_equal("9")
expect(_eval("=OCT2DEC(\"10\")")).to_equal("8")
expect(_eval("=HEX2DEC(\"FF\")")).to_equal("255")
expect(_eval("=HEX2DEC(\"ff\")")).to_equal("255")
```

</details>

#### *2DEC fail closed on out-of-radix digits

- *2DEC fail closed on out-of-radix digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("*2DEC fail closed on out-of-radix digits")
expect(_eval("=BIN2DEC(\"1201\")")).to_contain("#ERR")
expect(_eval("=HEX2DEC(\"GG\")")).to_contain("#ERR")
```

</details>

### Calc number bases — BASE / DECIMAL (arbitrary radix)

#### BASE renders with an optional zero-pad minimum length

- BASE renders with an optional zero-pad minimum length
   - Expected: _eval("=BASE(255, 16)") equals `FF`
   - Expected: _eval("=BASE(7, 2, 8)") equals `00000111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BASE renders with an optional zero-pad minimum length")
expect(_eval("=BASE(255, 16)")).to_equal("FF")
expect(_eval("=BASE(7, 2, 8)")).to_equal("00000111")
```

</details>

#### DECIMAL inverts BASE for a given radix

- DECIMAL inverts BASE for a given radix
   - Expected: _eval("=DECIMAL(\"FF\", 16)") equals `255`
   - Expected: _eval("=DECIMAL(\"111\", 2)") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DECIMAL inverts BASE for a given radix")
expect(_eval("=DECIMAL(\"FF\", 16)")).to_equal("255")
expect(_eval("=DECIMAL(\"111\", 2)")).to_equal("7")
```

</details>

#### BASE / DECIMAL fail closed on bad radix or digits

- BASE / DECIMAL fail closed on bad radix or digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BASE / DECIMAL fail closed on bad radix or digits")
expect(_eval("=BASE(10, 1)")).to_contain("#ERR")
expect(_eval("=BASE(10, 37)")).to_contain("#ERR")
expect(_eval("=DECIMAL(\"12\", 2)")).to_contain("#ERR")
```

</details>

### Calc bitwise ops

#### BITAND / BITOR / BITXOR operate on non-negative integers

- BITAND / BITOR / BITXOR operate on non-negative integers
   - Expected: _eval("=BITAND(13, 25)") equals `9`
   - Expected: _eval("=BITOR(13, 25)") equals `29`
   - Expected: _eval("=BITXOR(13, 25)") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BITAND / BITOR / BITXOR operate on non-negative integers")
expect(_eval("=BITAND(13, 25)")).to_equal("9")
expect(_eval("=BITOR(13, 25)")).to_equal("29")
expect(_eval("=BITXOR(13, 25)")).to_equal("20")
```

</details>

#### BITLSHIFT / BITRSHIFT shift by the given count

- BITLSHIFT / BITRSHIFT shift by the given count
   - Expected: _eval("=BITLSHIFT(4, 2)") equals `16`
   - Expected: _eval("=BITRSHIFT(13, 2)") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BITLSHIFT / BITRSHIFT shift by the given count")
expect(_eval("=BITLSHIFT(4, 2)")).to_equal("16")
expect(_eval("=BITRSHIFT(13, 2)")).to_equal("3")
```

</details>

#### bitwise ops fail closed on negative or fractional input

- bitwise ops fail closed on negative or fractional input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bitwise ops fail closed on negative or fractional input")
expect(_eval("=BITAND(-1, 3)")).to_contain("#ERR")
expect(_eval("=BITOR(2.5, 3)")).to_contain("#ERR")
expect(_eval("=BITLSHIFT(-4, 2)")).to_contain("#ERR")
```

</details>

### Calc significance rounding

#### CEILING rounds away from zero to a multiple of significance

- CEILING rounds away from zero to a multiple of significance
   - Expected: _eval("=CEILING(2.5, 1)") equals `3`
   - Expected: _eval("=CEILING(-2.5, -1)") equals `-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING rounds away from zero to a multiple of significance")
expect(_eval("=CEILING(2.5, 1)")).to_equal("3")
expect(_eval("=CEILING(-2.5, -1)")).to_equal("-3")
```

</details>

#### FLOOR rounds toward zero to a multiple of significance

- FLOOR rounds toward zero to a multiple of significance
   - Expected: _eval("=FLOOR(3.7, 2)") equals `2`
   - Expected: _eval("=FLOOR(-2.5, -1)") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FLOOR rounds toward zero to a multiple of significance")
expect(_eval("=FLOOR(3.7, 2)")).to_equal("2")
expect(_eval("=FLOOR(-2.5, -1)")).to_equal("-2")
```

</details>

#### CEILING / FLOOR fail closed on sign mismatch (positive num, negative sig)

- CEILING / FLOOR fail closed on sign mismatch (positive num, negative sig)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CEILING / FLOOR fail closed on sign mismatch (positive num, negative sig)")
expect(_eval("=CEILING(2.5, -1)")).to_contain("#ERR")
expect(_eval("=FLOOR(2.5, -1)")).to_contain("#ERR")
```

</details>

#### TRUNC and INT drop the fraction (INT floors, TRUNC toward zero)

- TRUNC and INT drop the fraction (INT floors, TRUNC toward zero)
   - Expected: _eval("=TRUNC(-8.9)") equals `-8`
   - Expected: _eval("=TRUNC(3.14159, 2)") equals `3.14`
   - Expected: _eval("=INT(-8.9)") equals `-9`
   - Expected: _eval("=INT(8.9)") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TRUNC and INT drop the fraction (INT floors, TRUNC toward zero)")
expect(_eval("=TRUNC(-8.9)")).to_equal("-8")
expect(_eval("=TRUNC(3.14159, 2)")).to_equal("3.14")
expect(_eval("=INT(-8.9)")).to_equal("-9")
expect(_eval("=INT(8.9)")).to_equal("8")
```

</details>

### Calc date-niche functions

#### EOMONTH returns the last day of the shifted month

- EOMONTH returns the last day of the shifted month
   - Expected: _eval("=YEAR(EOMONTH(DATE(2026, 1, 15), 1))") equals `2026`
   - Expected: _eval("=MONTH(EOMONTH(DATE(2026, 1, 15), 1))") equals `2`
   - Expected: _eval("=DAY(EOMONTH(DATE(2026, 1, 15), 1))") equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EOMONTH returns the last day of the shifted month")
expect(_eval("=YEAR(EOMONTH(DATE(2026, 1, 15), 1))")).to_equal("2026")
expect(_eval("=MONTH(EOMONTH(DATE(2026, 1, 15), 1))")).to_equal("2")
expect(_eval("=DAY(EOMONTH(DATE(2026, 1, 15), 1))")).to_equal("28")
```

</details>

#### WEEKNUM (system 1) puts Jan 1 in week 1

- WEEKNUM (system 1) puts Jan 1 in week 1
   - Expected: _eval("=WEEKNUM(DATE(2026, 1, 1))") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WEEKNUM (system 1) puts Jan 1 in week 1")
expect(_eval("=WEEKNUM(DATE(2026, 1, 1))")).to_equal("1")
```

</details>

#### NETWORKDAYS counts inclusive Mon-Fri working days

- NETWORKDAYS counts inclusive Mon-Fri working days
   - Expected: _eval("=NETWORKDAYS(DATE(2026, 7, 1), DATE(2026, 7, 10))") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NETWORKDAYS counts inclusive Mon-Fri working days")
expect(_eval("=NETWORKDAYS(DATE(2026, 7, 1), DATE(2026, 7, 10))")).to_equal("8")
```

</details>

#### WORKDAY skips weekends when advancing

- WORKDAY skips weekends when advancing
   - Expected: _eval("=YEAR(WORKDAY(DATE(2026, 7, 3), 1))") equals `2026`
   - Expected: _eval("=MONTH(WORKDAY(DATE(2026, 7, 3), 1))") equals `7`
   - Expected: _eval("=DAY(WORKDAY(DATE(2026, 7, 3), 1))") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WORKDAY skips weekends when advancing")
expect(_eval("=YEAR(WORKDAY(DATE(2026, 7, 3), 1))")).to_equal("2026")
expect(_eval("=MONTH(WORKDAY(DATE(2026, 7, 3), 1))")).to_equal("7")
expect(_eval("=DAY(WORKDAY(DATE(2026, 7, 3), 1))")).to_equal("6")
```

</details>

#### DATEDIF measures whole years / months / days

- DATEDIF measures whole years / months / days
   - Expected: _eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"Y\")") equals `2`
   - Expected: _eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"M\")") equals `29`
   - Expected: _eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"D\")") equals `900`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DATEDIF measures whole years / months / days")
expect(_eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"Y\")")).to_equal("2")
expect(_eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"M\")")).to_equal("29")
expect(_eval("=DATEDIF(DATE(2024, 1, 15), DATE(2026, 7, 3), \"D\")")).to_equal("900")
```

</details>

#### DATEDIF fails closed on an unknown unit

- DATEDIF fails closed on an unknown unit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DATEDIF fails closed on an unknown unit")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `284417516322bbf0e64c4408aaac9666c83e3fecaaa62a6a35a0aec609602022`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `284417516322bbf0e64c4408aaac9666c83e3fecaaa62a6a35a0aec609602022`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `284417516322bbf0e64c4408aaac9666c83e3fecaaa62a6a35a0aec609602022`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_eng_date_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_eng_date_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_eng_date_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_eng_date_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_eng_date_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DEC2BIN / DEC2OCT / DEC2HEX render integers in the target radix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_eng_date_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DEC2* fail closed on negative or fractional input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_eng_date_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BIN2DEC / OCT2DEC / HEX2DEC parse digit strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
