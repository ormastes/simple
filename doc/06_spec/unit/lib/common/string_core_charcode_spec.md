# String Core Char Code Specification

> Purpose: Prove that string_core - char_code_inline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 112 | 112 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Char Code Specification

Purpose: Prove that string_core - char_code_inline.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-STRING-CORE |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/unit/lib/common/string_core_charcode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that string_core - char_code_inline.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### string_core - char_code_inline

#### whitespace characters

#### returns 32 for space

- returns 32 for space
- Verify: returns 32 for space
   - Expected: char_code_inline(" ") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 32 for space")
step("Verify: returns 32 for space")
# @req: REQ-LIB-COMMON-001
expect(char_code_inline(" ")).to_equal(32)
```

</details>

#### returns 10 for newline

- returns 10 for newline
- Verify: returns 10 for newline
   - Expected: char_code_inline("\n") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 10 for newline")
step("Verify: returns 10 for newline")
expect(char_code_inline("\n")).to_equal(10)
```

</details>

#### returns 9 for tab

- returns 9 for tab
- Verify: returns 9 for tab
   - Expected: char_code_inline("\t") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 9 for tab")
step("Verify: returns 9 for tab")
expect(char_code_inline("\t")).to_equal(9)
```

</details>

#### returns 13 for carriage return

- returns 13 for carriage return
- Verify: returns 13 for carriage return
   - Expected: char_code_inline("\r") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 13 for carriage return")
step("Verify: returns 13 for carriage return")
expect(char_code_inline("\r")).to_equal(13)
```

</details>

#### punctuation

#### returns 33 for exclamation

- returns 33 for exclamation
- Verify: returns 33 for exclamation
   - Expected: char_code_inline("!") equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 33 for exclamation")
step("Verify: returns 33 for exclamation")
expect(char_code_inline("!")).to_equal(33)
```

</details>

#### returns 35 for hash

- returns 35 for hash
- Verify: returns 35 for hash
   - Expected: char_code_inline("#") equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 35 for hash")
step("Verify: returns 35 for hash")
expect(char_code_inline("#")).to_equal(35)
```

</details>

#### returns 46 for period

- returns 46 for period
- Verify: returns 46 for period
   - Expected: char_code_inline(".") equals `46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 46 for period")
step("Verify: returns 46 for period")
expect(char_code_inline(".")).to_equal(46)
```

</details>

#### returns 44 for comma

- returns 44 for comma
- Verify: returns 44 for comma
   - Expected: char_code_inline(",") equals `44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 44 for comma")
step("Verify: returns 44 for comma")
expect(char_code_inline(",")).to_equal(44)
```

</details>

#### returns 45 for hyphen

- returns 45 for hyphen
- Verify: returns 45 for hyphen
   - Expected: char_code_inline("-") equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 45 for hyphen")
step("Verify: returns 45 for hyphen")
expect(char_code_inline("-")).to_equal(45)
```

</details>

#### returns 95 for underscore

- returns 95 for underscore
- Verify: returns 95 for underscore
   - Expected: char_code_inline("_") equals `95`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 95 for underscore")
step("Verify: returns 95 for underscore")
expect(char_code_inline("_")).to_equal(95)
```

</details>

#### returns 64 for at-sign

- returns 64 for at-sign
- Verify: returns 64 for at-sign
   - Expected: char_code_inline("@") equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 64 for at-sign")
step("Verify: returns 64 for at-sign")
expect(char_code_inline("@")).to_equal(64)
```

</details>

#### returns 40 for open paren

- returns 40 for open paren
- Verify: returns 40 for open paren
   - Expected: char_code_inline("(") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 40 for open paren")
step("Verify: returns 40 for open paren")
expect(char_code_inline("(")).to_equal(40)
```

</details>

#### returns 41 for close paren

- returns 41 for close paren
- Verify: returns 41 for close paren
   - Expected: char_code_inline(")") equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 41 for close paren")
step("Verify: returns 41 for close paren")
expect(char_code_inline(")")).to_equal(41)
```

</details>

#### returns 91 for open bracket

- returns 91 for open bracket
- Verify: returns 91 for open bracket
   - Expected: char_code_inline("[") equals `91`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 91 for open bracket")
step("Verify: returns 91 for open bracket")
expect(char_code_inline("[")).to_equal(91)
```

</details>

#### returns 93 for close bracket

- returns 93 for close bracket
- Verify: returns 93 for close bracket
   - Expected: char_code_inline("]") equals `93`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 93 for close bracket")
step("Verify: returns 93 for close bracket")
expect(char_code_inline("]")).to_equal(93)
```

</details>

#### returns 123 for open brace

- returns 123 for open brace
- Verify: returns 123 for open brace
   - Expected: char_code_inline("{") equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 123 for open brace")
step("Verify: returns 123 for open brace")
expect(char_code_inline("{")).to_equal(123)
```

</details>

#### returns 125 for close brace

- returns 125 for close brace
- Verify: returns 125 for close brace
   - Expected: char_code_inline("}") equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 125 for close brace")
step("Verify: returns 125 for close brace")
expect(char_code_inline("}")).to_equal(125)
```

</details>

#### returns 124 for pipe

- returns 124 for pipe
- Verify: returns 124 for pipe
   - Expected: char_code_inline("|") equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 124 for pipe")
step("Verify: returns 124 for pipe")
expect(char_code_inline("|")).to_equal(124)
```

</details>

#### returns 126 for tilde

- returns 126 for tilde
- Verify: returns 126 for tilde
   - Expected: char_code_inline("~") equals `126`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 126 for tilde")
step("Verify: returns 126 for tilde")
expect(char_code_inline("~")).to_equal(126)
```

</details>

#### returns 94 for caret

- returns 94 for caret
- Verify: returns 94 for caret
   - Expected: char_code_inline("^") equals `94`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 94 for caret")
step("Verify: returns 94 for caret")
expect(char_code_inline("^")).to_equal(94)
```

</details>

#### returns 36 for dollar

- returns 36 for dollar
- Verify: returns 36 for dollar
   - Expected: char_code_inline("$") equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 36 for dollar")
step("Verify: returns 36 for dollar")
expect(char_code_inline("$")).to_equal(36)
```

</details>

#### returns 37 for percent

- returns 37 for percent
- Verify: returns 37 for percent
   - Expected: char_code_inline("%") equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 37 for percent")
step("Verify: returns 37 for percent")
expect(char_code_inline("%")).to_equal(37)
```

</details>

#### returns 38 for ampersand

- returns 38 for ampersand
- Verify: returns 38 for ampersand
   - Expected: char_code_inline("&") equals `38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 38 for ampersand")
step("Verify: returns 38 for ampersand")
expect(char_code_inline("&")).to_equal(38)
```

</details>

#### returns 42 for asterisk

- returns 42 for asterisk
- Verify: returns 42 for asterisk
   - Expected: char_code_inline("*") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 42 for asterisk")
step("Verify: returns 42 for asterisk")
expect(char_code_inline("*")).to_equal(42)
```

</details>

#### returns 43 for plus

- returns 43 for plus
- Verify: returns 43 for plus
   - Expected: char_code_inline("+") equals `43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 43 for plus")
step("Verify: returns 43 for plus")
expect(char_code_inline("+")).to_equal(43)
```

</details>

#### returns 47 for slash

- returns 47 for slash
- Verify: returns 47 for slash
   - Expected: char_code_inline("/") equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 47 for slash")
step("Verify: returns 47 for slash")
expect(char_code_inline("/")).to_equal(47)
```

</details>

#### returns 58 for colon

- returns 58 for colon
- Verify: returns 58 for colon
   - Expected: char_code_inline(":") equals `58`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 58 for colon")
step("Verify: returns 58 for colon")
expect(char_code_inline(":")).to_equal(58)
```

</details>

#### returns 59 for semicolon

- returns 59 for semicolon
- Verify: returns 59 for semicolon
   - Expected: char_code_inline(";") equals `59`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 59 for semicolon")
step("Verify: returns 59 for semicolon")
expect(char_code_inline(";")).to_equal(59)
```

</details>

#### returns 60 for less-than

- returns 60 for less-than
- Verify: returns 60 for less-than
   - Expected: char_code_inline("<") equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 60 for less-than")
step("Verify: returns 60 for less-than")
expect(char_code_inline("<")).to_equal(60)
```

</details>

#### returns 61 for equals

- returns 61 for equals
- Verify: returns 61 for equals
   - Expected: char_code_inline("=") equals `61`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 61 for equals")
step("Verify: returns 61 for equals")
expect(char_code_inline("=")).to_equal(61)
```

</details>

#### returns 62 for greater-than

- returns 62 for greater-than
- Verify: returns 62 for greater-than
   - Expected: char_code_inline(">") equals `62`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 62 for greater-than")
step("Verify: returns 62 for greater-than")
expect(char_code_inline(">")).to_equal(62)
```

</details>

#### returns 39 for single quote

- returns 39 for single quote
- Verify: returns 39 for single quote
   - Expected: char_code_inline("'") equals `39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 39 for single quote")
step("Verify: returns 39 for single quote")
expect(char_code_inline("'")).to_equal(39)
```

</details>

#### digits

#### returns 48 for 0

- returns 48 for 0
- Verify: returns 48 for 0
   - Expected: char_code_inline("0") equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 48 for 0")
step("Verify: returns 48 for 0")
expect(char_code_inline("0")).to_equal(48)
```

</details>

#### returns 53 for 5

- returns 53 for 5
- Verify: returns 53 for 5
   - Expected: char_code_inline("5") equals `53`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 53 for 5")
step("Verify: returns 53 for 5")
expect(char_code_inline("5")).to_equal(53)
```

</details>

#### returns 57 for 9

- returns 57 for 9
- Verify: returns 57 for 9
   - Expected: char_code_inline("9") equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 57 for 9")
step("Verify: returns 57 for 9")
expect(char_code_inline("9")).to_equal(57)
```

</details>

#### uppercase letters

#### returns 65 for A

- returns 65 for A
- Verify: returns 65 for A
   - Expected: char_code_inline("A") equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 65 for A")
step("Verify: returns 65 for A")
expect(char_code_inline("A")).to_equal(65)
```

</details>

#### returns 77 for M

- returns 77 for M
- Verify: returns 77 for M
   - Expected: char_code_inline("M") equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 77 for M")
step("Verify: returns 77 for M")
expect(char_code_inline("M")).to_equal(77)
```

</details>

#### returns 90 for Z

- returns 90 for Z
- Verify: returns 90 for Z
   - Expected: char_code_inline("Z") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 90 for Z")
step("Verify: returns 90 for Z")
expect(char_code_inline("Z")).to_equal(90)
```

</details>

#### lowercase letters

#### returns 97 for a

- returns 97 for a
- Verify: returns 97 for a
   - Expected: char_code_inline("a") equals `97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 97 for a")
step("Verify: returns 97 for a")
expect(char_code_inline("a")).to_equal(97)
```

</details>

#### returns 109 for m

- returns 109 for m
- Verify: returns 109 for m
   - Expected: char_code_inline("m") equals `109`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 109 for m")
step("Verify: returns 109 for m")
expect(char_code_inline("m")).to_equal(109)
```

</details>

#### returns 122 for z

- returns 122 for z
- Verify: returns 122 for z
   - Expected: char_code_inline("z") equals `122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 122 for z")
step("Verify: returns 122 for z")
expect(char_code_inline("z")).to_equal(122)
```

</details>

#### unknown characters

#### returns 0 for unknown character

- returns 0 for unknown character
- Verify: returns 0 for unknown character
   - Expected: char_code_inline("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for unknown character")
step("Verify: returns 0 for unknown character")
expect(char_code_inline("")).to_equal(0)
```

</details>

#### question mark

#### returns 63 for question mark

- returns 63 for question mark
- Verify: returns 63 for question mark
   - Expected: char_code_inline(qm) equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 63 for question mark")
step("Verify: returns 63 for question mark")
val qm = char_from_code_inline(63)
expect(char_code_inline(qm)).to_equal(63)  # oracle: 63 — named expected value from the requirement
```

</details>

### string_core - char_from_code_inline

#### whitespace codes

#### returns space for 32

- returns space for 32
- Verify: returns space for 32
   - Expected: char_from_code_inline(32) equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns space for 32")
step("Verify: returns space for 32")
expect(char_from_code_inline(32)).to_equal(" ")
```

</details>

#### returns newline for 10

- returns newline for 10
- Verify: returns newline for 10
   - Expected: char_from_code_inline(10) equals `\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns newline for 10")
step("Verify: returns newline for 10")
expect(char_from_code_inline(10)).to_equal("\n")
```

</details>

#### returns tab for 9

- returns tab for 9
- Verify: returns tab for 9
   - Expected: char_from_code_inline(9) equals `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns tab for 9")
step("Verify: returns tab for 9")
expect(char_from_code_inline(9)).to_equal("\t")
```

</details>

#### returns carriage return for 13

- returns carriage return for 13
- Verify: returns carriage return for 13
   - Expected: char_from_code_inline(13) equals `\r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns carriage return for 13")
step("Verify: returns carriage return for 13")
expect(char_from_code_inline(13)).to_equal("\r")
```

</details>

#### punctuation codes

#### returns exclamation for 33

- returns exclamation for 33
- Verify: returns exclamation for 33
   - Expected: char_from_code_inline(33) equals `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exclamation for 33")
step("Verify: returns exclamation for 33")
expect(char_from_code_inline(33)).to_equal("!")
```

</details>

#### returns period for 46

- returns period for 46
- Verify: returns period for 46
   - Expected: char_from_code_inline(46) equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns period for 46")
step("Verify: returns period for 46")
expect(char_from_code_inline(46)).to_equal(".")
```

</details>

#### returns underscore for 95

- returns underscore for 95
- Verify: returns underscore for 95
   - Expected: char_from_code_inline(95) equals `_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns underscore for 95")
step("Verify: returns underscore for 95")
expect(char_from_code_inline(95)).to_equal("_")
```

</details>

#### returns open paren for 40

- returns open paren for 40
- Verify: returns open paren for 40
   - Expected: char_from_code_inline(40) equals `(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns open paren for 40")
step("Verify: returns open paren for 40")
expect(char_from_code_inline(40)).to_equal("(")
```

</details>

#### returns close paren for 41

- returns close paren for 41
- Verify: returns close paren for 41
   - Expected: char_from_code_inline(41) equals `)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns close paren for 41")
step("Verify: returns close paren for 41")
expect(char_from_code_inline(41)).to_equal(")")
```

</details>

#### returns open bracket for 91

- returns open bracket for 91
- Verify: returns open bracket for 91
   - Expected: char_from_code_inline(91) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns open bracket for 91")
step("Verify: returns open bracket for 91")
expect(char_from_code_inline(91)).to_equal("[")
```

</details>

#### returns close bracket for 93

- returns close bracket for 93
- Verify: returns close bracket for 93
   - Expected: char_from_code_inline(93) equals `]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns close bracket for 93")
step("Verify: returns close bracket for 93")
expect(char_from_code_inline(93)).to_equal("]")
```

</details>

#### returns open brace for 123

- returns open brace for 123
- Verify: returns open brace for 123
   - Expected: char_from_code_inline(123) equals `{`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns open brace for 123")
step("Verify: returns open brace for 123")
expect(char_from_code_inline(123)).to_equal("{")
```

</details>

#### returns close brace for 125

- returns close brace for 125
- Verify: returns close brace for 125
   - Expected: char_from_code_inline(125) equals `}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns close brace for 125")
step("Verify: returns close brace for 125")
expect(char_from_code_inline(125)).to_equal("}")
```

</details>

#### returns pipe for 124

- returns pipe for 124
- Verify: returns pipe for 124
   - Expected: char_from_code_inline(124) equals `|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns pipe for 124")
step("Verify: returns pipe for 124")
expect(char_from_code_inline(124)).to_equal("|")
```

</details>

#### returns tilde for 126

- returns tilde for 126
- Verify: returns tilde for 126
   - Expected: char_from_code_inline(126) equals `~`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns tilde for 126")
step("Verify: returns tilde for 126")
expect(char_from_code_inline(126)).to_equal("~")
```

</details>

#### returns caret for 94

- returns caret for 94
- Verify: returns caret for 94
   - Expected: char_from_code_inline(94) equals `^`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns caret for 94")
step("Verify: returns caret for 94")
expect(char_from_code_inline(94)).to_equal("^")
```

</details>

#### returns hash for 35

- returns hash for 35
- Verify: returns hash for 35
   - Expected: char_from_code_inline(35) equals `#`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns hash for 35")
step("Verify: returns hash for 35")
expect(char_from_code_inline(35)).to_equal("#")
```

</details>

#### returns dollar for 36

- returns dollar for 36
- Verify: returns dollar for 36
   - Expected: char_from_code_inline(36) equals `$`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns dollar for 36")
step("Verify: returns dollar for 36")
expect(char_from_code_inline(36)).to_equal("$")
```

</details>

#### returns percent for 37

- returns percent for 37
- Verify: returns percent for 37
   - Expected: char_from_code_inline(37) equals `%`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns percent for 37")
step("Verify: returns percent for 37")
expect(char_from_code_inline(37)).to_equal("%")
```

</details>

#### returns ampersand for 38

- returns ampersand for 38
- Verify: returns ampersand for 38
   - Expected: char_from_code_inline(38) equals `&`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ampersand for 38")
step("Verify: returns ampersand for 38")
expect(char_from_code_inline(38)).to_equal("&")
```

</details>

#### returns single quote for 39

- returns single quote for 39
- Verify: returns single quote for 39
   - Expected: char_from_code_inline(39) equals `'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single quote for 39")
step("Verify: returns single quote for 39")
expect(char_from_code_inline(39)).to_equal("'")
```

</details>

#### returns asterisk for 42

- returns asterisk for 42
- Verify: returns asterisk for 42
   - Expected: char_from_code_inline(42) equals `*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns asterisk for 42")
step("Verify: returns asterisk for 42")
expect(char_from_code_inline(42)).to_equal("*")
```

</details>

#### returns plus for 43

- returns plus for 43
- Verify: returns plus for 43
   - Expected: char_from_code_inline(43) equals `+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns plus for 43")
step("Verify: returns plus for 43")
expect(char_from_code_inline(43)).to_equal("+")
```

</details>

#### returns comma for 44

- returns comma for 44
- Verify: returns comma for 44
   - Expected: char_from_code_inline(44) equals `,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns comma for 44")
step("Verify: returns comma for 44")
expect(char_from_code_inline(44)).to_equal(",")
```

</details>

#### returns hyphen for 45

- returns hyphen for 45
- Verify: returns hyphen for 45
   - Expected: char_from_code_inline(45) equals `-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns hyphen for 45")
step("Verify: returns hyphen for 45")
expect(char_from_code_inline(45)).to_equal("-")
```

</details>

#### returns slash for 47

- returns slash for 47
- Verify: returns slash for 47
   - Expected: char_from_code_inline(47) equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns slash for 47")
step("Verify: returns slash for 47")
expect(char_from_code_inline(47)).to_equal("/")
```

</details>

#### returns colon for 58

- returns colon for 58
- Verify: returns colon for 58
   - Expected: char_from_code_inline(58) equals `:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns colon for 58")
step("Verify: returns colon for 58")
expect(char_from_code_inline(58)).to_equal(":")
```

</details>

#### returns semicolon for 59

- returns semicolon for 59
- Verify: returns semicolon for 59
   - Expected: char_from_code_inline(59) equals `;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns semicolon for 59")
step("Verify: returns semicolon for 59")
expect(char_from_code_inline(59)).to_equal(";")
```

</details>

#### returns less-than for 60

- returns less-than for 60
- Verify: returns less-than for 60
   - Expected: char_from_code_inline(60) equals `<`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns less-than for 60")
step("Verify: returns less-than for 60")
expect(char_from_code_inline(60)).to_equal("<")
```

</details>

#### returns equals for 61

- returns equals for 61
- Verify: returns equals for 61
   - Expected: char_from_code_inline(61) equals `=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns equals for 61")
step("Verify: returns equals for 61")
expect(char_from_code_inline(61)).to_equal("=")
```

</details>

#### returns greater-than for 62

- returns greater-than for 62
- Verify: returns greater-than for 62
   - Expected: char_from_code_inline(62) equals `>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns greater-than for 62")
step("Verify: returns greater-than for 62")
expect(char_from_code_inline(62)).to_equal(">")
```

</details>

#### returns at-sign for 64

- returns at-sign for 64
- Verify: returns at-sign for 64
   - Expected: char_from_code_inline(64) equals `@`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns at-sign for 64")
step("Verify: returns at-sign for 64")
expect(char_from_code_inline(64)).to_equal("@")
```

</details>

#### digit codes

#### returns 0 for 48

- returns 0 for 48
- Verify: returns 0 for 48
   - Expected: char_from_code_inline(48) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for 48")
step("Verify: returns 0 for 48")
expect(char_from_code_inline(48)).to_equal("0")
```

</details>

#### returns 5 for 53

- returns 5 for 53
- Verify: returns 5 for 53
   - Expected: char_from_code_inline(53) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 5 for 53")
step("Verify: returns 5 for 53")
expect(char_from_code_inline(53)).to_equal("5")
```

</details>

#### returns 9 for 57

- returns 9 for 57
- Verify: returns 9 for 57
   - Expected: char_from_code_inline(57) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 9 for 57")
step("Verify: returns 9 for 57")
expect(char_from_code_inline(57)).to_equal("9")
```

</details>

#### uppercase letter codes

#### returns A for 65

- returns A for 65
- Verify: returns A for 65
   - Expected: char_from_code_inline(65) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns A for 65")
step("Verify: returns A for 65")
expect(char_from_code_inline(65)).to_equal("A")
```

</details>

#### returns M for 77

- returns M for 77
- Verify: returns M for 77
   - Expected: char_from_code_inline(77) equals `M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns M for 77")
step("Verify: returns M for 77")
expect(char_from_code_inline(77)).to_equal("M")
```

</details>

#### returns Z for 90

- returns Z for 90
- Verify: returns Z for 90
   - Expected: char_from_code_inline(90) equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Z for 90")
step("Verify: returns Z for 90")
expect(char_from_code_inline(90)).to_equal("Z")
```

</details>

#### lowercase letter codes

#### returns a for 97

- returns a for 97
- Verify: returns a for 97
   - Expected: char_from_code_inline(97) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a for 97")
step("Verify: returns a for 97")
expect(char_from_code_inline(97)).to_equal("a")
```

</details>

#### returns m for 109

- returns m for 109
- Verify: returns m for 109
   - Expected: char_from_code_inline(109) equals `m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns m for 109")
step("Verify: returns m for 109")
expect(char_from_code_inline(109)).to_equal("m")
```

</details>

#### returns z for 122

- returns z for 122
- Verify: returns z for 122
   - Expected: char_from_code_inline(122) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns z for 122")
step("Verify: returns z for 122")
expect(char_from_code_inline(122)).to_equal("z")
```

</details>

#### codes outside the fast ASCII table (now UTF-8 encoded, not dropped)

#### returns empty for negative code

- returns empty for negative code
- Verify: returns empty for negative code
   - Expected: char_from_code_inline(-1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for negative code")
step("Verify: returns empty for negative code")
expect(char_from_code_inline(-1)).to_equal("")
```

</details>

### string_core - Character Classification

#### is_alpha_char

#### returns true for lowercase letter

- returns true for lowercase letter
- Verify: returns true for lowercase letter
   - Expected: is_alpha_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for lowercase letter")
step("Verify: returns true for lowercase letter")
expect(is_alpha_char("a")).to_equal(true)
```

</details>

#### returns true for uppercase letter

- returns true for uppercase letter
- Verify: returns true for uppercase letter
   - Expected: is_alpha_char("Z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for uppercase letter")
step("Verify: returns true for uppercase letter")
expect(is_alpha_char("Z")).to_equal(true)
```

</details>

#### returns true for middle lowercase

- returns true for middle lowercase
- Verify: returns true for middle lowercase
   - Expected: is_alpha_char("m") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for middle lowercase")
step("Verify: returns true for middle lowercase")
expect(is_alpha_char("m")).to_equal(true)
```

</details>

#### returns true for middle uppercase

- returns true for middle uppercase
- Verify: returns true for middle uppercase
   - Expected: is_alpha_char("M") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for middle uppercase")
step("Verify: returns true for middle uppercase")
expect(is_alpha_char("M")).to_equal(true)
```

</details>

#### returns false for digit

- returns false for digit
- Verify: returns false for digit
   - Expected: is_alpha_char("5") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for digit")
step("Verify: returns false for digit")
expect(is_alpha_char("5")).to_equal(false)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_alpha_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for space")
step("Verify: returns false for space")
expect(is_alpha_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

- returns false for punctuation
- Verify: returns false for punctuation
   - Expected: is_alpha_char("!") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for punctuation")
step("Verify: returns false for punctuation")
expect(is_alpha_char("!")).to_equal(false)
```

</details>

#### returns false for underscore

- returns false for underscore
- Verify: returns false for underscore
   - Expected: is_alpha_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for underscore")
step("Verify: returns false for underscore")
expect(is_alpha_char("_")).to_equal(false)
```

</details>

#### is_digit_char

#### returns true for 0

- returns true for 0
- Verify: returns true for 0
   - Expected: is_digit_char("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for 0")
step("Verify: returns true for 0")
expect(is_digit_char("0")).to_equal(true)
```

</details>

#### returns true for 9

- returns true for 9
- Verify: returns true for 9
   - Expected: is_digit_char("9") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for 9")
step("Verify: returns true for 9")
expect(is_digit_char("9")).to_equal(true)
```

</details>

#### returns true for middle digit

- returns true for middle digit
- Verify: returns true for middle digit
   - Expected: is_digit_char("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for middle digit")
step("Verify: returns true for middle digit")
expect(is_digit_char("5")).to_equal(true)
```

</details>

#### returns false for letter

- returns false for letter
- Verify: returns false for letter
   - Expected: is_digit_char("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for letter")
step("Verify: returns false for letter")
expect(is_digit_char("a")).to_equal(false)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_digit_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for space")
step("Verify: returns false for space")
expect(is_digit_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

- returns false for punctuation
- Verify: returns false for punctuation
   - Expected: is_digit_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for punctuation")
step("Verify: returns false for punctuation")
expect(is_digit_char(".")).to_equal(false)
```

</details>

#### is_alnum_char

#### returns true for letter

- returns true for letter
- Verify: returns true for letter
   - Expected: is_alnum_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for letter")
step("Verify: returns true for letter")
expect(is_alnum_char("a")).to_equal(true)
```

</details>

#### returns true for uppercase letter

- returns true for uppercase letter
- Verify: returns true for uppercase letter
   - Expected: is_alnum_char("Z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for uppercase letter")
step("Verify: returns true for uppercase letter")
expect(is_alnum_char("Z")).to_equal(true)
```

</details>

#### returns true for digit

- returns true for digit
- Verify: returns true for digit
   - Expected: is_alnum_char("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for digit")
step("Verify: returns true for digit")
expect(is_alnum_char("5")).to_equal(true)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_alnum_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for space")
step("Verify: returns false for space")
expect(is_alnum_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

- returns false for punctuation
- Verify: returns false for punctuation
   - Expected: is_alnum_char("!") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for punctuation")
step("Verify: returns false for punctuation")
expect(is_alnum_char("!")).to_equal(false)
```

</details>

#### returns false for underscore

- returns false for underscore
- Verify: returns false for underscore
   - Expected: is_alnum_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for underscore")
step("Verify: returns false for underscore")
expect(is_alnum_char("_")).to_equal(false)
```

</details>

### string_core - char_from_code_inline non-ASCII (bug fix regression)

#### invalid-input policy: reject surrogates and out-of-range codepoints

#### returns empty text for the first UTF-16 surrogate (U+D800)

- returns empty text for the first UTF-16 surrogate (U+D800)
- Verify: returns empty text for the first UTF-16 surrogate (U+D800)
   - Expected: char_from_code_inline(0xD800) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for the first UTF-16 surrogate (U+D800)")
step("Verify: returns empty text for the first UTF-16 surrogate (U+D800)")
expect(char_from_code_inline(0xD800)).to_equal("")
```

</details>

#### returns empty text for the last UTF-16 surrogate (U+DFFF)

- returns empty text for the last UTF-16 surrogate (U+DFFF)
- Verify: returns empty text for the last UTF-16 surrogate (U+DFFF)
   - Expected: char_from_code_inline(0xDFFF) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for the last UTF-16 surrogate (U+DFFF)")
step("Verify: returns empty text for the last UTF-16 surrogate (U+DFFF)")
expect(char_from_code_inline(0xDFFF)).to_equal("")
```

</details>

#### returns empty text for a mid-range surrogate (U+DEAD)

- returns empty text for a mid-range surrogate (U+DEAD)
- Verify: returns empty text for a mid-range surrogate (U+DEAD)
   - Expected: char_from_code_inline(0xDEAD) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for a mid-range surrogate (U+DEAD)")
step("Verify: returns empty text for a mid-range surrogate (U+DEAD)")
expect(char_from_code_inline(0xDEAD)).to_equal("")
```

</details>

#### returns empty text for one past the max Unicode codepoint (U+110000)

- returns empty text for one past the max Unicode codepoint (U+110000)
- Verify: returns empty text for one past the max Unicode codepoint (U+110000)
   - Expected: char_from_code_inline(0x110000) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for one past the max Unicode codepoint (U+110000)")
step("Verify: returns empty text for one past the max Unicode codepoint (U+110000)")
expect(char_from_code_inline(0x110000)).to_equal("")
```

</details>

#### returns empty text for a codepoint far out of range

- returns empty text for a codepoint far out of range
- Verify: returns empty text for a codepoint far out of range
   - Expected: char_from_code_inline(0x100000041) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for a codepoint far out of range")
step("Verify: returns empty text for a codepoint far out of range")
expect(char_from_code_inline(0x100000041)).to_equal("")
```

</details>

#### returns empty text for a negative codepoint

- returns empty text for a negative codepoint
- Verify: returns empty text for a negative codepoint
   - Expected: char_from_code_inline(-1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for a negative codepoint")
step("Verify: returns empty text for a negative codepoint")
expect(char_from_code_inline(-1)).to_equal("")
```

</details>

#### char_from_code (public alias) matches char_from_code_inline

#### rejects invalid codepoints the same way as the inline implementation

- rejects invalid codepoints the same way as the inline implementation
- Verify: rejects invalid codepoints the same way as the inline implementation
   - Expected: char_from_code(0xD800) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid codepoints the same way as the inline implementation")
step("Verify: rejects invalid codepoints the same way as the inline implementation")
expect(char_from_code(0xD800)).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 112 |
| Active scenarios | 112 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `937fb8447f5ed3c4981117d0908a7752eefcc8147ea553ecee461534106728a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `937fb8447f5ed3c4981117d0908a7752eefcc8147ea553ecee461534106728a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `937fb8447f5ed3c4981117d0908a7752eefcc8147ea553ecee461534106728a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/string_core_charcode_spec.spl
mirror: doc/06_spec/unit/lib/common/string_core_charcode_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/string_core_charcode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/string_core_charcode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/string_core_charcode_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 42 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/string_core_charcode_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 32 for space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/string_core_charcode_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 10 for newline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/string_core_charcode_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 9 for tab' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
