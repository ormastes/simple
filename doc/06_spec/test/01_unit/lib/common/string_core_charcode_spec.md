# String Core Char Code Specification

> Tests for char_code_inline, char_from_code_inline, and character classification functions (is_alpha_char, is_digit_char, is_alnum_char).

<!-- sdn-diagram:id=string_core_charcode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_core_charcode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_core_charcode_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_core_charcode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 108 | 108 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Char Code Specification

Tests for char_code_inline, char_from_code_inline, and character classification functions (is_alpha_char, is_digit_char, is_alnum_char).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-STRING-CORE |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/string_core_charcode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for char_code_inline, char_from_code_inline, and character classification
functions (is_alpha_char, is_digit_char, is_alnum_char).

## Scenarios

### string_core - char_code_inline

#### whitespace characters

#### returns 32 for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(" ")).to_equal(32)
```

</details>

#### returns 10 for newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("\n")).to_equal(10)
```

</details>

#### returns 9 for tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("\t")).to_equal(9)
```

</details>

#### returns 13 for carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("\r")).to_equal(13)
```

</details>

#### punctuation

#### returns 33 for exclamation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("!")).to_equal(33)
```

</details>

#### returns 35 for hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("#")).to_equal(35)
```

</details>

#### returns 46 for period

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(".")).to_equal(46)
```

</details>

#### returns 44 for comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(",")).to_equal(44)
```

</details>

#### returns 45 for hyphen

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("-")).to_equal(45)
```

</details>

#### returns 95 for underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("_")).to_equal(95)
```

</details>

#### returns 64 for at-sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("@")).to_equal(64)
```

</details>

#### returns 40 for open paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("(")).to_equal(40)
```

</details>

#### returns 41 for close paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(")")).to_equal(41)
```

</details>

#### returns 91 for open bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("[")).to_equal(91)
```

</details>

#### returns 93 for close bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("]")).to_equal(93)
```

</details>

#### returns 123 for open brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("{")).to_equal(123)
```

</details>

#### returns 125 for close brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("}")).to_equal(125)
```

</details>

#### returns 124 for pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("|")).to_equal(124)
```

</details>

#### returns 126 for tilde

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("~")).to_equal(126)
```

</details>

#### returns 94 for caret

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("^")).to_equal(94)
```

</details>

#### returns 36 for dollar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("$")).to_equal(36)
```

</details>

#### returns 37 for percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("%")).to_equal(37)
```

</details>

#### returns 38 for ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("&")).to_equal(38)
```

</details>

#### returns 42 for asterisk

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("*")).to_equal(42)
```

</details>

#### returns 43 for plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("+")).to_equal(43)
```

</details>

#### returns 47 for slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("/")).to_equal(47)
```

</details>

#### returns 58 for colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(":")).to_equal(58)
```

</details>

#### returns 59 for semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(";")).to_equal(59)
```

</details>

#### returns 60 for less-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("<")).to_equal(60)
```

</details>

#### returns 61 for equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("=")).to_equal(61)
```

</details>

#### returns 62 for greater-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(">")).to_equal(62)
```

</details>

#### returns 39 for single quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("'")).to_equal(39)
```

</details>

#### digits

#### returns 48 for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("0")).to_equal(48)
```

</details>

#### returns 53 for 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("5")).to_equal(53)
```

</details>

#### returns 57 for 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("9")).to_equal(57)
```

</details>

#### uppercase letters

#### returns 65 for A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("A")).to_equal(65)
```

</details>

#### returns 77 for M

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("M")).to_equal(77)
```

</details>

#### returns 90 for Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("Z")).to_equal(90)
```

</details>

#### lowercase letters

#### returns 97 for a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("a")).to_equal(97)
```

</details>

#### returns 109 for m

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("m")).to_equal(109)
```

</details>

#### returns 122 for z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("z")).to_equal(122)
```

</details>

#### unknown characters

#### returns 0 for unknown character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("")).to_equal(0)
```

</details>

#### question mark

#### returns 63 for question mark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qm = char_from_code_inline(63)
expect(char_code_inline(qm)).to_equal(63)
```

</details>

### string_core - char_from_code_inline

#### whitespace codes

#### returns space for 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(32)).to_equal(" ")
```

</details>

#### returns newline for 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(10)).to_equal("\n")
```

</details>

#### returns tab for 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(9)).to_equal("\t")
```

</details>

#### returns carriage return for 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(13)).to_equal("\r")
```

</details>

#### punctuation codes

#### returns exclamation for 33

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(33)).to_equal("!")
```

</details>

#### returns period for 46

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(46)).to_equal(".")
```

</details>

#### returns underscore for 95

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(95)).to_equal("_")
```

</details>

#### returns open paren for 40

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(40)).to_equal("(")
```

</details>

#### returns close paren for 41

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(41)).to_equal(")")
```

</details>

#### returns open bracket for 91

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(91)).to_equal("[")
```

</details>

#### returns close bracket for 93

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(93)).to_equal("]")
```

</details>

#### returns open brace for 123

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(123)).to_equal("{")
```

</details>

#### returns close brace for 125

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(125)).to_equal("}")
```

</details>

#### returns pipe for 124

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(124)).to_equal("|")
```

</details>

#### returns tilde for 126

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(126)).to_equal("~")
```

</details>

#### returns caret for 94

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(94)).to_equal("^")
```

</details>

#### returns hash for 35

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(35)).to_equal("#")
```

</details>

#### returns dollar for 36

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(36)).to_equal("$")
```

</details>

#### returns percent for 37

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(37)).to_equal("%")
```

</details>

#### returns ampersand for 38

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(38)).to_equal("&")
```

</details>

#### returns single quote for 39

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(39)).to_equal("'")
```

</details>

#### returns asterisk for 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(42)).to_equal("*")
```

</details>

#### returns plus for 43

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(43)).to_equal("+")
```

</details>

#### returns comma for 44

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(44)).to_equal(",")
```

</details>

#### returns hyphen for 45

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(45)).to_equal("-")
```

</details>

#### returns slash for 47

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(47)).to_equal("/")
```

</details>

#### returns colon for 58

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(58)).to_equal(":")
```

</details>

#### returns semicolon for 59

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(59)).to_equal(";")
```

</details>

#### returns less-than for 60

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(60)).to_equal("<")
```

</details>

#### returns equals for 61

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(61)).to_equal("=")
```

</details>

#### returns greater-than for 62

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(62)).to_equal(">")
```

</details>

#### returns at-sign for 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(64)).to_equal("@")
```

</details>

#### digit codes

#### returns 0 for 48

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(48)).to_equal("0")
```

</details>

#### returns 5 for 53

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(53)).to_equal("5")
```

</details>

#### returns 9 for 57

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(57)).to_equal("9")
```

</details>

#### uppercase letter codes

#### returns A for 65

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(65)).to_equal("A")
```

</details>

#### returns M for 77

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(77)).to_equal("M")
```

</details>

#### returns Z for 90

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(90)).to_equal("Z")
```

</details>

#### lowercase letter codes

#### returns a for 97

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(97)).to_equal("a")
```

</details>

#### returns m for 109

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(109)).to_equal("m")
```

</details>

#### returns z for 122

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(122)).to_equal("z")
```

</details>

#### unknown codes

#### returns empty for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(0)).to_equal("")
```

</details>

#### returns empty for 999

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(999)).to_equal("")
```

</details>

#### returns empty for negative code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(-1)).to_equal("")
```

</details>

#### returns empty for code 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(1)).to_equal("")
```

</details>

### string_core - Character Classification

#### is_alpha_char

#### returns true for lowercase letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("a")).to_equal(true)
```

</details>

#### returns true for uppercase letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("Z")).to_equal(true)
```

</details>

#### returns true for middle lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("m")).to_equal(true)
```

</details>

#### returns true for middle uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("M")).to_equal(true)
```

</details>

#### returns false for digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("5")).to_equal(false)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("!")).to_equal(false)
```

</details>

#### returns false for underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("_")).to_equal(false)
```

</details>

#### is_digit_char

#### returns true for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("0")).to_equal(true)
```

</details>

#### returns true for 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("9")).to_equal(true)
```

</details>

#### returns true for middle digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("5")).to_equal(true)
```

</details>

#### returns false for letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("a")).to_equal(false)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char(".")).to_equal(false)
```

</details>

#### is_alnum_char

#### returns true for letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("a")).to_equal(true)
```

</details>

#### returns true for uppercase letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("Z")).to_equal(true)
```

</details>

#### returns true for digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("5")).to_equal(true)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("!")).to_equal(false)
```

</details>

#### returns false for underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("_")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 108 |
| Active scenarios | 108 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
