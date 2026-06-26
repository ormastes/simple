# Regex Character Utilities Coverage Specification

> Tests all exported functions from `src/lib/common/regex_engine/char_utils.spl` targeting 90%+ branch coverage. Each function is tested with inputs that exercise both true and false branches, boundary values, and edge cases.

<!-- sdn-diagram:id=regex_char_utils_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=regex_char_utils_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

regex_char_utils_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=regex_char_utils_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 366 | 366 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Regex Character Utilities Coverage Specification

Tests all exported functions from `src/lib/common/regex_engine/char_utils.spl` targeting 90%+ branch coverage. Each function is tested with inputs that exercise both true and false branches, boundary values, and edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REGEX-CHAR-UTILS |
| Category | Testing / Coverage |
| Status | Implemented |
| Source | `test/01_unit/lib/common/regex_char_utils_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests all exported functions from `src/lib/common/regex_engine/char_utils.spl`
targeting 90%+ branch coverage. Each function is tested with inputs that exercise
both true and false branches, boundary values, and edge cases.

## Scenarios

### char_code

#### digits

#### returns 48 for '0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("0")).to_equal(48)
```

</details>

#### returns 57 for '9'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("9")).to_equal(57)
```

</details>

#### returns 53 for '5'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("5")).to_equal(53)
```

</details>

#### uppercase letters

#### returns 65 for 'A'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("A")).to_equal(65)
```

</details>

#### returns 90 for 'Z'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("Z")).to_equal(90)
```

</details>

#### returns 77 for 'M'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("M")).to_equal(77)
```

</details>

#### lowercase letters

#### returns 97 for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("a")).to_equal(97)
```

</details>

#### returns 122 for 'z'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("z")).to_equal(122)
```

</details>

#### returns 109 for 'm'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("m")).to_equal(109)
```

</details>

#### special characters

#### returns 32 for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code(" ")).to_equal(32)
```

</details>

#### returns 33 for '!'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("!")).to_equal(33)
```

</details>

#### returns 46 for '.'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code(".")).to_equal(46)
```

</details>

#### returns 64 for '@'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("@")).to_equal(64)
```

</details>

#### returns 95 for '_'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("_")).to_equal(95)
```

</details>

#### returns 92 for backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("\\")).to_equal(92)
```

</details>

#### returns 91 for '['

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("[")).to_equal(91)
```

</details>

#### returns 93 for ']'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("]")).to_equal(93)
```

</details>

#### returns 123 for '{'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("{")).to_equal(123)
```

</details>

#### returns 125 for '}'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("}")).to_equal(125)
```

</details>

#### returns 124 for '|'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("|")).to_equal(124)
```

</details>

#### returns 94 for '^'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("^")).to_equal(94)
```

</details>

#### returns 36 for '$'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("$")).to_equal(36)
```

</details>

#### returns 126 for '~'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("~")).to_equal(126)
```

</details>

#### returns 34 for double quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("\"")).to_equal(34)
```

</details>

#### returns 39 for single quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("'")).to_equal(39)
```

</details>

#### returns 40 for '('

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("(")).to_equal(40)
```

</details>

#### returns 41 for ')'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code(")")).to_equal(41)
```

</details>

#### returns 42 for '*'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("*")).to_equal(42)
```

</details>

#### returns 43 for '+'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("+")).to_equal(43)
```

</details>

#### returns 44 for ','

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code(",")).to_equal(44)
```

</details>

#### returns 45 for '-'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("-")).to_equal(45)
```

</details>

#### returns 47 for '/'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("/")).to_equal(47)
```

</details>

#### returns 58 for ':'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code(":")).to_equal(58)
```

</details>

#### returns 59 for ';'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code(";")).to_equal(59)
```

</details>

#### returns 60 for '<'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("<")).to_equal(60)
```

</details>

#### returns 61 for '='

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("=")).to_equal(61)
```

</details>

#### returns 62 for '>'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code(">")).to_equal(62)
```

</details>

#### returns 63 for '?'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("?")).to_equal(63)
```

</details>

#### returns 35 for '#'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("#")).to_equal(35)
```

</details>

#### returns 37 for '%'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("%")).to_equal(37)
```

</details>

#### returns 38 for '&'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("&")).to_equal(38)
```

</details>

#### returns 96 for backtick

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("`")).to_equal(96)
```

</details>

#### whitespace characters

#### returns 10 for newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("\n")).to_equal(10)
```

</details>

#### returns 9 for tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("\t")).to_equal(9)
```

</details>

#### returns 13 for carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("\r")).to_equal(13)
```

</details>

#### edge cases

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("")).to_equal(0)
```

</details>

### string_from_code

#### digits

#### returns '0' for 48

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(48)).to_equal("0")
```

</details>

#### returns '9' for 57

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(57)).to_equal("9")
```

</details>

#### returns '5' for 53

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(53)).to_equal("5")
```

</details>

#### uppercase letters

#### returns 'A' for 65

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(65)).to_equal("A")
```

</details>

#### returns 'Z' for 90

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(90)).to_equal("Z")
```

</details>

#### returns 'M' for 77

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(77)).to_equal("M")
```

</details>

#### lowercase letters

#### returns 'a' for 97

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(97)).to_equal("a")
```

</details>

#### returns 'z' for 122

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(122)).to_equal("z")
```

</details>

#### returns 'm' for 109

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(109)).to_equal("m")
```

</details>

#### special characters

#### returns space for 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(32)).to_equal(" ")
```

</details>

#### returns '_' for 95

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(95)).to_equal("_")
```

</details>

#### returns backslash for 92

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(92)).to_equal("\\")
```

</details>

#### returns '.' for 46

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(46)).to_equal(".")
```

</details>

#### returns '|' for 124

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(124)).to_equal("|")
```

</details>

#### returns '~' for 126

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(126)).to_equal("~")
```

</details>

#### returns '!' for 33

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(33)).to_equal("!")
```

</details>

#### whitespace

#### returns newline for 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(10)).to_equal("\n")
```

</details>

#### returns tab for 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(9)).to_equal("\t")
```

</details>

#### returns carriage return for 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(13)).to_equal("\r")
```

</details>

#### edge cases - fallback

#### returns empty string for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(0)).to_equal("")
```

</details>

#### returns empty string for 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(255)).to_equal("")
```

</details>

#### returns empty string for negative code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(-1)).to_equal("")
```

</details>

### char_code and string_from_code roundtrip

#### roundtrips digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(char_code("0"))).to_equal("0")
expect(string_from_code(char_code("9"))).to_equal("9")
```

</details>

#### roundtrips uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(char_code("A"))).to_equal("A")
expect(string_from_code(char_code("Z"))).to_equal("Z")
```

</details>

#### roundtrips lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(char_code("a"))).to_equal("a")
expect(string_from_code(char_code("z"))).to_equal("z")
```

</details>

#### roundtrips special chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(char_code("."))).to_equal(".")
expect(string_from_code(char_code("_"))).to_equal("_")
expect(string_from_code(char_code("@"))).to_equal("@")
```

</details>

#### roundtrips whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(char_code("\n"))).to_equal("\n")
expect(string_from_code(char_code("\t"))).to_equal("\t")
```

</details>

### is_digit_char

#### true branch - digit characters

#### returns true for '0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("0")).to_equal(true)
```

</details>

#### returns true for '9'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("9")).to_equal(true)
```

</details>

#### returns true for '5'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("5")).to_equal(true)
```

</details>

#### returns true for '1'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("1")).to_equal(true)
```

</details>

#### false branch - non-digit characters

#### returns false for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("a")).to_equal(false)
```

</details>

#### returns false for 'Z'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("Z")).to_equal(false)
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

#### returns false for '.'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char(".")).to_equal(false)
```

</details>

#### returns false for '_'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("_")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("")).to_equal(false)
```

</details>

#### boundary values

#### returns false for '/' (code 47, just below 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("/")).to_equal(false)
```

</details>

#### returns false for ':' (code 58, just above 9)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char(":")).to_equal(false)
```

</details>

### is_alpha_char

#### true branch - uppercase letters

#### returns true for 'A'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("A")).to_equal(true)
```

</details>

#### returns true for 'Z'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("Z")).to_equal(true)
```

</details>

#### returns true for 'M'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("M")).to_equal(true)
```

</details>

#### true branch - lowercase letters

#### returns true for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("a")).to_equal(true)
```

</details>

#### returns true for 'z'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("z")).to_equal(true)
```

</details>

#### returns true for 'm'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("m")).to_equal(true)
```

</details>

#### false branch - non-alphabetic characters

#### returns false for '0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("0")).to_equal(false)
```

</details>

#### returns false for '9'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("9")).to_equal(false)
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

#### returns false for '_'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("_")).to_equal(false)
```

</details>

#### returns false for '.'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char(".")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("")).to_equal(false)
```

</details>

#### boundary values

#### returns false for '@' (code 64, just below A)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("@")).to_equal(false)
```

</details>

#### returns false for '[' (code 91, just above Z)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("[")).to_equal(false)
```

</details>

#### returns false for '`' (code 96, just below a)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("`")).to_equal(false)
```

</details>

#### returns false for '{' (code 123, just above z)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("{")).to_equal(false)
```

</details>

### is_alnum_char

#### true via alpha branch

#### returns true for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("a")).to_equal(true)
```

</details>

#### returns true for 'Z'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("Z")).to_equal(true)
```

</details>

#### true via digit branch

#### returns true for '0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("0")).to_equal(true)
```

</details>

#### returns true for '9'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("9")).to_equal(true)
```

</details>

#### false branch

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char(" ")).to_equal(false)
```

</details>

#### returns false for '_'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("_")).to_equal(false)
```

</details>

#### returns false for '.'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char(".")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("")).to_equal(false)
```

</details>

### is_word_char

#### true via alnum branch

#### returns true for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("a")).to_equal(true)
```

</details>

#### returns true for 'Z'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("Z")).to_equal(true)
```

</details>

#### returns true for '5'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("5")).to_equal(true)
```

</details>

#### true via underscore branch

#### returns true for '_'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("_")).to_equal(true)
```

</details>

#### false branch

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char(" ")).to_equal(false)
```

</details>

#### returns false for '.'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char(".")).to_equal(false)
```

</details>

#### returns false for '-'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("-")).to_equal(false)
```

</details>

#### returns false for '@'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("@")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_word_char("")).to_equal(false)
```

</details>

### is_whitespace_char

#### true branch - each whitespace type

#### returns true for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char(" ")).to_equal(true)
```

</details>

#### returns true for tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("\t")).to_equal(true)
```

</details>

#### returns true for newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("\n")).to_equal(true)
```

</details>

#### returns true for carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("\r")).to_equal(true)
```

</details>

#### false branch

#### returns false for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("a")).to_equal(false)
```

</details>

#### returns false for '0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("0")).to_equal(false)
```

</details>

#### returns false for '_'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("_")).to_equal(false)
```

</details>

#### returns false for '.'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char(".")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("")).to_equal(false)
```

</details>

### is_hex_char

#### true via numeric branch (0-9)

#### returns true for '0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("0")).to_equal(true)
```

</details>

#### returns true for '9'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("9")).to_equal(true)
```

</details>

#### returns true for '5'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("5")).to_equal(true)
```

</details>

#### true via uppercase branch (A-F)

#### returns true for 'A'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("A")).to_equal(true)
```

</details>

#### returns true for 'F'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("F")).to_equal(true)
```

</details>

#### returns true for 'C'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("C")).to_equal(true)
```

</details>

#### true via lowercase branch (a-f)

#### returns true for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("a")).to_equal(true)
```

</details>

#### returns true for 'f'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("f")).to_equal(true)
```

</details>

#### returns true for 'c'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("c")).to_equal(true)
```

</details>

#### false branch - non-hex characters

#### returns false for 'g'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("g")).to_equal(false)
```

</details>

#### returns false for 'G'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("G")).to_equal(false)
```

</details>

#### returns false for 'z'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("z")).to_equal(false)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char(" ")).to_equal(false)
```

</details>

#### returns false for '_'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("_")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("")).to_equal(false)
```

</details>

#### boundary values

#### returns false for '/' (code 47, just below 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("/")).to_equal(false)
```

</details>

#### returns false for ':' (code 58, just above 9)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char(":")).to_equal(false)
```

</details>

#### returns false for '@' (code 64, just below A)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("@")).to_equal(false)
```

</details>

#### returns false for 'G' (code 71, just above F)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("G")).to_equal(false)
```

</details>

#### returns false for '`' (code 96, just below a)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("`")).to_equal(false)
```

</details>

#### returns false for 'g' (code 103, just above f)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_hex_char("g")).to_equal(false)
```

</details>

### is_special_regex_char

#### true branch - all regex metacharacters

#### returns true for '.'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char(".")).to_equal(true)
```

</details>

#### returns true for '*'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("*")).to_equal(true)
```

</details>

#### returns true for '+'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("+")).to_equal(true)
```

</details>

#### returns true for '?'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("?")).to_equal(true)
```

</details>

#### returns true for '|'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("|")).to_equal(true)
```

</details>

#### returns true for '('

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("(")).to_equal(true)
```

</details>

#### returns true for ')'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char(")")).to_equal(true)
```

</details>

#### returns true for '['

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("[")).to_equal(true)
```

</details>

#### returns true for ']'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("]")).to_equal(true)
```

</details>

#### returns true for '{'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("{")).to_equal(true)
```

</details>

#### returns true for '}'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("}")).to_equal(true)
```

</details>

#### returns true for '^'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("^")).to_equal(true)
```

</details>

#### returns true for '$'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("$")).to_equal(true)
```

</details>

#### returns true for backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("\\")).to_equal(true)
```

</details>

#### false branch - non-metacharacters

#### returns false for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("a")).to_equal(false)
```

</details>

#### returns false for '0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("0")).to_equal(false)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char(" ")).to_equal(false)
```

</details>

#### returns false for '_'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("_")).to_equal(false)
```

</details>

#### returns false for '-'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("-")).to_equal(false)
```

</details>

#### returns false for '@'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("@")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_special_regex_char("")).to_equal(false)
```

</details>

### escape_regex

#### strings with special characters

#### escapes a dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex(".")).to_equal("\\.")
```

</details>

#### escapes a star

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("*")).to_equal("\\*")
```

</details>

#### escapes parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("()")).to_equal("\\(\\)")
```

</details>

#### escapes brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("[]")).to_equal("\\[\\]")
```

</details>

#### escapes braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("{}")).to_equal("\\{\\}")
```

</details>

#### escapes caret and dollar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("^$")).to_equal("\\^\\$")
```

</details>

#### escapes pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("|")).to_equal("\\|")
```

</details>

#### escapes plus and question mark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("+?")).to_equal("\\+\\?")
```

</details>

#### escapes backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("\\")).to_equal("\\\\")
```

</details>

#### strings without special characters

#### returns plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("hello")).to_equal("hello")
```

</details>

#### returns digits unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("12345")).to_equal("12345")
```

</details>

#### mixed content

#### escapes only special chars in mixed string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("a.b")).to_equal("a\\.b")
```

</details>

#### escapes multiple special chars among normal text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("a+b*c")).to_equal("a\\+b\\*c")
```

</details>

#### edge cases

#### returns empty string for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("")).to_equal("")
```

</details>

#### handles single normal character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_regex("x")).to_equal("x")
```

</details>

### unescape_regex

#### escaped special characters

#### unescapes a dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("\\.")).to_equal(".")
```

</details>

#### unescapes a star

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("\\*")).to_equal("*")
```

</details>

#### unescapes parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("\\(\\)")).to_equal("()")
```

</details>

#### unescapes brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("\\[\\]")).to_equal("[]")
```

</details>

#### normal characters pass through

#### returns plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("hello")).to_equal("hello")
```

</details>

#### returns digits unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("12345")).to_equal("12345")
```

</details>

#### mixed content

#### unescapes only escaped chars in mixed string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("a\\.b")).to_equal("a.b")
```

</details>

#### handles multiple escaped chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("a\\+b\\*c")).to_equal("a+b*c")
```

</details>

#### trailing backslash

#### preserves trailing backslash when no char follows

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("abc\\")).to_equal("abc\\")
```

</details>

#### handles lone backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("\\")).to_equal("\\")
```

</details>

#### edge cases

#### returns empty string for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("")).to_equal("")
```

</details>

#### unescapes escaped backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex("\\\\")).to_equal("\\")
```

</details>

### expand_escape

#### literal escapes

#### expands 'n' to newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("n")).to_equal("\n")
```

</details>

#### expands 't' to tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("t")).to_equal("\t")
```

</details>

#### expands 'r' to carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("r")).to_equal("\r")
```

</details>

#### character class escapes

#### expands 'd' to digit class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("d")).to_equal("[0-9]")
```

</details>

#### expands 'D' to non-digit class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("D")).to_equal("[^0-9]")
```

</details>

#### expands 'w' to word class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("w")).to_equal("[a-zA-Z0-9_]")
```

</details>

#### expands 'W' to non-word class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("W")).to_equal("[^a-zA-Z0-9_]")
```

</details>

#### expands 's' to whitespace class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("s")).to_equal("[ \t\n\r]")
```

</details>

#### expands 'S' to non-whitespace class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("S")).to_equal("[^ \t\n\r]")
```

</details>

#### boundary escapes

#### expands 'b' to word boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("b")).to_equal("\\b")
```

</details>

#### expands 'B' to non-word boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("B")).to_equal("\\B")
```

</details>

#### fallback - unrecognized escapes

#### returns 'x' unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("x")).to_equal("x")
```

</details>

#### returns 'a' unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("a")).to_equal("a")
```

</details>

#### returns '.' unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape(".")).to_equal(".")
```

</details>

#### returns empty string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("")).to_equal("")
```

</details>

#### returns '1' unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expand_escape("1")).to_equal("1")
```

</details>

### is_escape_char

#### true branch - all recognized escape characters

#### returns true for 'n'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("n")).to_equal(true)
```

</details>

#### returns true for 't'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("t")).to_equal(true)
```

</details>

#### returns true for 'r'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("r")).to_equal(true)
```

</details>

#### returns true for 'd'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("d")).to_equal(true)
```

</details>

#### returns true for 'D'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("D")).to_equal(true)
```

</details>

#### returns true for 'w'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("w")).to_equal(true)
```

</details>

#### returns true for 'W'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("W")).to_equal(true)
```

</details>

#### returns true for 's'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("s")).to_equal(true)
```

</details>

#### returns true for 'S'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("S")).to_equal(true)
```

</details>

#### returns true for 'b'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("b")).to_equal(true)
```

</details>

#### returns true for 'B'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("B")).to_equal(true)
```

</details>

#### false branch - non-escape characters

#### returns false for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("a")).to_equal(false)
```

</details>

#### returns false for 'x'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("x")).to_equal(false)
```

</details>

#### returns false for '0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("0")).to_equal(false)
```

</details>

#### returns false for '.'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char(".")).to_equal(false)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char("")).to_equal(false)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_escape_char(" ")).to_equal(false)
```

</details>

### escape and unescape roundtrip

#### roundtrips plain text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "hello world"
expect(unescape_regex(escape_regex(original))).to_equal(original)
```

</details>

#### roundtrips string with dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "a.b.c"
expect(unescape_regex(escape_regex(original))).to_equal(original)
```

</details>

#### roundtrips string with all metacharacters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = ".*+?|()[]{}^$"
expect(unescape_regex(escape_regex(original))).to_equal(original)
```

</details>

#### roundtrips empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unescape_regex(escape_regex(""))).to_equal("")
```

</details>

#### roundtrips mixed content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "foo(bar)+baz*"
expect(unescape_regex(escape_regex(original))).to_equal(original)
```

</details>

### char_code all uppercase letters

#### returns 66 for 'B'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("B")).to_equal(66)
```

</details>

#### returns 67 for 'C'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("C")).to_equal(67)
```

</details>

#### returns 68 for 'D'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("D")).to_equal(68)
```

</details>

#### returns 69 for 'E'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("E")).to_equal(69)
```

</details>

#### returns 70 for 'F'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("F")).to_equal(70)
```

</details>

#### returns 71 for 'G'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("G")).to_equal(71)
```

</details>

#### returns 72 for 'H'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("H")).to_equal(72)
```

</details>

#### returns 73 for 'I'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("I")).to_equal(73)
```

</details>

#### returns 74 for 'J'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("J")).to_equal(74)
```

</details>

#### returns 75 for 'K'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("K")).to_equal(75)
```

</details>

#### returns 76 for 'L'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("L")).to_equal(76)
```

</details>

#### returns 78 for 'N'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("N")).to_equal(78)
```

</details>

#### returns 79 for 'O'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("O")).to_equal(79)
```

</details>

#### returns 80 for 'P'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("P")).to_equal(80)
```

</details>

#### returns 81 for 'Q'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("Q")).to_equal(81)
```

</details>

#### returns 82 for 'R'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("R")).to_equal(82)
```

</details>

#### returns 83 for 'S'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("S")).to_equal(83)
```

</details>

#### returns 84 for 'T'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("T")).to_equal(84)
```

</details>

#### returns 85 for 'U'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("U")).to_equal(85)
```

</details>

#### returns 86 for 'V'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("V")).to_equal(86)
```

</details>

#### returns 87 for 'W'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("W")).to_equal(87)
```

</details>

#### returns 88 for 'X'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("X")).to_equal(88)
```

</details>

#### returns 89 for 'Y'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("Y")).to_equal(89)
```

</details>

### char_code all lowercase letters

#### returns 98 for 'b'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("b")).to_equal(98)
```

</details>

#### returns 99 for 'c'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("c")).to_equal(99)
```

</details>

#### returns 100 for 'd'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("d")).to_equal(100)
```

</details>

#### returns 101 for 'e'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("e")).to_equal(101)
```

</details>

#### returns 102 for 'f'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("f")).to_equal(102)
```

</details>

#### returns 103 for 'g'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("g")).to_equal(103)
```

</details>

#### returns 104 for 'h'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("h")).to_equal(104)
```

</details>

#### returns 105 for 'i'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("i")).to_equal(105)
```

</details>

#### returns 106 for 'j'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("j")).to_equal(106)
```

</details>

#### returns 107 for 'k'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("k")).to_equal(107)
```

</details>

#### returns 108 for 'l'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("l")).to_equal(108)
```

</details>

#### returns 110 for 'n'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("n")).to_equal(110)
```

</details>

#### returns 111 for 'o'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("o")).to_equal(111)
```

</details>

#### returns 112 for 'p'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("p")).to_equal(112)
```

</details>

#### returns 113 for 'q'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("q")).to_equal(113)
```

</details>

#### returns 114 for 'r'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("r")).to_equal(114)
```

</details>

#### returns 115 for 's'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("s")).to_equal(115)
```

</details>

#### returns 116 for 't'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("t")).to_equal(116)
```

</details>

#### returns 117 for 'u'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("u")).to_equal(117)
```

</details>

#### returns 118 for 'v'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("v")).to_equal(118)
```

</details>

#### returns 119 for 'w'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("w")).to_equal(119)
```

</details>

#### returns 120 for 'x'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("x")).to_equal(120)
```

</details>

#### returns 121 for 'y'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("y")).to_equal(121)
```

</details>

### char_code all digits

#### returns 49 for '1'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("1")).to_equal(49)
```

</details>

#### returns 50 for '2'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("2")).to_equal(50)
```

</details>

#### returns 51 for '3'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("3")).to_equal(51)
```

</details>

#### returns 52 for '4'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("4")).to_equal(52)
```

</details>

#### returns 54 for '6'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("6")).to_equal(54)
```

</details>

#### returns 55 for '7'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("7")).to_equal(55)
```

</details>

#### returns 56 for '8'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("8")).to_equal(56)
```

</details>

### string_from_code all uppercase letters

#### returns 'B' for 66

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(66)).to_equal("B")
```

</details>

#### returns 'C' for 67

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(67)).to_equal("C")
```

</details>

#### returns 'D' for 68

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(68)).to_equal("D")
```

</details>

#### returns 'E' for 69

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(69)).to_equal("E")
```

</details>

#### returns 'F' for 70

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(70)).to_equal("F")
```

</details>

#### returns 'G' for 71

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(71)).to_equal("G")
```

</details>

#### returns 'H' for 72

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(72)).to_equal("H")
```

</details>

#### returns 'I' for 73

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(73)).to_equal("I")
```

</details>

#### returns 'J' for 74

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(74)).to_equal("J")
```

</details>

#### returns 'K' for 75

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(75)).to_equal("K")
```

</details>

#### returns 'L' for 76

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(76)).to_equal("L")
```

</details>

#### returns 'N' for 78

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(78)).to_equal("N")
```

</details>

#### returns 'O' for 79

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(79)).to_equal("O")
```

</details>

#### returns 'P' for 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(80)).to_equal("P")
```

</details>

#### returns 'Q' for 81

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(81)).to_equal("Q")
```

</details>

#### returns 'R' for 82

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(82)).to_equal("R")
```

</details>

#### returns 'S' for 83

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(83)).to_equal("S")
```

</details>

#### returns 'T' for 84

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(84)).to_equal("T")
```

</details>

#### returns 'U' for 85

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(85)).to_equal("U")
```

</details>

#### returns 'V' for 86

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(86)).to_equal("V")
```

</details>

#### returns 'W' for 87

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(87)).to_equal("W")
```

</details>

#### returns 'X' for 88

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(88)).to_equal("X")
```

</details>

#### returns 'Y' for 89

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(89)).to_equal("Y")
```

</details>

### string_from_code all lowercase letters

#### returns 'b' for 98

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(98)).to_equal("b")
```

</details>

#### returns 'c' for 99

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(99)).to_equal("c")
```

</details>

#### returns 'd' for 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(100)).to_equal("d")
```

</details>

#### returns 'e' for 101

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(101)).to_equal("e")
```

</details>

#### returns 'f' for 102

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(102)).to_equal("f")
```

</details>

#### returns 'g' for 103

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(103)).to_equal("g")
```

</details>

#### returns 'h' for 104

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(104)).to_equal("h")
```

</details>

#### returns 'i' for 105

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(105)).to_equal("i")
```

</details>

#### returns 'j' for 106

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(106)).to_equal("j")
```

</details>

#### returns 'k' for 107

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(107)).to_equal("k")
```

</details>

#### returns 'l' for 108

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(108)).to_equal("l")
```

</details>

#### returns 'n' for 110

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(110)).to_equal("n")
```

</details>

#### returns 'o' for 111

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(111)).to_equal("o")
```

</details>

#### returns 'p' for 112

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(112)).to_equal("p")
```

</details>

#### returns 'q' for 113

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(113)).to_equal("q")
```

</details>

#### returns 'r' for 114

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(114)).to_equal("r")
```

</details>

#### returns 's' for 115

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(115)).to_equal("s")
```

</details>

#### returns 't' for 116

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(116)).to_equal("t")
```

</details>

#### returns 'u' for 117

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(117)).to_equal("u")
```

</details>

#### returns 'v' for 118

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(118)).to_equal("v")
```

</details>

#### returns 'w' for 119

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(119)).to_equal("w")
```

</details>

#### returns 'x' for 120

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(120)).to_equal("x")
```

</details>

#### returns 'y' for 121

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(121)).to_equal("y")
```

</details>

### string_from_code all digits

#### returns '1' for 49

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(49)).to_equal("1")
```

</details>

#### returns '2' for 50

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(50)).to_equal("2")
```

</details>

#### returns '3' for 51

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(51)).to_equal("3")
```

</details>

#### returns '4' for 52

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(52)).to_equal("4")
```

</details>

#### returns '6' for 54

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(54)).to_equal("6")
```

</details>

#### returns '7' for 55

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(55)).to_equal("7")
```

</details>

#### returns '8' for 56

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(56)).to_equal("8")
```

</details>

### string_from_code all special characters

#### returns double-quote for 34

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(34)).to_equal("\"")
```

</details>

#### returns '#' for 35

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(35)).to_equal("#")
```

</details>

#### returns '$' for 36

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(36)).to_equal("$")
```

</details>

#### returns '%' for 37

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(37)).to_equal("%")
```

</details>

#### returns '&' for 38

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(38)).to_equal("&")
```

</details>

#### returns single-quote for 39

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(39)).to_equal("'")
```

</details>

#### returns '(' for 40

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(40)).to_equal("(")
```

</details>

#### returns ')' for 41

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(41)).to_equal(")")
```

</details>

#### returns '*' for 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(42)).to_equal("*")
```

</details>

#### returns '+' for 43

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(43)).to_equal("+")
```

</details>

#### returns ',' for 44

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(44)).to_equal(",")
```

</details>

#### returns '-' for 45

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(45)).to_equal("-")
```

</details>

#### returns '/' for 47

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(47)).to_equal("/")
```

</details>

#### returns ':' for 58

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(58)).to_equal(":")
```

</details>

#### returns ';' for 59

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(59)).to_equal(";")
```

</details>

#### returns '<' for 60

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(60)).to_equal("<")
```

</details>

#### returns '=' for 61

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(61)).to_equal("=")
```

</details>

#### returns '>' for 62

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(62)).to_equal(">")
```

</details>

#### returns '?' for 63

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(63)).to_equal("?")
```

</details>

#### returns '@' for 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(64)).to_equal("@")
```

</details>

#### returns '[' for 91

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(91)).to_equal("[")
```

</details>

#### returns ']' for 93

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(93)).to_equal("]")
```

</details>

#### returns '^' for 94

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(94)).to_equal("^")
```

</details>

#### returns backtick for 96

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(96)).to_equal("`")
```

</details>

#### returns '{' for 123

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(123)).to_equal("{")
```

</details>

#### returns '}' for 125

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(string_from_code(125)).to_equal("}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 366 |
| Active scenarios | 366 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
