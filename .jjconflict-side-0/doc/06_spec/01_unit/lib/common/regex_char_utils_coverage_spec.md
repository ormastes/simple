# Regex Character Utilities Coverage Specification

> Purpose: Prove that char_code.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 366 | 366 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Regex Character Utilities Coverage Specification

Purpose: Prove that char_code.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REGEX-CHAR-UTILS |
| Category | Testing / Coverage |
| Status | Implemented |
| Source | `test/01_unit/lib/common/regex_char_utils_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that char_code.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### char_code

#### digits

#### returns 48 for '0'

- returns 48 for '0'
- Verify: returns 48 for '0'
   - Expected: char_code("0") equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 48 for '0'")
step("Verify: returns 48 for '0'")
# @req: REQ-LIB-COMMON-001
expect(char_code("0")).to_equal(48)
```

</details>

#### returns 57 for '9'

- returns 57 for '9'
- Verify: returns 57 for '9'
   - Expected: char_code("9") equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 57 for '9'")
step("Verify: returns 57 for '9'")
expect(char_code("9")).to_equal(57)
```

</details>

#### returns 53 for '5'

- returns 53 for '5'
- Verify: returns 53 for '5'
   - Expected: char_code("5") equals `53`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 53 for '5'")
step("Verify: returns 53 for '5'")
expect(char_code("5")).to_equal(53)
```

</details>

#### uppercase letters

#### returns 65 for 'A'

- returns 65 for 'A'
- Verify: returns 65 for 'A'
   - Expected: char_code("A") equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 65 for 'A'")
step("Verify: returns 65 for 'A'")
expect(char_code("A")).to_equal(65)
```

</details>

#### returns 90 for 'Z'

- returns 90 for 'Z'
- Verify: returns 90 for 'Z'
   - Expected: char_code("Z") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 90 for 'Z'")
step("Verify: returns 90 for 'Z'")
expect(char_code("Z")).to_equal(90)
```

</details>

#### returns 77 for 'M'

- returns 77 for 'M'
- Verify: returns 77 for 'M'
   - Expected: char_code("M") equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 77 for 'M'")
step("Verify: returns 77 for 'M'")
expect(char_code("M")).to_equal(77)
```

</details>

#### lowercase letters

#### returns 97 for 'a'

- returns 97 for 'a'
- Verify: returns 97 for 'a'
   - Expected: char_code("a") equals `97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 97 for 'a'")
step("Verify: returns 97 for 'a'")
expect(char_code("a")).to_equal(97)
```

</details>

#### returns 122 for 'z'

- returns 122 for 'z'
- Verify: returns 122 for 'z'
   - Expected: char_code("z") equals `122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 122 for 'z'")
step("Verify: returns 122 for 'z'")
expect(char_code("z")).to_equal(122)
```

</details>

#### returns 109 for 'm'

- returns 109 for 'm'
- Verify: returns 109 for 'm'
   - Expected: char_code("m") equals `109`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 109 for 'm'")
step("Verify: returns 109 for 'm'")
expect(char_code("m")).to_equal(109)
```

</details>

#### special characters

#### returns 32 for space

- returns 32 for space
- Verify: returns 32 for space
   - Expected: char_code(" ") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 32 for space")
step("Verify: returns 32 for space")
expect(char_code(" ")).to_equal(32)
```

</details>

#### returns 33 for '!'

- returns 33 for '!'
- Verify: returns 33 for '!'
   - Expected: char_code("!") equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 33 for '!'")
step("Verify: returns 33 for '!'")
expect(char_code("!")).to_equal(33)
```

</details>

#### returns 46 for '.'

- returns 46 for '.'
- Verify: returns 46 for '.'
   - Expected: char_code(".") equals `46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 46 for '.'")
step("Verify: returns 46 for '.'")
expect(char_code(".")).to_equal(46)
```

</details>

#### returns 64 for '@'

- returns 64 for '@'
- Verify: returns 64 for '@'
   - Expected: char_code("@") equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 64 for '@'")
step("Verify: returns 64 for '@'")
expect(char_code("@")).to_equal(64)
```

</details>

#### returns 95 for '_'

- returns 95 for '_'
- Verify: returns 95 for '_'
   - Expected: char_code("_") equals `95`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 95 for '_'")
step("Verify: returns 95 for '_'")
expect(char_code("_")).to_equal(95)
```

</details>

#### returns 92 for backslash

- returns 92 for backslash
- Verify: returns 92 for backslash
   - Expected: char_code("\\") equals `92`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 92 for backslash")
step("Verify: returns 92 for backslash")
expect(char_code("\\")).to_equal(92)
```

</details>

#### returns 91 for '['

- returns 91 for '['
- Verify: returns 91 for '['
   - Expected: char_code("[") equals `91`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 91 for '['")
step("Verify: returns 91 for '['")
expect(char_code("[")).to_equal(91)
```

</details>

#### returns 93 for ']'

- returns 93 for ']'
- Verify: returns 93 for ']'
   - Expected: char_code("]") equals `93`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 93 for ']'")
step("Verify: returns 93 for ']'")
expect(char_code("]")).to_equal(93)
```

</details>

#### returns 123 for '{'

- returns 123 for '{'
- Verify: returns 123 for '('
   - Expected: char_code("{") equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 123 for '{'")
step("Verify: returns 123 for '('")
expect(char_code("{")).to_equal(123)
```

</details>

#### returns 125 for '}'

- returns 125 for '}'
- Verify: returns 125 for ')'
   - Expected: char_code("}") equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 125 for '}'")
step("Verify: returns 125 for ')'")
expect(char_code("}")).to_equal(125)
```

</details>

#### returns 124 for '|'

- returns 124 for '|'
- Verify: returns 124 for '|'
   - Expected: char_code("|") equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 124 for '|'")
step("Verify: returns 124 for '|'")
expect(char_code("|")).to_equal(124)
```

</details>

#### returns 94 for '^'

- returns 94 for '^'
- Verify: returns 94 for '^'
   - Expected: char_code("^") equals `94`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 94 for '^'")
step("Verify: returns 94 for '^'")
expect(char_code("^")).to_equal(94)
```

</details>

#### returns 36 for '$'

- returns 36 for '$'
- Verify: returns 36 for '$'
   - Expected: char_code("$") equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 36 for '$'")
step("Verify: returns 36 for '$'")
expect(char_code("$")).to_equal(36)
```

</details>

#### returns 126 for '~'

- returns 126 for '~'
- Verify: returns 126 for '~'
   - Expected: char_code("~") equals `126`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 126 for '~'")
step("Verify: returns 126 for '~'")
expect(char_code("~")).to_equal(126)
```

</details>

#### returns 34 for double quote

- returns 34 for double quote
- Verify: returns 34 for double quote
   - Expected: char_code("\"") equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 34 for double quote")
step("Verify: returns 34 for double quote")
expect(char_code("\"")).to_equal(34)
```

</details>

#### returns 39 for single quote

- returns 39 for single quote
- Verify: returns 39 for single quote
   - Expected: char_code("'") equals `39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 39 for single quote")
step("Verify: returns 39 for single quote")
expect(char_code("'")).to_equal(39)
```

</details>

#### returns 40 for '('

- returns 40 for '('
- Verify: returns 40 for '('
   - Expected: char_code("(") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 40 for '('")
step("Verify: returns 40 for '('")
expect(char_code("(")).to_equal(40)
```

</details>

#### returns 41 for ')'

- returns 41 for ')'
- Verify: returns 41 for ')'
   - Expected: char_code(")") equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 41 for ')'")
step("Verify: returns 41 for ')'")
expect(char_code(")")).to_equal(41)
```

</details>

#### returns 42 for '*'

- returns 42 for '*'
- Verify: returns 42 for '*'
   - Expected: char_code("*") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 42 for '*'")
step("Verify: returns 42 for '*'")
expect(char_code("*")).to_equal(42)
```

</details>

#### returns 43 for '+'

- returns 43 for '+'
- Verify: returns 43 for '+'
   - Expected: char_code("+") equals `43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 43 for '+'")
step("Verify: returns 43 for '+'")
expect(char_code("+")).to_equal(43)
```

</details>

#### returns 44 for ','

- returns 44 for ','
- Verify: returns 44 for ','
   - Expected: char_code(",") equals `44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 44 for ','")
step("Verify: returns 44 for ','")
expect(char_code(",")).to_equal(44)
```

</details>

#### returns 45 for '-'

- returns 45 for '-'
- Verify: returns 45 for '-'
   - Expected: char_code("-") equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 45 for '-'")
step("Verify: returns 45 for '-'")
expect(char_code("-")).to_equal(45)
```

</details>

#### returns 47 for '/'

- returns 47 for '/'
- Verify: returns 47 for '/'
   - Expected: char_code("/") equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 47 for '/'")
step("Verify: returns 47 for '/'")
expect(char_code("/")).to_equal(47)
```

</details>

#### returns 58 for ':'

- returns 58 for ':'
- Verify: returns 58 for ':'
   - Expected: char_code(":") equals `58`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 58 for ':'")
step("Verify: returns 58 for ':'")
expect(char_code(":")).to_equal(58)
```

</details>

#### returns 59 for ';'

- returns 59 for ';'
- Verify: returns 59 for ';'
   - Expected: char_code(";") equals `59`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 59 for ';'")
step("Verify: returns 59 for ';'")
expect(char_code(";")).to_equal(59)
```

</details>

#### returns 60 for '<'

- returns 60 for '<'
- Verify: returns 60 for '<'
   - Expected: char_code("<") equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 60 for '<'")
step("Verify: returns 60 for '<'")
expect(char_code("<")).to_equal(60)
```

</details>

#### returns 61 for '='

- returns 61 for '='
- Verify: returns 61 for '='
   - Expected: char_code("=") equals `61`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 61 for '='")
step("Verify: returns 61 for '='")
expect(char_code("=")).to_equal(61)
```

</details>

#### returns 62 for '>'

- returns 62 for '>'
- Verify: returns 62 for '>'
   - Expected: char_code(">") equals `62`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 62 for '>'")
step("Verify: returns 62 for '>'")
expect(char_code(">")).to_equal(62)
```

</details>

#### returns 63 for '?'

- returns 63 for '?'
- Verify: returns 63 for '?'
   - Expected: char_code("?") equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 63 for '?'")
step("Verify: returns 63 for '?'")
expect(char_code("?")).to_equal(63)
```

</details>

#### returns 35 for '#'

- returns 35 for '#'
- Verify: returns 35 for '#'
   - Expected: char_code("#") equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 35 for '#'")
step("Verify: returns 35 for '#'")
expect(char_code("#")).to_equal(35)
```

</details>

#### returns 37 for '%'

- returns 37 for '%'
- Verify: returns 37 for '%'
   - Expected: char_code("%") equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 37 for '%'")
step("Verify: returns 37 for '%'")
expect(char_code("%")).to_equal(37)
```

</details>

#### returns 38 for '&'

- returns 38 for '&'
- Verify: returns 38 for '&'
   - Expected: char_code("&") equals `38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 38 for '&'")
step("Verify: returns 38 for '&'")
expect(char_code("&")).to_equal(38)
```

</details>

#### returns 96 for backtick

- returns 96 for backtick
- Verify: returns 96 for backtick
   - Expected: char_code("`") equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 96 for backtick")
step("Verify: returns 96 for backtick")
expect(char_code("`")).to_equal(96)
```

</details>

#### whitespace characters

#### returns 10 for newline

- returns 10 for newline
- Verify: returns 10 for newline
   - Expected: char_code("\n") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 10 for newline")
step("Verify: returns 10 for newline")
expect(char_code("\n")).to_equal(10)
```

</details>

#### returns 9 for tab

- returns 9 for tab
- Verify: returns 9 for tab
   - Expected: char_code("\t") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 9 for tab")
step("Verify: returns 9 for tab")
expect(char_code("\t")).to_equal(9)
```

</details>

#### returns 13 for carriage return

- returns 13 for carriage return
- Verify: returns 13 for carriage return
   - Expected: char_code("\r") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 13 for carriage return")
step("Verify: returns 13 for carriage return")
expect(char_code("\r")).to_equal(13)
```

</details>

#### edge cases

#### returns 0 for empty string

- returns 0 for empty string
- Verify: returns 0 for empty string
   - Expected: char_code("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 0 for empty string")
step("Verify: returns 0 for empty string")
expect(char_code("")).to_equal(0)
```

</details>

### string_from_code

#### digits

#### returns '0' for 48

- returns '0' for 48
- Verify: returns '0' for 48
   - Expected: string_from_code(48) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '0' for 48")
step("Verify: returns '0' for 48")
expect(string_from_code(48)).to_equal("0")
```

</details>

#### returns '9' for 57

- returns '9' for 57
- Verify: returns '9' for 57
   - Expected: string_from_code(57) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '9' for 57")
step("Verify: returns '9' for 57")
expect(string_from_code(57)).to_equal("9")
```

</details>

#### returns '5' for 53

- returns '5' for 53
- Verify: returns '5' for 53
   - Expected: string_from_code(53) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '5' for 53")
step("Verify: returns '5' for 53")
expect(string_from_code(53)).to_equal("5")
```

</details>

#### uppercase letters

#### returns 'A' for 65

- returns 'A' for 65
- Verify: returns 'A' for 65
   - Expected: string_from_code(65) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'A' for 65")
step("Verify: returns 'A' for 65")
expect(string_from_code(65)).to_equal("A")
```

</details>

#### returns 'Z' for 90

- returns 'Z' for 90
- Verify: returns 'Z' for 90
   - Expected: string_from_code(90) equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'Z' for 90")
step("Verify: returns 'Z' for 90")
expect(string_from_code(90)).to_equal("Z")
```

</details>

#### returns 'M' for 77

- returns 'M' for 77
- Verify: returns 'M' for 77
   - Expected: string_from_code(77) equals `M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'M' for 77")
step("Verify: returns 'M' for 77")
expect(string_from_code(77)).to_equal("M")
```

</details>

#### lowercase letters

#### returns 'a' for 97

- returns 'a' for 97
- Verify: returns 'a' for 97
   - Expected: string_from_code(97) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'a' for 97")
step("Verify: returns 'a' for 97")
expect(string_from_code(97)).to_equal("a")
```

</details>

#### returns 'z' for 122

- returns 'z' for 122
- Verify: returns 'z' for 122
   - Expected: string_from_code(122) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'z' for 122")
step("Verify: returns 'z' for 122")
expect(string_from_code(122)).to_equal("z")
```

</details>

#### returns 'm' for 109

- returns 'm' for 109
- Verify: returns 'm' for 109
   - Expected: string_from_code(109) equals `m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'm' for 109")
step("Verify: returns 'm' for 109")
expect(string_from_code(109)).to_equal("m")
```

</details>

#### special characters

#### returns space for 32

- returns space for 32
- Verify: returns space for 32
   - Expected: string_from_code(32) equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns space for 32")
step("Verify: returns space for 32")
expect(string_from_code(32)).to_equal(" ")
```

</details>

#### returns '_' for 95

- returns '_' for 95
- Verify: returns '_' for 95
   - Expected: string_from_code(95) equals `_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '_' for 95")
step("Verify: returns '_' for 95")
expect(string_from_code(95)).to_equal("_")
```

</details>

#### returns backslash for 92

- returns backslash for 92
- Verify: returns backslash for 92
   - Expected: string_from_code(92) equals `\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns backslash for 92")
step("Verify: returns backslash for 92")
expect(string_from_code(92)).to_equal("\\")
```

</details>

#### returns '.' for 46

- returns '.' for 46
- Verify: returns '.' for 46
   - Expected: string_from_code(46) equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '.' for 46")
step("Verify: returns '.' for 46")
expect(string_from_code(46)).to_equal(".")
```

</details>

#### returns '|' for 124

- returns '|' for 124
- Verify: returns '|' for 124
   - Expected: string_from_code(124) equals `|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '|' for 124")
step("Verify: returns '|' for 124")
expect(string_from_code(124)).to_equal("|")
```

</details>

#### returns '~' for 126

- returns '~' for 126
- Verify: returns '~' for 126
   - Expected: string_from_code(126) equals `~`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '~' for 126")
step("Verify: returns '~' for 126")
expect(string_from_code(126)).to_equal("~")
```

</details>

#### returns '!' for 33

- returns '!' for 33
- Verify: returns '!' for 33
   - Expected: string_from_code(33) equals `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '!' for 33")
step("Verify: returns '!' for 33")
expect(string_from_code(33)).to_equal("!")
```

</details>

#### whitespace

#### returns newline for 10

- returns newline for 10
- Verify: returns newline for 10
   - Expected: string_from_code(10) equals `\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns newline for 10")
step("Verify: returns newline for 10")
expect(string_from_code(10)).to_equal("\n")
```

</details>

#### returns tab for 9

- returns tab for 9
- Verify: returns tab for 9
   - Expected: string_from_code(9) equals `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns tab for 9")
step("Verify: returns tab for 9")
expect(string_from_code(9)).to_equal("\t")
```

</details>

#### returns carriage return for 13

- returns carriage return for 13
- Verify: returns carriage return for 13
   - Expected: string_from_code(13) equals `\r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns carriage return for 13")
step("Verify: returns carriage return for 13")
expect(string_from_code(13)).to_equal("\r")
```

</details>

#### edge cases - fallback

#### returns empty string for 0

- returns empty string for 0
- Verify: returns empty string for 0
   - Expected: string_from_code(0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty string for 0")
step("Verify: returns empty string for 0")
expect(string_from_code(0)).to_equal("")
```

</details>

#### returns empty string for 255

- returns empty string for 255
- Verify: returns empty string for 255
   - Expected: string_from_code(255) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty string for 255")
step("Verify: returns empty string for 255")
expect(string_from_code(255)).to_equal("")
```

</details>

#### returns empty string for negative code

- returns empty string for negative code
- Verify: returns empty string for negative code
   - Expected: string_from_code(-1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty string for negative code")
step("Verify: returns empty string for negative code")
expect(string_from_code(-1)).to_equal("")
```

</details>

### char_code and string_from_code roundtrip

#### roundtrips digits

- roundtrips digits
- Verify: roundtrips digits
   - Expected: string_from_code(char_code("0")) equals `0`
   - Expected: string_from_code(char_code("9")) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips digits")
step("Verify: roundtrips digits")
expect(string_from_code(char_code("0"))).to_equal("0")
expect(string_from_code(char_code("9"))).to_equal("9")
```

</details>

#### roundtrips uppercase

- roundtrips uppercase
- Verify: roundtrips uppercase
   - Expected: string_from_code(char_code("A")) equals `A`
   - Expected: string_from_code(char_code("Z")) equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips uppercase")
step("Verify: roundtrips uppercase")
expect(string_from_code(char_code("A"))).to_equal("A")
expect(string_from_code(char_code("Z"))).to_equal("Z")
```

</details>

#### roundtrips lowercase

- roundtrips lowercase
- Verify: roundtrips lowercase
   - Expected: string_from_code(char_code("a")) equals `a`
   - Expected: string_from_code(char_code("z")) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips lowercase")
step("Verify: roundtrips lowercase")
expect(string_from_code(char_code("a"))).to_equal("a")
expect(string_from_code(char_code("z"))).to_equal("z")
```

</details>

#### roundtrips special chars

- roundtrips special chars
- Verify: roundtrips special chars
   - Expected: string_from_code(char_code(".")) equals `.`
   - Expected: string_from_code(char_code("_")) equals `_`
   - Expected: string_from_code(char_code("@")) equals `@`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips special chars")
step("Verify: roundtrips special chars")
expect(string_from_code(char_code("."))).to_equal(".")
expect(string_from_code(char_code("_"))).to_equal("_")
expect(string_from_code(char_code("@"))).to_equal("@")
```

</details>

#### roundtrips whitespace

- roundtrips whitespace
- Verify: roundtrips whitespace
   - Expected: string_from_code(char_code("\n")) equals `\n`
   - Expected: string_from_code(char_code("\t")) equals `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips whitespace")
step("Verify: roundtrips whitespace")
expect(string_from_code(char_code("\n"))).to_equal("\n")
expect(string_from_code(char_code("\t"))).to_equal("\t")
```

</details>

### is_digit_char

#### true branch - digit characters

#### returns true for '0'

- returns true for '0'
- Verify: returns true for '0'
   - Expected: is_digit_char("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '0'")
step("Verify: returns true for '0'")
expect(is_digit_char("0")).to_equal(true)
```

</details>

#### returns true for '9'

- returns true for '9'
- Verify: returns true for '9'
   - Expected: is_digit_char("9") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '9'")
step("Verify: returns true for '9'")
expect(is_digit_char("9")).to_equal(true)
```

</details>

#### returns true for '5'

- returns true for '5'
- Verify: returns true for '5'
   - Expected: is_digit_char("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '5'")
step("Verify: returns true for '5'")
expect(is_digit_char("5")).to_equal(true)
```

</details>

#### returns true for '1'

- returns true for '1'
- Verify: returns true for '1'
   - Expected: is_digit_char("1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '1'")
step("Verify: returns true for '1'")
expect(is_digit_char("1")).to_equal(true)
```

</details>

#### false branch - non-digit characters

#### returns false for 'a'

- returns false for 'a'
- Verify: returns false for 'a'
   - Expected: is_digit_char("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'a'")
step("Verify: returns false for 'a'")
expect(is_digit_char("a")).to_equal(false)
```

</details>

#### returns false for 'Z'

- returns false for 'Z'
- Verify: returns false for 'Z'
   - Expected: is_digit_char("Z") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'Z'")
step("Verify: returns false for 'Z'")
expect(is_digit_char("Z")).to_equal(false)
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
# @req REQ-SSPEC-LIB
step("returns false for space")
step("Verify: returns false for space")
expect(is_digit_char(" ")).to_equal(false)
```

</details>

#### returns false for '.'

- returns false for '.'
- Verify: returns false for '.'
   - Expected: is_digit_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '.'")
step("Verify: returns false for '.'")
expect(is_digit_char(".")).to_equal(false)
```

</details>

#### returns false for '_'

- returns false for '_'
- Verify: returns false for '_'
   - Expected: is_digit_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '_'")
step("Verify: returns false for '_'")
expect(is_digit_char("_")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_digit_char("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_digit_char("")).to_equal(false)
```

</details>

#### boundary values

#### returns false for '/' (code 47, just below 0)

- returns false for '/' (code 47, just below 0)
- Verify: returns false for '/' (code 47, just below 0)
   - Expected: is_digit_char("/") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '/' (code 47, just below 0)")
step("Verify: returns false for '/' (code 47, just below 0)")
expect(is_digit_char("/")).to_equal(false)
```

</details>

#### returns false for ':' (code 58, just above 9)

- returns false for ':' (code 58, just above 9)
- Verify: returns false for ':' (code 58, just above 9)
   - Expected: is_digit_char(":") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for ':' (code 58, just above 9)")
step("Verify: returns false for ':' (code 58, just above 9)")
expect(is_digit_char(":")).to_equal(false)
```

</details>

### is_alpha_char

#### true branch - uppercase letters

#### returns true for 'A'

- returns true for 'A'
- Verify: returns true for 'A'
   - Expected: is_alpha_char("A") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'A'")
step("Verify: returns true for 'A'")
expect(is_alpha_char("A")).to_equal(true)
```

</details>

#### returns true for 'Z'

- returns true for 'Z'
- Verify: returns true for 'Z'
   - Expected: is_alpha_char("Z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'Z'")
step("Verify: returns true for 'Z'")
expect(is_alpha_char("Z")).to_equal(true)
```

</details>

#### returns true for 'M'

- returns true for 'M'
- Verify: returns true for 'M'
   - Expected: is_alpha_char("M") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'M'")
step("Verify: returns true for 'M'")
expect(is_alpha_char("M")).to_equal(true)
```

</details>

#### true branch - lowercase letters

#### returns true for 'a'

- returns true for 'a'
- Verify: returns true for 'a'
   - Expected: is_alpha_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'a'")
step("Verify: returns true for 'a'")
expect(is_alpha_char("a")).to_equal(true)
```

</details>

#### returns true for 'z'

- returns true for 'z'
- Verify: returns true for 'z'
   - Expected: is_alpha_char("z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'z'")
step("Verify: returns true for 'z'")
expect(is_alpha_char("z")).to_equal(true)
```

</details>

#### returns true for 'm'

- returns true for 'm'
- Verify: returns true for 'm'
   - Expected: is_alpha_char("m") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'm'")
step("Verify: returns true for 'm'")
expect(is_alpha_char("m")).to_equal(true)
```

</details>

#### false branch - non-alphabetic characters

#### returns false for '0'

- returns false for '0'
- Verify: returns false for '0'
   - Expected: is_alpha_char("0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '0'")
step("Verify: returns false for '0'")
expect(is_alpha_char("0")).to_equal(false)
```

</details>

#### returns false for '9'

- returns false for '9'
- Verify: returns false for '9'
   - Expected: is_alpha_char("9") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '9'")
step("Verify: returns false for '9'")
expect(is_alpha_char("9")).to_equal(false)
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
# @req REQ-SSPEC-LIB
step("returns false for space")
step("Verify: returns false for space")
expect(is_alpha_char(" ")).to_equal(false)
```

</details>

#### returns false for '_'

- returns false for '_'
- Verify: returns false for '_'
   - Expected: is_alpha_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '_'")
step("Verify: returns false for '_'")
expect(is_alpha_char("_")).to_equal(false)
```

</details>

#### returns false for '.'

- returns false for '.'
- Verify: returns false for '.'
   - Expected: is_alpha_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '.'")
step("Verify: returns false for '.'")
expect(is_alpha_char(".")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_alpha_char("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_alpha_char("")).to_equal(false)
```

</details>

#### boundary values

#### returns false for '@' (code 64, just below A)

- returns false for '@' (code 64, just below A)
- Verify: returns false for '@' (code 64, just below A)
   - Expected: is_alpha_char("@") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '@' (code 64, just below A)")
step("Verify: returns false for '@' (code 64, just below A)")
expect(is_alpha_char("@")).to_equal(false)
```

</details>

#### returns false for '[' (code 91, just above Z)

- returns false for '[' (code 91, just above Z)
- Verify: returns false for '[' (code 91, just above Z)
   - Expected: is_alpha_char("[") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '[' (code 91, just above Z)")
step("Verify: returns false for '[' (code 91, just above Z)")
expect(is_alpha_char("[")).to_equal(false)
```

</details>

#### returns false for '`' (code 96, just below a)

- returns false for '`' (code 96, just below a)
- Verify: returns false for '`' (code 96, just below a)
   - Expected: is_alpha_char("`") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '`' (code 96, just below a)")
step("Verify: returns false for '`' (code 96, just below a)")
expect(is_alpha_char("`")).to_equal(false)
```

</details>

#### returns false for '{' (code 123, just above z)

- returns false for '{' (code 123, just above z)
- Verify: returns false for '(' (code 123, just above z)
   - Expected: is_alpha_char("{") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '{' (code 123, just above z)")
step("Verify: returns false for '(' (code 123, just above z)")
expect(is_alpha_char("{")).to_equal(false)
```

</details>

### is_alnum_char

#### true via alpha branch

#### returns true for 'a'

- returns true for 'a'
- Verify: returns true for 'a'
   - Expected: is_alnum_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'a'")
step("Verify: returns true for 'a'")
expect(is_alnum_char("a")).to_equal(true)
```

</details>

#### returns true for 'Z'

- returns true for 'Z'
- Verify: returns true for 'Z'
   - Expected: is_alnum_char("Z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'Z'")
step("Verify: returns true for 'Z'")
expect(is_alnum_char("Z")).to_equal(true)
```

</details>

#### true via digit branch

#### returns true for '0'

- returns true for '0'
- Verify: returns true for '0'
   - Expected: is_alnum_char("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '0'")
step("Verify: returns true for '0'")
expect(is_alnum_char("0")).to_equal(true)
```

</details>

#### returns true for '9'

- returns true for '9'
- Verify: returns true for '9'
   - Expected: is_alnum_char("9") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '9'")
step("Verify: returns true for '9'")
expect(is_alnum_char("9")).to_equal(true)
```

</details>

#### false branch

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_alnum_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for space")
step("Verify: returns false for space")
expect(is_alnum_char(" ")).to_equal(false)
```

</details>

#### returns false for '_'

- returns false for '_'
- Verify: returns false for '_'
   - Expected: is_alnum_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '_'")
step("Verify: returns false for '_'")
expect(is_alnum_char("_")).to_equal(false)
```

</details>

#### returns false for '.'

- returns false for '.'
- Verify: returns false for '.'
   - Expected: is_alnum_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '.'")
step("Verify: returns false for '.'")
expect(is_alnum_char(".")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_alnum_char("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_alnum_char("")).to_equal(false)
```

</details>

### is_word_char

#### true via alnum branch

#### returns true for 'a'

- returns true for 'a'
- Verify: returns true for 'a'
   - Expected: is_word_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'a'")
step("Verify: returns true for 'a'")
expect(is_word_char("a")).to_equal(true)
```

</details>

#### returns true for 'Z'

- returns true for 'Z'
- Verify: returns true for 'Z'
   - Expected: is_word_char("Z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'Z'")
step("Verify: returns true for 'Z'")
expect(is_word_char("Z")).to_equal(true)
```

</details>

#### returns true for '5'

- returns true for '5'
- Verify: returns true for '5'
   - Expected: is_word_char("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '5'")
step("Verify: returns true for '5'")
expect(is_word_char("5")).to_equal(true)
```

</details>

#### true via underscore branch

#### returns true for '_'

- returns true for '_'
- Verify: returns true for '_'
   - Expected: is_word_char("_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '_'")
step("Verify: returns true for '_'")
expect(is_word_char("_")).to_equal(true)
```

</details>

#### false branch

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_word_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for space")
step("Verify: returns false for space")
expect(is_word_char(" ")).to_equal(false)
```

</details>

#### returns false for '.'

- returns false for '.'
- Verify: returns false for '.'
   - Expected: is_word_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '.'")
step("Verify: returns false for '.'")
expect(is_word_char(".")).to_equal(false)
```

</details>

#### returns false for '-'

- returns false for '-'
- Verify: returns false for '-'
   - Expected: is_word_char("-") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '-'")
step("Verify: returns false for '-'")
expect(is_word_char("-")).to_equal(false)
```

</details>

#### returns false for '@'

- returns false for '@'
- Verify: returns false for '@'
   - Expected: is_word_char("@") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '@'")
step("Verify: returns false for '@'")
expect(is_word_char("@")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_word_char("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_word_char("")).to_equal(false)
```

</details>

### is_whitespace_char

#### true branch - each whitespace type

#### returns true for space

- returns true for space
- Verify: returns true for space
   - Expected: is_whitespace_char(" ") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for space")
step("Verify: returns true for space")
expect(is_whitespace_char(" ")).to_equal(true)
```

</details>

#### returns true for tab

- returns true for tab
- Verify: returns true for tab
   - Expected: is_whitespace_char("\t") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for tab")
step("Verify: returns true for tab")
expect(is_whitespace_char("\t")).to_equal(true)
```

</details>

#### returns true for newline

- returns true for newline
- Verify: returns true for newline
   - Expected: is_whitespace_char("\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for newline")
step("Verify: returns true for newline")
expect(is_whitespace_char("\n")).to_equal(true)
```

</details>

#### returns true for carriage return

- returns true for carriage return
- Verify: returns true for carriage return
   - Expected: is_whitespace_char("\r") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for carriage return")
step("Verify: returns true for carriage return")
expect(is_whitespace_char("\r")).to_equal(true)
```

</details>

#### false branch

#### returns false for 'a'

- returns false for 'a'
- Verify: returns false for 'a'
   - Expected: is_whitespace_char("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'a'")
step("Verify: returns false for 'a'")
expect(is_whitespace_char("a")).to_equal(false)
```

</details>

#### returns false for '0'

- returns false for '0'
- Verify: returns false for '0'
   - Expected: is_whitespace_char("0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '0'")
step("Verify: returns false for '0'")
expect(is_whitespace_char("0")).to_equal(false)
```

</details>

#### returns false for '_'

- returns false for '_'
- Verify: returns false for '_'
   - Expected: is_whitespace_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '_'")
step("Verify: returns false for '_'")
expect(is_whitespace_char("_")).to_equal(false)
```

</details>

#### returns false for '.'

- returns false for '.'
- Verify: returns false for '.'
   - Expected: is_whitespace_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '.'")
step("Verify: returns false for '.'")
expect(is_whitespace_char(".")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_whitespace_char("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_whitespace_char("")).to_equal(false)
```

</details>

### is_hex_char

#### true via numeric branch (0-9)

#### returns true for '0'

- returns true for '0'
- Verify: returns true for '0'
   - Expected: is_hex_char("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '0'")
step("Verify: returns true for '0'")
expect(is_hex_char("0")).to_equal(true)
```

</details>

#### returns true for '9'

- returns true for '9'
- Verify: returns true for '9'
   - Expected: is_hex_char("9") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '9'")
step("Verify: returns true for '9'")
expect(is_hex_char("9")).to_equal(true)
```

</details>

#### returns true for '5'

- returns true for '5'
- Verify: returns true for '5'
   - Expected: is_hex_char("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '5'")
step("Verify: returns true for '5'")
expect(is_hex_char("5")).to_equal(true)
```

</details>

#### true via uppercase branch (A-F)

#### returns true for 'A'

- returns true for 'A'
- Verify: returns true for 'A'
   - Expected: is_hex_char("A") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'A'")
step("Verify: returns true for 'A'")
expect(is_hex_char("A")).to_equal(true)
```

</details>

#### returns true for 'F'

- returns true for 'F'
- Verify: returns true for 'F'
   - Expected: is_hex_char("F") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'F'")
step("Verify: returns true for 'F'")
expect(is_hex_char("F")).to_equal(true)
```

</details>

#### returns true for 'C'

- returns true for 'C'
- Verify: returns true for 'C'
   - Expected: is_hex_char("C") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'C'")
step("Verify: returns true for 'C'")
expect(is_hex_char("C")).to_equal(true)
```

</details>

#### true via lowercase branch (a-f)

#### returns true for 'a'

- returns true for 'a'
- Verify: returns true for 'a'
   - Expected: is_hex_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'a'")
step("Verify: returns true for 'a'")
expect(is_hex_char("a")).to_equal(true)
```

</details>

#### returns true for 'f'

- returns true for 'f'
- Verify: returns true for 'f'
   - Expected: is_hex_char("f") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'f'")
step("Verify: returns true for 'f'")
expect(is_hex_char("f")).to_equal(true)
```

</details>

#### returns true for 'c'

- returns true for 'c'
- Verify: returns true for 'c'
   - Expected: is_hex_char("c") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'c'")
step("Verify: returns true for 'c'")
expect(is_hex_char("c")).to_equal(true)
```

</details>

#### false branch - non-hex characters

#### returns false for 'g'

- returns false for 'g'
- Verify: returns false for 'g'
   - Expected: is_hex_char("g") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'g'")
step("Verify: returns false for 'g'")
expect(is_hex_char("g")).to_equal(false)
```

</details>

#### returns false for 'G'

- returns false for 'G'
- Verify: returns false for 'G'
   - Expected: is_hex_char("G") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'G'")
step("Verify: returns false for 'G'")
expect(is_hex_char("G")).to_equal(false)
```

</details>

#### returns false for 'z'

- returns false for 'z'
- Verify: returns false for 'z'
   - Expected: is_hex_char("z") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'z'")
step("Verify: returns false for 'z'")
expect(is_hex_char("z")).to_equal(false)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_hex_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for space")
step("Verify: returns false for space")
expect(is_hex_char(" ")).to_equal(false)
```

</details>

#### returns false for '_'

- returns false for '_'
- Verify: returns false for '_'
   - Expected: is_hex_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '_'")
step("Verify: returns false for '_'")
expect(is_hex_char("_")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_hex_char("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_hex_char("")).to_equal(false)
```

</details>

#### boundary values

#### returns false for '/' (code 47, just below 0)

- returns false for '/' (code 47, just below 0)
- Verify: returns false for '/' (code 47, just below 0)
   - Expected: is_hex_char("/") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '/' (code 47, just below 0)")
step("Verify: returns false for '/' (code 47, just below 0)")
expect(is_hex_char("/")).to_equal(false)
```

</details>

#### returns false for ':' (code 58, just above 9)

- returns false for ':' (code 58, just above 9)
- Verify: returns false for ':' (code 58, just above 9)
   - Expected: is_hex_char(":") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for ':' (code 58, just above 9)")
step("Verify: returns false for ':' (code 58, just above 9)")
expect(is_hex_char(":")).to_equal(false)
```

</details>

#### returns false for '@' (code 64, just below A)

- returns false for '@' (code 64, just below A)
- Verify: returns false for '@' (code 64, just below A)
   - Expected: is_hex_char("@") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '@' (code 64, just below A)")
step("Verify: returns false for '@' (code 64, just below A)")
expect(is_hex_char("@")).to_equal(false)
```

</details>

#### returns false for 'G' (code 71, just above F)

- returns false for 'G' (code 71, just above F)
- Verify: returns false for 'G' (code 71, just above F)
   - Expected: is_hex_char("G") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'G' (code 71, just above F)")
step("Verify: returns false for 'G' (code 71, just above F)")
expect(is_hex_char("G")).to_equal(false)
```

</details>

#### returns false for '`' (code 96, just below a)

- returns false for '`' (code 96, just below a)
- Verify: returns false for '`' (code 96, just below a)
   - Expected: is_hex_char("`") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '`' (code 96, just below a)")
step("Verify: returns false for '`' (code 96, just below a)")
expect(is_hex_char("`")).to_equal(false)
```

</details>

#### returns false for 'g' (code 103, just above f)

- returns false for 'g' (code 103, just above f)
- Verify: returns false for 'g' (code 103, just above f)
   - Expected: is_hex_char("g") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'g' (code 103, just above f)")
step("Verify: returns false for 'g' (code 103, just above f)")
expect(is_hex_char("g")).to_equal(false)
```

</details>

### is_special_regex_char

#### true branch - all regex metacharacters

#### returns true for '.'

- returns true for '.'
- Verify: returns true for '.'
   - Expected: is_special_regex_char(".") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '.'")
step("Verify: returns true for '.'")
expect(is_special_regex_char(".")).to_equal(true)
```

</details>

#### returns true for '*'

- returns true for '*'
- Verify: returns true for '*'
   - Expected: is_special_regex_char("*") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '*'")
step("Verify: returns true for '*'")
expect(is_special_regex_char("*")).to_equal(true)
```

</details>

#### returns true for '+'

- returns true for '+'
- Verify: returns true for '+'
   - Expected: is_special_regex_char("+") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '+'")
step("Verify: returns true for '+'")
expect(is_special_regex_char("+")).to_equal(true)
```

</details>

#### returns true for '?'

- returns true for '?'
- Verify: returns true for '?'
   - Expected: is_special_regex_char("?") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '?'")
step("Verify: returns true for '?'")
expect(is_special_regex_char("?")).to_equal(true)
```

</details>

#### returns true for '|'

- returns true for '|'
- Verify: returns true for '|'
   - Expected: is_special_regex_char("|") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '|'")
step("Verify: returns true for '|'")
expect(is_special_regex_char("|")).to_equal(true)
```

</details>

#### returns true for '('

- returns true for '('
- Verify: returns true for '('
   - Expected: is_special_regex_char("(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '('")
step("Verify: returns true for '('")
expect(is_special_regex_char("(")).to_equal(true)
```

</details>

#### returns true for ')'

- returns true for ')'
- Verify: returns true for ')'
   - Expected: is_special_regex_char(")") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for ')'")
step("Verify: returns true for ')'")
expect(is_special_regex_char(")")).to_equal(true)
```

</details>

#### returns true for '['

- returns true for '['
- Verify: returns true for '['
   - Expected: is_special_regex_char("[") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '['")
step("Verify: returns true for '['")
expect(is_special_regex_char("[")).to_equal(true)
```

</details>

#### returns true for ']'

- returns true for ']'
- Verify: returns true for ']'
   - Expected: is_special_regex_char("]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for ']'")
step("Verify: returns true for ']'")
expect(is_special_regex_char("]")).to_equal(true)
```

</details>

#### returns true for '{'

- returns true for '{'
- Verify: returns true for '('
   - Expected: is_special_regex_char("{") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '{'")
step("Verify: returns true for '('")
expect(is_special_regex_char("{")).to_equal(true)
```

</details>

#### returns true for '}'

- returns true for '}'
- Verify: returns true for ')'
   - Expected: is_special_regex_char("}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '}'")
step("Verify: returns true for ')'")
expect(is_special_regex_char("}")).to_equal(true)
```

</details>

#### returns true for '^'

- returns true for '^'
- Verify: returns true for '^'
   - Expected: is_special_regex_char("^") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '^'")
step("Verify: returns true for '^'")
expect(is_special_regex_char("^")).to_equal(true)
```

</details>

#### returns true for '$'

- returns true for '$'
- Verify: returns true for '$'
   - Expected: is_special_regex_char("$") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for '$'")
step("Verify: returns true for '$'")
expect(is_special_regex_char("$")).to_equal(true)
```

</details>

#### returns true for backslash

- returns true for backslash
- Verify: returns true for backslash
   - Expected: is_special_regex_char("\\") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for backslash")
step("Verify: returns true for backslash")
expect(is_special_regex_char("\\")).to_equal(true)
```

</details>

#### false branch - non-metacharacters

#### returns false for 'a'

- returns false for 'a'
- Verify: returns false for 'a'
   - Expected: is_special_regex_char("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'a'")
step("Verify: returns false for 'a'")
expect(is_special_regex_char("a")).to_equal(false)
```

</details>

#### returns false for '0'

- returns false for '0'
- Verify: returns false for '0'
   - Expected: is_special_regex_char("0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '0'")
step("Verify: returns false for '0'")
expect(is_special_regex_char("0")).to_equal(false)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_special_regex_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for space")
step("Verify: returns false for space")
expect(is_special_regex_char(" ")).to_equal(false)
```

</details>

#### returns false for '_'

- returns false for '_'
- Verify: returns false for '_'
   - Expected: is_special_regex_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '_'")
step("Verify: returns false for '_'")
expect(is_special_regex_char("_")).to_equal(false)
```

</details>

#### returns false for '-'

- returns false for '-'
- Verify: returns false for '-'
   - Expected: is_special_regex_char("-") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '-'")
step("Verify: returns false for '-'")
expect(is_special_regex_char("-")).to_equal(false)
```

</details>

#### returns false for '@'

- returns false for '@'
- Verify: returns false for '@'
   - Expected: is_special_regex_char("@") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '@'")
step("Verify: returns false for '@'")
expect(is_special_regex_char("@")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_special_regex_char("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_special_regex_char("")).to_equal(false)
```

</details>

### escape_regex

#### strings with special characters

#### escapes a dot

- escapes a dot
- Verify: escapes a dot
   - Expected: escape_regex(".") equals `\\.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes a dot")
step("Verify: escapes a dot")
expect(escape_regex(".")).to_equal("\\.")
```

</details>

#### escapes a star

- escapes a star
- Verify: escapes a star
   - Expected: escape_regex("*") equals `\\*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes a star")
step("Verify: escapes a star")
expect(escape_regex("*")).to_equal("\\*")
```

</details>

#### escapes parentheses

- escapes parentheses
- Verify: escapes parentheses
   - Expected: escape_regex("()") equals `\\(\\)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes parentheses")
step("Verify: escapes parentheses")
expect(escape_regex("()")).to_equal("\\(\\)")
```

</details>

#### escapes brackets

- escapes brackets
- Verify: escapes brackets
   - Expected: escape_regex("[]") equals `\\[\\]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes brackets")
step("Verify: escapes brackets")
expect(escape_regex("[]")).to_equal("\\[\\]")
```

</details>

#### escapes braces

- escapes braces
- Verify: escapes braces
   - Expected: escape_regex("{}") equals `\\{\\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes braces")
step("Verify: escapes braces")
expect(escape_regex("{}")).to_equal("\\{\\}")
```

</details>

#### escapes caret and dollar

- escapes caret and dollar
- Verify: escapes caret and dollar
   - Expected: escape_regex("^$") equals `\\^\\$`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes caret and dollar")
step("Verify: escapes caret and dollar")
expect(escape_regex("^$")).to_equal("\\^\\$")
```

</details>

#### escapes pipe

- escapes pipe
- Verify: escapes pipe
   - Expected: escape_regex("|") equals `\\|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes pipe")
step("Verify: escapes pipe")
expect(escape_regex("|")).to_equal("\\|")
```

</details>

#### escapes plus and question mark

- escapes plus and question mark
- Verify: escapes plus and question mark
   - Expected: escape_regex("+?") equals `\\+\\?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes plus and question mark")
step("Verify: escapes plus and question mark")
expect(escape_regex("+?")).to_equal("\\+\\?")
```

</details>

#### escapes backslash

- escapes backslash
- Verify: escapes backslash
   - Expected: escape_regex("\\") equals `\\\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes backslash")
step("Verify: escapes backslash")
expect(escape_regex("\\")).to_equal("\\\\")
```

</details>

#### strings without special characters

#### returns plain text unchanged

- returns plain text unchanged
- Verify: returns plain text unchanged
   - Expected: escape_regex("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns plain text unchanged")
step("Verify: returns plain text unchanged")
expect(escape_regex("hello")).to_equal("hello")
```

</details>

#### returns digits unchanged

- returns digits unchanged
- Verify: returns digits unchanged
   - Expected: escape_regex("12345") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns digits unchanged")
step("Verify: returns digits unchanged")
expect(escape_regex("12345")).to_equal("12345")
```

</details>

#### mixed content

#### escapes only special chars in mixed string

- escapes only special chars in mixed string
- Verify: escapes only special chars in mixed string
   - Expected: escape_regex("a.b") equals `a\\.b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes only special chars in mixed string")
step("Verify: escapes only special chars in mixed string")
expect(escape_regex("a.b")).to_equal("a\\.b")
```

</details>

#### escapes multiple special chars among normal text

- escapes multiple special chars among normal text
- Verify: escapes multiple special chars among normal text
   - Expected: escape_regex("a+b*c") equals `a\\+b\\*c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes multiple special chars among normal text")
step("Verify: escapes multiple special chars among normal text")
expect(escape_regex("a+b*c")).to_equal("a\\+b\\*c")
```

</details>

#### edge cases

#### returns empty string for empty input

- returns empty string for empty input
- Verify: returns empty string for empty input
   - Expected: escape_regex("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty string for empty input")
step("Verify: returns empty string for empty input")
expect(escape_regex("")).to_equal("")
```

</details>

#### handles single normal character

- handles single normal character
- Verify: handles single normal character
   - Expected: escape_regex("x") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles single normal character")
step("Verify: handles single normal character")
expect(escape_regex("x")).to_equal("x")
```

</details>

### unescape_regex

#### escaped special characters

#### unescapes a dot

- unescapes a dot
- Verify: unescapes a dot
   - Expected: unescape_regex("\\.") equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes a dot")
step("Verify: unescapes a dot")
expect(unescape_regex("\\.")).to_equal(".")
```

</details>

#### unescapes a star

- unescapes a star
- Verify: unescapes a star
   - Expected: unescape_regex("\\*") equals `*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes a star")
step("Verify: unescapes a star")
expect(unescape_regex("\\*")).to_equal("*")
```

</details>

#### unescapes parentheses

- unescapes parentheses
- Verify: unescapes parentheses
   - Expected: unescape_regex("\\(\\)") equals `()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes parentheses")
step("Verify: unescapes parentheses")
expect(unescape_regex("\\(\\)")).to_equal("()")
```

</details>

#### unescapes brackets

- unescapes brackets
- Verify: unescapes brackets
   - Expected: unescape_regex("\\[\\]") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes brackets")
step("Verify: unescapes brackets")
expect(unescape_regex("\\[\\]")).to_equal("[]")
```

</details>

#### normal characters pass through

#### returns plain text unchanged

- returns plain text unchanged
- Verify: returns plain text unchanged
   - Expected: unescape_regex("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns plain text unchanged")
step("Verify: returns plain text unchanged")
expect(unescape_regex("hello")).to_equal("hello")
```

</details>

#### returns digits unchanged

- returns digits unchanged
- Verify: returns digits unchanged
   - Expected: unescape_regex("12345") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns digits unchanged")
step("Verify: returns digits unchanged")
expect(unescape_regex("12345")).to_equal("12345")
```

</details>

#### mixed content

#### unescapes only escaped chars in mixed string

- unescapes only escaped chars in mixed string
- Verify: unescapes only escaped chars in mixed string
   - Expected: unescape_regex("a\\.b") equals `a.b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes only escaped chars in mixed string")
step("Verify: unescapes only escaped chars in mixed string")
expect(unescape_regex("a\\.b")).to_equal("a.b")
```

</details>

#### handles multiple escaped chars

- handles multiple escaped chars
- Verify: handles multiple escaped chars
   - Expected: unescape_regex("a\\+b\\*c") equals `a+b*c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multiple escaped chars")
step("Verify: handles multiple escaped chars")
expect(unescape_regex("a\\+b\\*c")).to_equal("a+b*c")
```

</details>

#### trailing backslash

#### preserves trailing backslash when no char follows

- preserves trailing backslash when no char follows
- Verify: preserves trailing backslash when no char follows
   - Expected: unescape_regex("abc\\") equals `abc\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves trailing backslash when no char follows")
step("Verify: preserves trailing backslash when no char follows")
expect(unescape_regex("abc\\")).to_equal("abc\\")
```

</details>

#### handles lone backslash

- handles lone backslash
- Verify: handles lone backslash
   - Expected: unescape_regex("\\") equals `\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles lone backslash")
step("Verify: handles lone backslash")
expect(unescape_regex("\\")).to_equal("\\")
```

</details>

#### edge cases

#### returns empty string for empty input

- returns empty string for empty input
- Verify: returns empty string for empty input
   - Expected: unescape_regex("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty string for empty input")
step("Verify: returns empty string for empty input")
expect(unescape_regex("")).to_equal("")
```

</details>

#### unescapes escaped backslash

- unescapes escaped backslash
- Verify: unescapes escaped backslash
   - Expected: unescape_regex("\\\\") equals `\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unescapes escaped backslash")
step("Verify: unescapes escaped backslash")
expect(unescape_regex("\\\\")).to_equal("\\")
```

</details>

### expand_escape

#### literal escapes

#### expands 'n' to newline

- expands 'n' to newline
- Verify: expands 'n' to newline
   - Expected: expand_escape("n") equals `\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'n' to newline")
step("Verify: expands 'n' to newline")
expect(expand_escape("n")).to_equal("\n")
```

</details>

#### expands 't' to tab

- expands 't' to tab
- Verify: expands 't' to tab
   - Expected: expand_escape("t") equals `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 't' to tab")
step("Verify: expands 't' to tab")
expect(expand_escape("t")).to_equal("\t")
```

</details>

#### expands 'r' to carriage return

- expands 'r' to carriage return
- Verify: expands 'r' to carriage return
   - Expected: expand_escape("r") equals `\r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'r' to carriage return")
step("Verify: expands 'r' to carriage return")
expect(expand_escape("r")).to_equal("\r")
```

</details>

#### character class escapes

#### expands 'd' to digit class

- expands 'd' to digit class
- Verify: expands 'd' to digit class
   - Expected: expand_escape("d") equals `[0-9]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'd' to digit class")
step("Verify: expands 'd' to digit class")
expect(expand_escape("d")).to_equal("[0-9]")
```

</details>

#### expands 'D' to non-digit class

- expands 'D' to non-digit class
- Verify: expands 'D' to non-digit class
   - Expected: expand_escape("D") equals `[^0-9]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'D' to non-digit class")
step("Verify: expands 'D' to non-digit class")
expect(expand_escape("D")).to_equal("[^0-9]")
```

</details>

#### expands 'w' to word class

- expands 'w' to word class
- Verify: expands 'w' to word class
   - Expected: expand_escape("w") equals `[a-zA-Z0-9_]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'w' to word class")
step("Verify: expands 'w' to word class")
expect(expand_escape("w")).to_equal("[a-zA-Z0-9_]")
```

</details>

#### expands 'W' to non-word class

- expands 'W' to non-word class
- Verify: expands 'W' to non-word class
   - Expected: expand_escape("W") equals `[^a-zA-Z0-9_]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'W' to non-word class")
step("Verify: expands 'W' to non-word class")
expect(expand_escape("W")).to_equal("[^a-zA-Z0-9_]")
```

</details>

#### expands 's' to whitespace class

- expands 's' to whitespace class
- Verify: expands 's' to whitespace class
   - Expected: expand_escape("s") equals `[ \t\n\r]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 's' to whitespace class")
step("Verify: expands 's' to whitespace class")
expect(expand_escape("s")).to_equal("[ \t\n\r]")
```

</details>

#### expands 'S' to non-whitespace class

- expands 'S' to non-whitespace class
- Verify: expands 'S' to non-whitespace class
   - Expected: expand_escape("S") equals `[^ \t\n\r]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'S' to non-whitespace class")
step("Verify: expands 'S' to non-whitespace class")
expect(expand_escape("S")).to_equal("[^ \t\n\r]")
```

</details>

#### boundary escapes

#### expands 'b' to word boundary

- expands 'b' to word boundary
- Verify: expands 'b' to word boundary
   - Expected: expand_escape("b") equals `\\b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'b' to word boundary")
step("Verify: expands 'b' to word boundary")
expect(expand_escape("b")).to_equal("\\b")
```

</details>

#### expands 'B' to non-word boundary

- expands 'B' to non-word boundary
- Verify: expands 'B' to non-word boundary
   - Expected: expand_escape("B") equals `\\B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands 'B' to non-word boundary")
step("Verify: expands 'B' to non-word boundary")
expect(expand_escape("B")).to_equal("\\B")
```

</details>

#### fallback - unrecognized escapes

#### returns 'x' unchanged

- returns 'x' unchanged
- Verify: returns 'x' unchanged
   - Expected: expand_escape("x") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'x' unchanged")
step("Verify: returns 'x' unchanged")
expect(expand_escape("x")).to_equal("x")
```

</details>

#### returns 'a' unchanged

- returns 'a' unchanged
- Verify: returns 'a' unchanged
   - Expected: expand_escape("a") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'a' unchanged")
step("Verify: returns 'a' unchanged")
expect(expand_escape("a")).to_equal("a")
```

</details>

#### returns '.' unchanged

- returns '.' unchanged
- Verify: returns '.' unchanged
   - Expected: expand_escape(".") equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '.' unchanged")
step("Verify: returns '.' unchanged")
expect(expand_escape(".")).to_equal(".")
```

</details>

#### returns empty string unchanged

- returns empty string unchanged
- Verify: returns empty string unchanged
   - Expected: expand_escape("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty string unchanged")
step("Verify: returns empty string unchanged")
expect(expand_escape("")).to_equal("")
```

</details>

#### returns '1' unchanged

- returns '1' unchanged
- Verify: returns '1' unchanged
   - Expected: expand_escape("1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '1' unchanged")
step("Verify: returns '1' unchanged")
expect(expand_escape("1")).to_equal("1")
```

</details>

### is_escape_char

#### true branch - all recognized escape characters

#### returns true for 'n'

- returns true for 'n'
- Verify: returns true for 'n'
   - Expected: is_escape_char("n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'n'")
step("Verify: returns true for 'n'")
expect(is_escape_char("n")).to_equal(true)
```

</details>

#### returns true for 't'

- returns true for 't'
- Verify: returns true for 't'
   - Expected: is_escape_char("t") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 't'")
step("Verify: returns true for 't'")
expect(is_escape_char("t")).to_equal(true)
```

</details>

#### returns true for 'r'

- returns true for 'r'
- Verify: returns true for 'r'
   - Expected: is_escape_char("r") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'r'")
step("Verify: returns true for 'r'")
expect(is_escape_char("r")).to_equal(true)
```

</details>

#### returns true for 'd'

- returns true for 'd'
- Verify: returns true for 'd'
   - Expected: is_escape_char("d") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'd'")
step("Verify: returns true for 'd'")
expect(is_escape_char("d")).to_equal(true)
```

</details>

#### returns true for 'D'

- returns true for 'D'
- Verify: returns true for 'D'
   - Expected: is_escape_char("D") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'D'")
step("Verify: returns true for 'D'")
expect(is_escape_char("D")).to_equal(true)
```

</details>

#### returns true for 'w'

- returns true for 'w'
- Verify: returns true for 'w'
   - Expected: is_escape_char("w") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'w'")
step("Verify: returns true for 'w'")
expect(is_escape_char("w")).to_equal(true)
```

</details>

#### returns true for 'W'

- returns true for 'W'
- Verify: returns true for 'W'
   - Expected: is_escape_char("W") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'W'")
step("Verify: returns true for 'W'")
expect(is_escape_char("W")).to_equal(true)
```

</details>

#### returns true for 's'

- returns true for 's'
- Verify: returns true for 's'
   - Expected: is_escape_char("s") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 's'")
step("Verify: returns true for 's'")
expect(is_escape_char("s")).to_equal(true)
```

</details>

#### returns true for 'S'

- returns true for 'S'
- Verify: returns true for 'S'
   - Expected: is_escape_char("S") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'S'")
step("Verify: returns true for 'S'")
expect(is_escape_char("S")).to_equal(true)
```

</details>

#### returns true for 'b'

- returns true for 'b'
- Verify: returns true for 'b'
   - Expected: is_escape_char("b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'b'")
step("Verify: returns true for 'b'")
expect(is_escape_char("b")).to_equal(true)
```

</details>

#### returns true for 'B'

- returns true for 'B'
- Verify: returns true for 'B'
   - Expected: is_escape_char("B") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for 'B'")
step("Verify: returns true for 'B'")
expect(is_escape_char("B")).to_equal(true)
```

</details>

#### false branch - non-escape characters

#### returns false for 'a'

- returns false for 'a'
- Verify: returns false for 'a'
   - Expected: is_escape_char("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'a'")
step("Verify: returns false for 'a'")
expect(is_escape_char("a")).to_equal(false)
```

</details>

#### returns false for 'x'

- returns false for 'x'
- Verify: returns false for 'x'
   - Expected: is_escape_char("x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for 'x'")
step("Verify: returns false for 'x'")
expect(is_escape_char("x")).to_equal(false)
```

</details>

#### returns false for '0'

- returns false for '0'
- Verify: returns false for '0'
   - Expected: is_escape_char("0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '0'")
step("Verify: returns false for '0'")
expect(is_escape_char("0")).to_equal(false)
```

</details>

#### returns false for '.'

- returns false for '.'
- Verify: returns false for '.'
   - Expected: is_escape_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for '.'")
step("Verify: returns false for '.'")
expect(is_escape_char(".")).to_equal(false)
```

</details>

#### returns false for empty string

- returns false for empty string
- Verify: returns false for empty string
   - Expected: is_escape_char("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for empty string")
step("Verify: returns false for empty string")
expect(is_escape_char("")).to_equal(false)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_escape_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for space")
step("Verify: returns false for space")
expect(is_escape_char(" ")).to_equal(false)
```

</details>

### escape and unescape roundtrip

#### roundtrips plain text

- roundtrips plain text
- Verify: roundtrips plain text
   - Expected: unescape_regex(escape_regex(original)) equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips plain text")
step("Verify: roundtrips plain text")
val original = "hello world"
expect(unescape_regex(escape_regex(original))).to_equal(original)
```

</details>

#### roundtrips string with dots

- roundtrips string with dots
- Verify: roundtrips string with dots
   - Expected: unescape_regex(escape_regex(original)) equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips string with dots")
step("Verify: roundtrips string with dots")
val original = "a.b.c"
expect(unescape_regex(escape_regex(original))).to_equal(original)
```

</details>

#### roundtrips string with all metacharacters

- roundtrips string with all metacharacters
- Verify: roundtrips string with all metacharacters
   - Expected: unescape_regex(escape_regex(original)) equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips string with all metacharacters")
step("Verify: roundtrips string with all metacharacters")
val original = ".*+?|()[]{}^$"
expect(unescape_regex(escape_regex(original))).to_equal(original)
```

</details>

#### roundtrips empty string

- roundtrips empty string
- Verify: roundtrips empty string
   - Expected: unescape_regex(escape_regex("")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips empty string")
step("Verify: roundtrips empty string")
expect(unescape_regex(escape_regex(""))).to_equal("")
```

</details>

#### roundtrips mixed content

- roundtrips mixed content
- Verify: roundtrips mixed content
   - Expected: unescape_regex(escape_regex(original)) equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("roundtrips mixed content")
step("Verify: roundtrips mixed content")
val original = "foo(bar)+baz*"
expect(unescape_regex(escape_regex(original))).to_equal(original)
```

</details>

### char_code all uppercase letters

#### returns 66 for 'B'

- returns 66 for 'B'
- Verify: returns 66 for 'B'
   - Expected: char_code("B") equals `66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 66 for 'B'")
step("Verify: returns 66 for 'B'")
expect(char_code("B")).to_equal(66)
```

</details>

#### returns 67 for 'C'

- returns 67 for 'C'
- Verify: returns 67 for 'C'
   - Expected: char_code("C") equals `67`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 67 for 'C'")
step("Verify: returns 67 for 'C'")
expect(char_code("C")).to_equal(67)
```

</details>

#### returns 68 for 'D'

- returns 68 for 'D'
- Verify: returns 68 for 'D'
   - Expected: char_code("D") equals `68`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 68 for 'D'")
step("Verify: returns 68 for 'D'")
expect(char_code("D")).to_equal(68)
```

</details>

#### returns 69 for 'E'

- returns 69 for 'E'
- Verify: returns 69 for 'E'
   - Expected: char_code("E") equals `69`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 69 for 'E'")
step("Verify: returns 69 for 'E'")
expect(char_code("E")).to_equal(69)
```

</details>

#### returns 70 for 'F'

- returns 70 for 'F'
- Verify: returns 70 for 'F'
   - Expected: char_code("F") equals `70`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 70 for 'F'")
step("Verify: returns 70 for 'F'")
expect(char_code("F")).to_equal(70)
```

</details>

#### returns 71 for 'G'

- returns 71 for 'G'
- Verify: returns 71 for 'G'
   - Expected: char_code("G") equals `71`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 71 for 'G'")
step("Verify: returns 71 for 'G'")
expect(char_code("G")).to_equal(71)
```

</details>

#### returns 72 for 'H'

- returns 72 for 'H'
- Verify: returns 72 for 'H'
   - Expected: char_code("H") equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 72 for 'H'")
step("Verify: returns 72 for 'H'")
expect(char_code("H")).to_equal(72)
```

</details>

#### returns 73 for 'I'

- returns 73 for 'I'
- Verify: returns 73 for 'I'
   - Expected: char_code("I") equals `73`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 73 for 'I'")
step("Verify: returns 73 for 'I'")
expect(char_code("I")).to_equal(73)
```

</details>

#### returns 74 for 'J'

- returns 74 for 'J'
- Verify: returns 74 for 'J'
   - Expected: char_code("J") equals `74`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 74 for 'J'")
step("Verify: returns 74 for 'J'")
expect(char_code("J")).to_equal(74)
```

</details>

#### returns 75 for 'K'

- returns 75 for 'K'
- Verify: returns 75 for 'K'
   - Expected: char_code("K") equals `75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 75 for 'K'")
step("Verify: returns 75 for 'K'")
expect(char_code("K")).to_equal(75)
```

</details>

#### returns 76 for 'L'

- returns 76 for 'L'
- Verify: returns 76 for 'L'
   - Expected: char_code("L") equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 76 for 'L'")
step("Verify: returns 76 for 'L'")
expect(char_code("L")).to_equal(76)
```

</details>

#### returns 78 for 'N'

- returns 78 for 'N'
- Verify: returns 78 for 'N'
   - Expected: char_code("N") equals `78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 78 for 'N'")
step("Verify: returns 78 for 'N'")
expect(char_code("N")).to_equal(78)
```

</details>

#### returns 79 for 'O'

- returns 79 for 'O'
- Verify: returns 79 for 'O'
   - Expected: char_code("O") equals `79`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 79 for 'O'")
step("Verify: returns 79 for 'O'")
expect(char_code("O")).to_equal(79)
```

</details>

#### returns 80 for 'P'

- returns 80 for 'P'
- Verify: returns 80 for 'P'
   - Expected: char_code("P") equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 80 for 'P'")
step("Verify: returns 80 for 'P'")
expect(char_code("P")).to_equal(80)
```

</details>

#### returns 81 for 'Q'

- returns 81 for 'Q'
- Verify: returns 81 for 'Q'
   - Expected: char_code("Q") equals `81`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 81 for 'Q'")
step("Verify: returns 81 for 'Q'")
expect(char_code("Q")).to_equal(81)
```

</details>

#### returns 82 for 'R'

- returns 82 for 'R'
- Verify: returns 82 for 'R'
   - Expected: char_code("R") equals `82`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 82 for 'R'")
step("Verify: returns 82 for 'R'")
expect(char_code("R")).to_equal(82)
```

</details>

#### returns 83 for 'S'

- returns 83 for 'S'
- Verify: returns 83 for 'S'
   - Expected: char_code("S") equals `83`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 83 for 'S'")
step("Verify: returns 83 for 'S'")
expect(char_code("S")).to_equal(83)
```

</details>

#### returns 84 for 'T'

- returns 84 for 'T'
- Verify: returns 84 for 'T'
   - Expected: char_code("T") equals `84`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 84 for 'T'")
step("Verify: returns 84 for 'T'")
expect(char_code("T")).to_equal(84)
```

</details>

#### returns 85 for 'U'

- returns 85 for 'U'
- Verify: returns 85 for 'U'
   - Expected: char_code("U") equals `85`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 85 for 'U'")
step("Verify: returns 85 for 'U'")
expect(char_code("U")).to_equal(85)
```

</details>

#### returns 86 for 'V'

- returns 86 for 'V'
- Verify: returns 86 for 'V'
   - Expected: char_code("V") equals `86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 86 for 'V'")
step("Verify: returns 86 for 'V'")
expect(char_code("V")).to_equal(86)
```

</details>

#### returns 87 for 'W'

- returns 87 for 'W'
- Verify: returns 87 for 'W'
   - Expected: char_code("W") equals `87`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 87 for 'W'")
step("Verify: returns 87 for 'W'")
expect(char_code("W")).to_equal(87)
```

</details>

#### returns 88 for 'X'

- returns 88 for 'X'
- Verify: returns 88 for 'X'
   - Expected: char_code("X") equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 88 for 'X'")
step("Verify: returns 88 for 'X'")
expect(char_code("X")).to_equal(88)
```

</details>

#### returns 89 for 'Y'

- returns 89 for 'Y'
- Verify: returns 89 for 'Y'
   - Expected: char_code("Y") equals `89`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 89 for 'Y'")
step("Verify: returns 89 for 'Y'")
expect(char_code("Y")).to_equal(89)
```

</details>

### char_code all lowercase letters

#### returns 98 for 'b'

- returns 98 for 'b'
- Verify: returns 98 for 'b'
   - Expected: char_code("b") equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 98 for 'b'")
step("Verify: returns 98 for 'b'")
expect(char_code("b")).to_equal(98)
```

</details>

#### returns 99 for 'c'

- returns 99 for 'c'
- Verify: returns 99 for 'c'
   - Expected: char_code("c") equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 99 for 'c'")
step("Verify: returns 99 for 'c'")
expect(char_code("c")).to_equal(99)
```

</details>

#### returns 100 for 'd'

- returns 100 for 'd'
- Verify: returns 100 for 'd'
   - Expected: char_code("d") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 100 for 'd'")
step("Verify: returns 100 for 'd'")
expect(char_code("d")).to_equal(100)
```

</details>

#### returns 101 for 'e'

- returns 101 for 'e'
- Verify: returns 101 for 'e'
   - Expected: char_code("e") equals `101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 101 for 'e'")
step("Verify: returns 101 for 'e'")
expect(char_code("e")).to_equal(101)
```

</details>

#### returns 102 for 'f'

- returns 102 for 'f'
- Verify: returns 102 for 'f'
   - Expected: char_code("f") equals `102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 102 for 'f'")
step("Verify: returns 102 for 'f'")
expect(char_code("f")).to_equal(102)
```

</details>

#### returns 103 for 'g'

- returns 103 for 'g'
- Verify: returns 103 for 'g'
   - Expected: char_code("g") equals `103`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 103 for 'g'")
step("Verify: returns 103 for 'g'")
expect(char_code("g")).to_equal(103)
```

</details>

#### returns 104 for 'h'

- returns 104 for 'h'
- Verify: returns 104 for 'h'
   - Expected: char_code("h") equals `104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 104 for 'h'")
step("Verify: returns 104 for 'h'")
expect(char_code("h")).to_equal(104)
```

</details>

#### returns 105 for 'i'

- returns 105 for 'i'
- Verify: returns 105 for 'i'
   - Expected: char_code("i") equals `105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 105 for 'i'")
step("Verify: returns 105 for 'i'")
expect(char_code("i")).to_equal(105)
```

</details>

#### returns 106 for 'j'

- returns 106 for 'j'
- Verify: returns 106 for 'j'
   - Expected: char_code("j") equals `106`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 106 for 'j'")
step("Verify: returns 106 for 'j'")
expect(char_code("j")).to_equal(106)
```

</details>

#### returns 107 for 'k'

- returns 107 for 'k'
- Verify: returns 107 for 'k'
   - Expected: char_code("k") equals `107`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 107 for 'k'")
step("Verify: returns 107 for 'k'")
expect(char_code("k")).to_equal(107)
```

</details>

#### returns 108 for 'l'

- returns 108 for 'l'
- Verify: returns 108 for 'l'
   - Expected: char_code("l") equals `108`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 108 for 'l'")
step("Verify: returns 108 for 'l'")
expect(char_code("l")).to_equal(108)
```

</details>

#### returns 110 for 'n'

- returns 110 for 'n'
- Verify: returns 110 for 'n'
   - Expected: char_code("n") equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 110 for 'n'")
step("Verify: returns 110 for 'n'")
expect(char_code("n")).to_equal(110)
```

</details>

#### returns 111 for 'o'

- returns 111 for 'o'
- Verify: returns 111 for 'o'
   - Expected: char_code("o") equals `111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 111 for 'o'")
step("Verify: returns 111 for 'o'")
expect(char_code("o")).to_equal(111)
```

</details>

#### returns 112 for 'p'

- returns 112 for 'p'
- Verify: returns 112 for 'p'
   - Expected: char_code("p") equals `112`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 112 for 'p'")
step("Verify: returns 112 for 'p'")
expect(char_code("p")).to_equal(112)
```

</details>

#### returns 113 for 'q'

- returns 113 for 'q'
- Verify: returns 113 for 'q'
   - Expected: char_code("q") equals `113`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 113 for 'q'")
step("Verify: returns 113 for 'q'")
expect(char_code("q")).to_equal(113)
```

</details>

#### returns 114 for 'r'

- returns 114 for 'r'
- Verify: returns 114 for 'r'
   - Expected: char_code("r") equals `114`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 114 for 'r'")
step("Verify: returns 114 for 'r'")
expect(char_code("r")).to_equal(114)
```

</details>

#### returns 115 for 's'

- returns 115 for 's'
- Verify: returns 115 for 's'
   - Expected: char_code("s") equals `115`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 115 for 's'")
step("Verify: returns 115 for 's'")
expect(char_code("s")).to_equal(115)
```

</details>

#### returns 116 for 't'

- returns 116 for 't'
- Verify: returns 116 for 't'
   - Expected: char_code("t") equals `116`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 116 for 't'")
step("Verify: returns 116 for 't'")
expect(char_code("t")).to_equal(116)
```

</details>

#### returns 117 for 'u'

- returns 117 for 'u'
- Verify: returns 117 for 'u'
   - Expected: char_code("u") equals `117`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 117 for 'u'")
step("Verify: returns 117 for 'u'")
expect(char_code("u")).to_equal(117)
```

</details>

#### returns 118 for 'v'

- returns 118 for 'v'
- Verify: returns 118 for 'v'
   - Expected: char_code("v") equals `118`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 118 for 'v'")
step("Verify: returns 118 for 'v'")
expect(char_code("v")).to_equal(118)
```

</details>

#### returns 119 for 'w'

- returns 119 for 'w'
- Verify: returns 119 for 'w'
   - Expected: char_code("w") equals `119`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 119 for 'w'")
step("Verify: returns 119 for 'w'")
expect(char_code("w")).to_equal(119)
```

</details>

#### returns 120 for 'x'

- returns 120 for 'x'
- Verify: returns 120 for 'x'
   - Expected: char_code("x") equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 120 for 'x'")
step("Verify: returns 120 for 'x'")
expect(char_code("x")).to_equal(120)
```

</details>

#### returns 121 for 'y'

- returns 121 for 'y'
- Verify: returns 121 for 'y'
   - Expected: char_code("y") equals `121`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 121 for 'y'")
step("Verify: returns 121 for 'y'")
expect(char_code("y")).to_equal(121)
```

</details>

### char_code all digits

#### returns 49 for '1'

- returns 49 for '1'
- Verify: returns 49 for '1'
   - Expected: char_code("1") equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 49 for '1'")
step("Verify: returns 49 for '1'")
expect(char_code("1")).to_equal(49)
```

</details>

#### returns 50 for '2'

- returns 50 for '2'
- Verify: returns 50 for '2'
   - Expected: char_code("2") equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 50 for '2'")
step("Verify: returns 50 for '2'")
expect(char_code("2")).to_equal(50)
```

</details>

#### returns 51 for '3'

- returns 51 for '3'
- Verify: returns 51 for '3'
   - Expected: char_code("3") equals `51`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 51 for '3'")
step("Verify: returns 51 for '3'")
expect(char_code("3")).to_equal(51)
```

</details>

#### returns 52 for '4'

- returns 52 for '4'
- Verify: returns 52 for '4'
   - Expected: char_code("4") equals `52`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 52 for '4'")
step("Verify: returns 52 for '4'")
expect(char_code("4")).to_equal(52)
```

</details>

#### returns 54 for '6'

- returns 54 for '6'
- Verify: returns 54 for '6'
   - Expected: char_code("6") equals `54`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 54 for '6'")
step("Verify: returns 54 for '6'")
expect(char_code("6")).to_equal(54)
```

</details>

#### returns 55 for '7'

- returns 55 for '7'
- Verify: returns 55 for '7'
   - Expected: char_code("7") equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 55 for '7'")
step("Verify: returns 55 for '7'")
expect(char_code("7")).to_equal(55)
```

</details>

#### returns 56 for '8'

- returns 56 for '8'
- Verify: returns 56 for '8'
   - Expected: char_code("8") equals `56`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 56 for '8'")
step("Verify: returns 56 for '8'")
expect(char_code("8")).to_equal(56)
```

</details>

### string_from_code all uppercase letters

#### returns 'B' for 66

- returns 'B' for 66
- Verify: returns 'B' for 66
   - Expected: string_from_code(66) equals `B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'B' for 66")
step("Verify: returns 'B' for 66")
expect(string_from_code(66)).to_equal("B")
```

</details>

#### returns 'C' for 67

- returns 'C' for 67
- Verify: returns 'C' for 67
   - Expected: string_from_code(67) equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'C' for 67")
step("Verify: returns 'C' for 67")
expect(string_from_code(67)).to_equal("C")
```

</details>

#### returns 'D' for 68

- returns 'D' for 68
- Verify: returns 'D' for 68
   - Expected: string_from_code(68) equals `D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'D' for 68")
step("Verify: returns 'D' for 68")
expect(string_from_code(68)).to_equal("D")
```

</details>

#### returns 'E' for 69

- returns 'E' for 69
- Verify: returns 'E' for 69
   - Expected: string_from_code(69) equals `E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'E' for 69")
step("Verify: returns 'E' for 69")
expect(string_from_code(69)).to_equal("E")
```

</details>

#### returns 'F' for 70

- returns 'F' for 70
- Verify: returns 'F' for 70
   - Expected: string_from_code(70) equals `F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'F' for 70")
step("Verify: returns 'F' for 70")
expect(string_from_code(70)).to_equal("F")
```

</details>

#### returns 'G' for 71

- returns 'G' for 71
- Verify: returns 'G' for 71
   - Expected: string_from_code(71) equals `G`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'G' for 71")
step("Verify: returns 'G' for 71")
expect(string_from_code(71)).to_equal("G")
```

</details>

#### returns 'H' for 72

- returns 'H' for 72
- Verify: returns 'H' for 72
   - Expected: string_from_code(72) equals `H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'H' for 72")
step("Verify: returns 'H' for 72")
expect(string_from_code(72)).to_equal("H")
```

</details>

#### returns 'I' for 73

- returns 'I' for 73
- Verify: returns 'I' for 73
   - Expected: string_from_code(73) equals `I`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'I' for 73")
step("Verify: returns 'I' for 73")
expect(string_from_code(73)).to_equal("I")
```

</details>

#### returns 'J' for 74

- returns 'J' for 74
- Verify: returns 'J' for 74
   - Expected: string_from_code(74) equals `J`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'J' for 74")
step("Verify: returns 'J' for 74")
expect(string_from_code(74)).to_equal("J")
```

</details>

#### returns 'K' for 75

- returns 'K' for 75
- Verify: returns 'K' for 75
   - Expected: string_from_code(75) equals `K`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'K' for 75")
step("Verify: returns 'K' for 75")
expect(string_from_code(75)).to_equal("K")
```

</details>

#### returns 'L' for 76

- returns 'L' for 76
- Verify: returns 'L' for 76
   - Expected: string_from_code(76) equals `L`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'L' for 76")
step("Verify: returns 'L' for 76")
expect(string_from_code(76)).to_equal("L")
```

</details>

#### returns 'N' for 78

- returns 'N' for 78
- Verify: returns 'N' for 78
   - Expected: string_from_code(78) equals `N`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'N' for 78")
step("Verify: returns 'N' for 78")
expect(string_from_code(78)).to_equal("N")
```

</details>

#### returns 'O' for 79

- returns 'O' for 79
- Verify: returns 'O' for 79
   - Expected: string_from_code(79) equals `O`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'O' for 79")
step("Verify: returns 'O' for 79")
expect(string_from_code(79)).to_equal("O")
```

</details>

#### returns 'P' for 80

- returns 'P' for 80
- Verify: returns 'P' for 80
   - Expected: string_from_code(80) equals `P`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'P' for 80")
step("Verify: returns 'P' for 80")
expect(string_from_code(80)).to_equal("P")
```

</details>

#### returns 'Q' for 81

- returns 'Q' for 81
- Verify: returns 'Q' for 81
   - Expected: string_from_code(81) equals `Q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'Q' for 81")
step("Verify: returns 'Q' for 81")
expect(string_from_code(81)).to_equal("Q")
```

</details>

#### returns 'R' for 82

- returns 'R' for 82
- Verify: returns 'R' for 82
   - Expected: string_from_code(82) equals `R`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'R' for 82")
step("Verify: returns 'R' for 82")
expect(string_from_code(82)).to_equal("R")
```

</details>

#### returns 'S' for 83

- returns 'S' for 83
- Verify: returns 'S' for 83
   - Expected: string_from_code(83) equals `S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'S' for 83")
step("Verify: returns 'S' for 83")
expect(string_from_code(83)).to_equal("S")
```

</details>

#### returns 'T' for 84

- returns 'T' for 84
- Verify: returns 'T' for 84
   - Expected: string_from_code(84) equals `T`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'T' for 84")
step("Verify: returns 'T' for 84")
expect(string_from_code(84)).to_equal("T")
```

</details>

#### returns 'U' for 85

- returns 'U' for 85
- Verify: returns 'U' for 85
   - Expected: string_from_code(85) equals `U`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'U' for 85")
step("Verify: returns 'U' for 85")
expect(string_from_code(85)).to_equal("U")
```

</details>

#### returns 'V' for 86

- returns 'V' for 86
- Verify: returns 'V' for 86
   - Expected: string_from_code(86) equals `V`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'V' for 86")
step("Verify: returns 'V' for 86")
expect(string_from_code(86)).to_equal("V")
```

</details>

#### returns 'W' for 87

- returns 'W' for 87
- Verify: returns 'W' for 87
   - Expected: string_from_code(87) equals `W`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'W' for 87")
step("Verify: returns 'W' for 87")
expect(string_from_code(87)).to_equal("W")
```

</details>

#### returns 'X' for 88

- returns 'X' for 88
- Verify: returns 'X' for 88
   - Expected: string_from_code(88) equals `X`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'X' for 88")
step("Verify: returns 'X' for 88")
expect(string_from_code(88)).to_equal("X")
```

</details>

#### returns 'Y' for 89

- returns 'Y' for 89
- Verify: returns 'Y' for 89
   - Expected: string_from_code(89) equals `Y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'Y' for 89")
step("Verify: returns 'Y' for 89")
expect(string_from_code(89)).to_equal("Y")
```

</details>

### string_from_code all lowercase letters

#### returns 'b' for 98

- returns 'b' for 98
- Verify: returns 'b' for 98
   - Expected: string_from_code(98) equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'b' for 98")
step("Verify: returns 'b' for 98")
expect(string_from_code(98)).to_equal("b")
```

</details>

#### returns 'c' for 99

- returns 'c' for 99
- Verify: returns 'c' for 99
   - Expected: string_from_code(99) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'c' for 99")
step("Verify: returns 'c' for 99")
expect(string_from_code(99)).to_equal("c")
```

</details>

#### returns 'd' for 100

- returns 'd' for 100
- Verify: returns 'd' for 100
   - Expected: string_from_code(100) equals `d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'd' for 100")
step("Verify: returns 'd' for 100")
expect(string_from_code(100)).to_equal("d")
```

</details>

#### returns 'e' for 101

- returns 'e' for 101
- Verify: returns 'e' for 101
   - Expected: string_from_code(101) equals `e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'e' for 101")
step("Verify: returns 'e' for 101")
expect(string_from_code(101)).to_equal("e")
```

</details>

#### returns 'f' for 102

- returns 'f' for 102
- Verify: returns 'f' for 102
   - Expected: string_from_code(102) equals `f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'f' for 102")
step("Verify: returns 'f' for 102")
expect(string_from_code(102)).to_equal("f")
```

</details>

#### returns 'g' for 103

- returns 'g' for 103
- Verify: returns 'g' for 103
   - Expected: string_from_code(103) equals `g`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'g' for 103")
step("Verify: returns 'g' for 103")
expect(string_from_code(103)).to_equal("g")
```

</details>

#### returns 'h' for 104

- returns 'h' for 104
- Verify: returns 'h' for 104
   - Expected: string_from_code(104) equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'h' for 104")
step("Verify: returns 'h' for 104")
expect(string_from_code(104)).to_equal("h")
```

</details>

#### returns 'i' for 105

- returns 'i' for 105
- Verify: returns 'i' for 105
   - Expected: string_from_code(105) equals `i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'i' for 105")
step("Verify: returns 'i' for 105")
expect(string_from_code(105)).to_equal("i")
```

</details>

#### returns 'j' for 106

- returns 'j' for 106
- Verify: returns 'j' for 106
   - Expected: string_from_code(106) equals `j`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'j' for 106")
step("Verify: returns 'j' for 106")
expect(string_from_code(106)).to_equal("j")
```

</details>

#### returns 'k' for 107

- returns 'k' for 107
- Verify: returns 'k' for 107
   - Expected: string_from_code(107) equals `k`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'k' for 107")
step("Verify: returns 'k' for 107")
expect(string_from_code(107)).to_equal("k")
```

</details>

#### returns 'l' for 108

- returns 'l' for 108
- Verify: returns 'l' for 108
   - Expected: string_from_code(108) equals `l`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'l' for 108")
step("Verify: returns 'l' for 108")
expect(string_from_code(108)).to_equal("l")
```

</details>

#### returns 'n' for 110

- returns 'n' for 110
- Verify: returns 'n' for 110
   - Expected: string_from_code(110) equals `n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'n' for 110")
step("Verify: returns 'n' for 110")
expect(string_from_code(110)).to_equal("n")
```

</details>

#### returns 'o' for 111

- returns 'o' for 111
- Verify: returns 'o' for 111
   - Expected: string_from_code(111) equals `o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'o' for 111")
step("Verify: returns 'o' for 111")
expect(string_from_code(111)).to_equal("o")
```

</details>

#### returns 'p' for 112

- returns 'p' for 112
- Verify: returns 'p' for 112
   - Expected: string_from_code(112) equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'p' for 112")
step("Verify: returns 'p' for 112")
expect(string_from_code(112)).to_equal("p")
```

</details>

#### returns 'q' for 113

- returns 'q' for 113
- Verify: returns 'q' for 113
   - Expected: string_from_code(113) equals `q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'q' for 113")
step("Verify: returns 'q' for 113")
expect(string_from_code(113)).to_equal("q")
```

</details>

#### returns 'r' for 114

- returns 'r' for 114
- Verify: returns 'r' for 114
   - Expected: string_from_code(114) equals `r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'r' for 114")
step("Verify: returns 'r' for 114")
expect(string_from_code(114)).to_equal("r")
```

</details>

#### returns 's' for 115

- returns 's' for 115
- Verify: returns 's' for 115
   - Expected: string_from_code(115) equals `s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 's' for 115")
step("Verify: returns 's' for 115")
expect(string_from_code(115)).to_equal("s")
```

</details>

#### returns 't' for 116

- returns 't' for 116
- Verify: returns 't' for 116
   - Expected: string_from_code(116) equals `t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 't' for 116")
step("Verify: returns 't' for 116")
expect(string_from_code(116)).to_equal("t")
```

</details>

#### returns 'u' for 117

- returns 'u' for 117
- Verify: returns 'u' for 117
   - Expected: string_from_code(117) equals `u`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'u' for 117")
step("Verify: returns 'u' for 117")
expect(string_from_code(117)).to_equal("u")
```

</details>

#### returns 'v' for 118

- returns 'v' for 118
- Verify: returns 'v' for 118
   - Expected: string_from_code(118) equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'v' for 118")
step("Verify: returns 'v' for 118")
expect(string_from_code(118)).to_equal("v")
```

</details>

#### returns 'w' for 119

- returns 'w' for 119
- Verify: returns 'w' for 119
   - Expected: string_from_code(119) equals `w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'w' for 119")
step("Verify: returns 'w' for 119")
expect(string_from_code(119)).to_equal("w")
```

</details>

#### returns 'x' for 120

- returns 'x' for 120
- Verify: returns 'x' for 120
   - Expected: string_from_code(120) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'x' for 120")
step("Verify: returns 'x' for 120")
expect(string_from_code(120)).to_equal("x")
```

</details>

#### returns 'y' for 121

- returns 'y' for 121
- Verify: returns 'y' for 121
   - Expected: string_from_code(121) equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns 'y' for 121")
step("Verify: returns 'y' for 121")
expect(string_from_code(121)).to_equal("y")
```

</details>

### string_from_code all digits

#### returns '1' for 49

- returns '1' for 49
- Verify: returns '1' for 49
   - Expected: string_from_code(49) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '1' for 49")
step("Verify: returns '1' for 49")
expect(string_from_code(49)).to_equal("1")
```

</details>

#### returns '2' for 50

- returns '2' for 50
- Verify: returns '2' for 50
   - Expected: string_from_code(50) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '2' for 50")
step("Verify: returns '2' for 50")
expect(string_from_code(50)).to_equal("2")
```

</details>

#### returns '3' for 51

- returns '3' for 51
- Verify: returns '3' for 51
   - Expected: string_from_code(51) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '3' for 51")
step("Verify: returns '3' for 51")
expect(string_from_code(51)).to_equal("3")
```

</details>

#### returns '4' for 52

- returns '4' for 52
- Verify: returns '4' for 52
   - Expected: string_from_code(52) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '4' for 52")
step("Verify: returns '4' for 52")
expect(string_from_code(52)).to_equal("4")
```

</details>

#### returns '6' for 54

- returns '6' for 54
- Verify: returns '6' for 54
   - Expected: string_from_code(54) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '6' for 54")
step("Verify: returns '6' for 54")
expect(string_from_code(54)).to_equal("6")
```

</details>

#### returns '7' for 55

- returns '7' for 55
- Verify: returns '7' for 55
   - Expected: string_from_code(55) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '7' for 55")
step("Verify: returns '7' for 55")
expect(string_from_code(55)).to_equal("7")
```

</details>

#### returns '8' for 56

- returns '8' for 56
- Verify: returns '8' for 56
   - Expected: string_from_code(56) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '8' for 56")
step("Verify: returns '8' for 56")
expect(string_from_code(56)).to_equal("8")
```

</details>

### string_from_code all special characters

#### returns double-quote for 34

- returns double-quote for 34
- Verify: returns double-quote for 34
   - Expected: string_from_code(34) equals `"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns double-quote for 34")
step("Verify: returns double-quote for 34")
expect(string_from_code(34)).to_equal("\"")
```

</details>

#### returns '#' for 35

- returns '#' for 35
- Verify: returns '#' for 35
   - Expected: string_from_code(35) equals `#`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '#' for 35")
step("Verify: returns '#' for 35")
expect(string_from_code(35)).to_equal("#")
```

</details>

#### returns '$' for 36

- returns '$' for 36
- Verify: returns '$' for 36
   - Expected: string_from_code(36) equals `$`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '$' for 36")
step("Verify: returns '$' for 36")
expect(string_from_code(36)).to_equal("$")
```

</details>

#### returns '%' for 37

- returns '%' for 37
- Verify: returns '%' for 37
   - Expected: string_from_code(37) equals `%`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '%' for 37")
step("Verify: returns '%' for 37")
expect(string_from_code(37)).to_equal("%")
```

</details>

#### returns '&' for 38

- returns '&' for 38
- Verify: returns '&' for 38
   - Expected: string_from_code(38) equals `&`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '&' for 38")
step("Verify: returns '&' for 38")
expect(string_from_code(38)).to_equal("&")
```

</details>

#### returns single-quote for 39

- returns single-quote for 39
- Verify: returns single-quote for 39
   - Expected: string_from_code(39) equals `'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns single-quote for 39")
step("Verify: returns single-quote for 39")
expect(string_from_code(39)).to_equal("'")
```

</details>

#### returns '(' for 40

- returns '(' for 40
- Verify: returns '(' for 40
   - Expected: string_from_code(40) equals `(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '(' for 40")
step("Verify: returns '(' for 40")
expect(string_from_code(40)).to_equal("(")
```

</details>

#### returns ')' for 41

- returns ')' for 41
- Verify: returns ')' for 41
   - Expected: string_from_code(41) equals `)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns ')' for 41")
step("Verify: returns ')' for 41")
expect(string_from_code(41)).to_equal(")")
```

</details>

#### returns '*' for 42

- returns '*' for 42
- Verify: returns '*' for 42
   - Expected: string_from_code(42) equals `*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '*' for 42")
step("Verify: returns '*' for 42")
expect(string_from_code(42)).to_equal("*")
```

</details>

#### returns '+' for 43

- returns '+' for 43
- Verify: returns '+' for 43
   - Expected: string_from_code(43) equals `+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '+' for 43")
step("Verify: returns '+' for 43")
expect(string_from_code(43)).to_equal("+")
```

</details>

#### returns ',' for 44

- returns ',' for 44
- Verify: returns ',' for 44
   - Expected: string_from_code(44) equals `,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns ',' for 44")
step("Verify: returns ',' for 44")
expect(string_from_code(44)).to_equal(",")
```

</details>

#### returns '-' for 45

- returns '-' for 45
- Verify: returns '-' for 45
   - Expected: string_from_code(45) equals `-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '-' for 45")
step("Verify: returns '-' for 45")
expect(string_from_code(45)).to_equal("-")
```

</details>

#### returns '/' for 47

- returns '/' for 47
- Verify: returns '/' for 47
   - Expected: string_from_code(47) equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '/' for 47")
step("Verify: returns '/' for 47")
expect(string_from_code(47)).to_equal("/")
```

</details>

#### returns ':' for 58

- returns ':' for 58
- Verify: returns ':' for 58
   - Expected: string_from_code(58) equals `:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns ':' for 58")
step("Verify: returns ':' for 58")
expect(string_from_code(58)).to_equal(":")
```

</details>

#### returns ';' for 59

- returns ';' for 59
- Verify: returns ';' for 59
   - Expected: string_from_code(59) equals `;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns ';' for 59")
step("Verify: returns ';' for 59")
expect(string_from_code(59)).to_equal(";")
```

</details>

#### returns '<' for 60

- returns '<' for 60
- Verify: returns '<' for 60
   - Expected: string_from_code(60) equals `<`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '<' for 60")
step("Verify: returns '<' for 60")
expect(string_from_code(60)).to_equal("<")
```

</details>

#### returns '=' for 61

- returns '=' for 61
- Verify: returns '=' for 61
   - Expected: string_from_code(61) equals `=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '=' for 61")
step("Verify: returns '=' for 61")
expect(string_from_code(61)).to_equal("=")
```

</details>

#### returns '>' for 62

- returns '>' for 62
- Verify: returns '>' for 62
   - Expected: string_from_code(62) equals `>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '>' for 62")
step("Verify: returns '>' for 62")
expect(string_from_code(62)).to_equal(">")
```

</details>

#### returns '?' for 63

- returns '?' for 63
- Verify: returns '?' for 63
   - Expected: string_from_code(63) equals `?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '?' for 63")
step("Verify: returns '?' for 63")
expect(string_from_code(63)).to_equal("?")
```

</details>

#### returns '@' for 64

- returns '@' for 64
- Verify: returns '@' for 64
   - Expected: string_from_code(64) equals `@`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '@' for 64")
step("Verify: returns '@' for 64")
expect(string_from_code(64)).to_equal("@")
```

</details>

#### returns '[' for 91

- returns '[' for 91
- Verify: returns '[' for 91
   - Expected: string_from_code(91) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '[' for 91")
step("Verify: returns '[' for 91")
expect(string_from_code(91)).to_equal("[")
```

</details>

#### returns ']' for 93

- returns ']' for 93
- Verify: returns ']' for 93
   - Expected: string_from_code(93) equals `]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns ']' for 93")
step("Verify: returns ']' for 93")
expect(string_from_code(93)).to_equal("]")
```

</details>

#### returns '^' for 94

- returns '^' for 94
- Verify: returns '^' for 94
   - Expected: string_from_code(94) equals `^`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '^' for 94")
step("Verify: returns '^' for 94")
expect(string_from_code(94)).to_equal("^")
```

</details>

#### returns backtick for 96

- returns backtick for 96
- Verify: returns backtick for 96
   - Expected: string_from_code(96) equals ```


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns backtick for 96")
step("Verify: returns backtick for 96")
expect(string_from_code(96)).to_equal("`")
```

</details>

#### returns '{' for 123

- returns '{' for 123
- Verify: returns '(' for 123
   - Expected: string_from_code(123) equals `{`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '{' for 123")
step("Verify: returns '(' for 123")
expect(string_from_code(123)).to_equal("{")
```

</details>

#### returns '}' for 125

- returns '}' for 125
- Verify: returns ')' for 125
   - Expected: string_from_code(125) equals `}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns '}' for 125")
step("Verify: returns ')' for 125")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e965ee4e667a39155062eba6af848d344a47f28b5302b14dabbb2dd8d538ed7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e965ee4e667a39155062eba6af848d344a47f28b5302b14dabbb2dd8d538ed7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e965ee4e667a39155062eba6af848d344a47f28b5302b14dabbb2dd8d538ed7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/regex_char_utils_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/regex_char_utils_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/regex_char_utils_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/regex_char_utils_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/regex_char_utils_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 99 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/regex_char_utils_coverage_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 48 for '0'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/regex_char_utils_coverage_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 57 for '9'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/regex_char_utils_coverage_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 53 for '5'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
