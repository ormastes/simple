# CMM Lexer Specification

> Tests for the CMM (PRACTICE Script) lexer. Validates tokenization of all CMM lexical elements: comments, labels, macros, numbers, strings, dot commands, operators, options, file channels, and full lines.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 95 | 95 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CMM Lexer Specification

Tests for the CMM (PRACTICE Script) lexer. Validates tokenization of all CMM lexical elements: comments, labels, macros, numbers, strings, dot commands, operators, options, file channels, and full lines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-LEX |
| Category | Tooling |
| Status | Implemented |
| Source | `test/feature/usage/cmm_lsp/cmm_lexer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the CMM (PRACTICE Script) lexer. Validates tokenization of all
CMM lexical elements: comments, labels, macros, numbers, strings, dot
commands, operators, options, file channels, and full lines.

Interpreter mode: it block bodies don't execute. Tests verify that
all CMM lexer concepts are structurally valid Simple code that loads
without errors.

## Scenarios

### CMM Lexer - Comments

#### lexes semicolon comment

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lexes semicolon comment
- lexes semicolon comment
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes semicolon comment")
step("lexes semicolon comment")
# @req: REQ-FEAT-CMM-LSP-CMM-LEXER-SPEC-001
val tokens = lex_cmm_line("; this is a comment", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes double-slash comment

- lexes double-slash comment
- lexes double-slash comment
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes double-slash comment")
step("lexes double-slash comment")
val tokens = lex_cmm_line("// another comment", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes semicolon comment with no trailing text

- lexes semicolon comment with no trailing text
- lexes semicolon comment with no trailing text
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes semicolon comment with no trailing text")
step("lexes semicolon comment with no trailing text")
val tokens = lex_cmm_line(";", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes double-slash comment with no trailing text

- lexes double-slash comment with no trailing text
- lexes double-slash comment with no trailing text
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes double-slash comment with no trailing text")
step("lexes double-slash comment with no trailing text")
val tokens = lex_cmm_line("//", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes inline comment after whitespace

- lexes inline comment after whitespace
- lexes inline comment after whitespace
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes inline comment after whitespace")
step("lexes inline comment after whitespace")
val tokens = lex_cmm_line("  ; inline comment", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Labels

#### lexes label at column 1

- lexes label at column 1
- lexes label at column 1
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes label at column 1")
step("lexes label at column 1")
val tokens = lex_cmm_line("start:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes label with underscore

- lexes label with underscore
- lexes label with underscore
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes label with underscore")
step("lexes label with underscore")
val tokens = lex_cmm_line("_my_label:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes label with alphanumeric chars

- lexes label with alphanumeric chars
- lexes label with alphanumeric chars
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes label with alphanumeric chars")
step("lexes label with alphanumeric chars")
val tokens = lex_cmm_line("FlashSetup3:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### distinguishes label from device selector

- distinguishes label from device selector
- distinguishes label from device selector
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("distinguishes label from device selector")
step("distinguishes label from device selector")
# B:: is a device selector, not a label
val tokens = lex_cmm_line("B::", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### returns empty for empty line

- returns empty for empty line
- returns empty for empty line
   - Expected: tokens.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns empty for empty line")
step("returns empty for empty line")
val tokens = lex_cmm_line("", 1)
expect(tokens.len()).to_equal(0)
```

</details>

### CMM Lexer - Macro References

#### lexes simple macro ref

- lexes simple macro ref
- lexes simple macro ref
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes simple macro ref")
step("lexes simple macro ref")
val tokens = lex_cmm_line("  &myvar", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes recursive macro ref

- lexes recursive macro ref
- lexes recursive macro ref
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes recursive macro ref")
step("lexes recursive macro ref")
val tokens = lex_cmm_line("  &&myvar", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes bare ampersand as operator when no identifier follows

- lexes bare ampersand as operator when no identifier follows
- lexes bare ampersand as operator when no identifier follows
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes bare ampersand as operator when no identifier follows")
step("lexes bare ampersand as operator when no identifier follows")
# & without an identifier after it is the binary AND operator
val tokens = lex_cmm_line("  &", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes bare double-ampersand as logical AND when no identifier follows

- lexes bare double-ampersand as logical AND when no identifier follows
- lexes bare double-ampersand as logical AND when no identifier follows
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes bare double-ampersand as logical AND when no identifier follows")
step("lexes bare double-ampersand as logical AND when no identifier follows")
# && without an identifier is the logical AND operator
val tokens = lex_cmm_line("  &&", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes macro ref with underscore in name

- lexes macro ref with underscore in name
- lexes macro ref with underscore in name
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes macro ref with underscore in name")
step("lexes macro ref with underscore in name")
val tokens = lex_cmm_line("  &my_var_1", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Hex Numbers

#### lexes hex number with lowercase 0x

- lexes hex number with lowercase 0x
- lexes hex number with lowercase 0x
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes hex number with lowercase 0x")
step("lexes hex number with lowercase 0x")
val tokens = lex_cmm_line("  0x1000", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hex number with uppercase 0X

- lexes hex number with uppercase 0X
- lexes hex number with uppercase 0X
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes hex number with uppercase 0X")
step("lexes hex number with uppercase 0X")
val tokens = lex_cmm_line("  0XABCDEF", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hex mask with dont-care bits

- lexes hex mask with dont-care bits
- lexes hex mask with dont-care bits
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes hex mask with dont-care bits")
step("lexes hex mask with dont-care bits")
# 0xFX has dont-care nibble
val tokens = lex_cmm_line("  0xFX", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hex mask with multiple dont-care bits

- lexes hex mask with multiple dont-care bits
- lexes hex mask with multiple dont-care bits
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes hex mask with multiple dont-care bits")
step("lexes hex mask with multiple dont-care bits")
val tokens = lex_cmm_line("  0xff1cxxxx", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Binary Numbers

#### lexes binary number with 0y prefix

- lexes binary number with 0y prefix
- lexes binary number with 0y prefix
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes binary number with 0y prefix")
step("lexes binary number with 0y prefix")
val tokens = lex_cmm_line("  0y101", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes binary mask with dont-care bits

- lexes binary mask with dont-care bits
- lexes binary mask with dont-care bits
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes binary mask with dont-care bits")
step("lexes binary mask with dont-care bits")
val tokens = lex_cmm_line("  0yX111XXX", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Decimal and Integer Numbers

#### lexes decimal number with trailing dot

- lexes decimal number with trailing dot
- lexes decimal number with trailing dot
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes decimal number with trailing dot")
step("lexes decimal number with trailing dot")
val tokens = lex_cmm_line("  100.", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes plain integer

- lexes plain integer
- lexes plain integer
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes plain integer")
step("lexes plain integer")
val tokens = lex_cmm_line("  1234", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes float number

- lexes float number
- lexes float number
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes float number")
step("lexes float number")
val tokens = lex_cmm_line("  1.3", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes float with exponent

- lexes float with exponent
- lexes float with exponent
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes float with exponent")
step("lexes float with exponent")
val tokens = lex_cmm_line("  1.3e+34", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Time Literals

#### lexes millisecond time literal

- lexes millisecond time literal
- lexes millisecond time literal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes millisecond time literal")
step("lexes millisecond time literal")
val tokens = lex_cmm_line("  10ms", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes microsecond time literal

- lexes microsecond time literal
- lexes microsecond time literal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes microsecond time literal")
step("lexes microsecond time literal")
val tokens = lex_cmm_line("  100us", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes nanosecond time literal

- lexes nanosecond time literal
- lexes nanosecond time literal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes nanosecond time literal")
step("lexes nanosecond time literal")
val tokens = lex_cmm_line("  75ns", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes second time literal

- lexes second time literal
- lexes second time literal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes second time literal")
step("lexes second time literal")
val tokens = lex_cmm_line("  10s", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes float time literal

- lexes float time literal
- lexes float time literal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes float time literal")
step("lexes float time literal")
val tokens = lex_cmm_line("  23.24ms", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Strings

#### lexes simple string

- lexes simple string
- lexes simple string
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes simple string")
step("lexes simple string")
val tokens = lex_cmm_line("  \"hello world\"", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes empty string

- lexes empty string
- lexes empty string
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes empty string")
step("lexes empty string")
val tokens = lex_cmm_line("  \"\"", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes string with escaped double quote

- lexes string with escaped double quote
- lexes string with escaped double quote
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes string with escaped double quote")
step("lexes string with escaped double quote")
# In CMM, "" inside a string is an escaped double-quote
val tokens = lex_cmm_line("  \"abc\"\"def\"", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Char Literals

#### lexes single character literal

- lexes single character literal
- lexes single character literal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes single character literal")
step("lexes single character literal")
val tokens = lex_cmm_line("  'A'", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes lowercase char literal

- lexes lowercase char literal
- lexes lowercase char literal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes lowercase char literal")
step("lexes lowercase char literal")
val tokens = lex_cmm_line("  'z'", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Dot Commands

#### lexes simple dot command

- lexes simple dot command
- lexes simple dot command
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes simple dot command")
step("lexes simple dot command")
val tokens = lex_cmm_line("  Data.dump", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes two-level dot command

- lexes two-level dot command
- lexes two-level dot command
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes two-level dot command")
step("lexes two-level dot command")
val tokens = lex_cmm_line("  SYStem.CPU", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes multi-level dot command

- lexes multi-level dot command
- lexes multi-level dot command
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes multi-level dot command")
step("lexes multi-level dot command")
val tokens = lex_cmm_line("  FLASH.ReProgram.ALL", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes dot command with reset

- lexes dot command with reset
- lexes dot command with reset
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes dot command with reset")
step("lexes dot command with reset")
val tokens = lex_cmm_line("  FLASH.RESet", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Comparison Operators

#### lexes equality operator

- lexes equality operator
- lexes equality operator
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes equality operator")
step("lexes equality operator")
val tokens = lex_cmm_line("  ==", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes not-equal operator

- lexes not-equal operator
- lexes not-equal operator
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes not-equal operator")
step("lexes not-equal operator")
val tokens = lex_cmm_line("  !=", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes less-than-or-equal

- lexes less-than-or-equal
- lexes less-than-or-equal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes less-than-or-equal")
step("lexes less-than-or-equal")
val tokens = lex_cmm_line("  <=", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes greater-than-or-equal

- lexes greater-than-or-equal
- lexes greater-than-or-equal
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes greater-than-or-equal")
step("lexes greater-than-or-equal")
val tokens = lex_cmm_line("  >=", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Range Operators

#### lexes range-to operator

- lexes range-to operator
- lexes range-to operator
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes range-to operator")
step("lexes range-to operator")
val tokens = lex_cmm_line("  --", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes range-offset operator

- lexes range-offset operator
- lexes range-offset operator
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes range-offset operator")
step("lexes range-offset operator")
val tokens = lex_cmm_line("  ++", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes range-dots operator

- lexes range-dots operator
- lexes range-dots operator
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes range-dots operator")
step("lexes range-dots operator")
val tokens = lex_cmm_line("  ..", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Logical Operators

#### lexes logical AND

- lexes logical AND
- lexes logical AND
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes logical AND")
step("lexes logical AND")
val tokens = lex_cmm_line("  &&", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes logical OR

- lexes logical OR
- lexes logical OR
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes logical OR")
step("lexes logical OR")
val tokens = lex_cmm_line("  ||", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes logical XOR

- lexes logical XOR
- lexes logical XOR
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes logical XOR")
step("lexes logical XOR")
val tokens = lex_cmm_line("  ^^", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Shift Operators

#### lexes shift left

- lexes shift left
- lexes shift left
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes shift left")
step("lexes shift left")
val tokens = lex_cmm_line("  <<", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes shift right

- lexes shift right
- lexes shift right
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes shift right")
step("lexes shift right")
val tokens = lex_cmm_line("  >>", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Classic Operators

#### lexes classic AND colon form

- lexes classic AND colon form
- lexes classic AND colon form
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes classic AND colon form")
step("lexes classic AND colon form")
val tokens = lex_cmm_line("  :A:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes classic OR colon form

- lexes classic OR colon form
- lexes classic OR colon form
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes classic OR colon form")
step("lexes classic OR colon form")
val tokens = lex_cmm_line("  :O:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes classic XOR colon form

- lexes classic XOR colon form
- lexes classic XOR colon form
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes classic XOR colon form")
step("lexes classic XOR colon form")
val tokens = lex_cmm_line("  :X:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Single-Char Operators

#### lexes plus

- lexes plus
- lexes plus
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes plus")
step("lexes plus")
val tokens = lex_cmm_line("  +", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes minus

- lexes minus
- lexes minus
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes minus")
step("lexes minus")
val tokens = lex_cmm_line("  -", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes star

- lexes star
- lexes star
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes star")
step("lexes star")
val tokens = lex_cmm_line("  *", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes percent

- lexes percent
- lexes percent
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes percent")
step("lexes percent")
val tokens = lex_cmm_line("  %", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes tilde

- lexes tilde
- lexes tilde
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes tilde")
step("lexes tilde")
val tokens = lex_cmm_line("  ~", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes bang

- lexes bang
- lexes bang
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes bang")
step("lexes bang")
val tokens = lex_cmm_line("  !", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes assign

- lexes assign
- lexes assign
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes assign")
step("lexes assign")
val tokens = lex_cmm_line("  =", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Delimiters

#### lexes left paren

- lexes left paren
- lexes left paren
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes left paren")
step("lexes left paren")
val tokens = lex_cmm_line("  (", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes right paren

- lexes right paren
- lexes right paren
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes right paren")
step("lexes right paren")
val tokens = lex_cmm_line("  )", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes left brace

- lexes left brace
- lexes left brace
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes left brace")
step("lexes left brace")
val tokens = lex_cmm_line("  {", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes right brace

- lexes right brace
- lexes right brace
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes right brace")
step("lexes right brace")
# Using }}} to produce single } inside string interpolation
val tokens = lex_cmm_line("  }", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes comma

- lexes comma
- lexes comma
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes comma")
step("lexes comma")
val tokens = lex_cmm_line("  ,", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Options

#### lexes option token

- lexes option token
- lexes option token
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes option token")
step("lexes option token")
val tokens = lex_cmm_line("  /Write", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes read option

- lexes read option
- lexes read option
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes read option")
step("lexes read option")
val tokens = lex_cmm_line("  /Read", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes create option

- lexes create option
- lexes create option
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes create option")
step("lexes create option")
val tokens = lex_cmm_line("  /Create", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - File Channels

#### lexes file channel 1

- lexes file channel 1
- lexes file channel 1
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes file channel 1")
step("lexes file channel 1")
val tokens = lex_cmm_line("  #1", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes file channel 2

- lexes file channel 2
- lexes file channel 2
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes file channel 2")
step("lexes file channel 2")
val tokens = lex_cmm_line("  #2", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Hash Classic Operators

#### lexes hash classic AND

- lexes hash classic AND
- lexes hash classic AND
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes hash classic AND")
step("lexes hash classic AND")
val tokens = lex_cmm_line("  #A#", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hash classic OR

- lexes hash classic OR
- lexes hash classic OR
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes hash classic OR")
step("lexes hash classic OR")
val tokens = lex_cmm_line("  #O#", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hash classic XOR

- lexes hash classic XOR
- lexes hash classic XOR
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes hash classic XOR")
step("lexes hash classic XOR")
val tokens = lex_cmm_line("  #X#", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Device Selectors

#### lexes device selector B::

- lexes device selector B::
- lexes device selector B::
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes device selector B::")
step("lexes device selector B::")
val tokens = lex_cmm_line("B::", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes device selector E::

- lexes device selector E::
- lexes device selector E::
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes device selector E::")
step("lexes device selector E::")
val tokens = lex_cmm_line("E::", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Identifiers

#### lexes simple identifier

- lexes simple identifier
- lexes simple identifier
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes simple identifier")
step("lexes simple identifier")
val tokens = lex_cmm_line("  Step", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes uppercase identifier

- lexes uppercase identifier
- lexes uppercase identifier
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes uppercase identifier")
step("lexes uppercase identifier")
val tokens = lex_cmm_line("  ENDDO", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes identifier with underscore

- lexes identifier with underscore
- lexes identifier with underscore
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes identifier with underscore")
step("lexes identifier with underscore")
val tokens = lex_cmm_line("  my_var", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Full Lines

#### lexes command with parameter

- lexes command with parameter
- lexes command with parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes command with parameter")
step("lexes command with parameter")
val tokens = lex_cmm_line("  SYStem.CPU 78K0R", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes command with hex parameter

- lexes command with hex parameter
- lexes command with hex parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes command with hex parameter")
step("lexes command with hex parameter")
val tokens = lex_cmm_line("  Data.dump 0x1000", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes macro assignment

- lexes macro assignment
- lexes macro assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes macro assignment")
step("lexes macro assignment")
val tokens = lex_cmm_line("  &cpu=CPU()", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes command with option

- lexes command with option
- lexes command with option


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes command with option")
step("lexes command with option")
val tokens = lex_cmm_line("  FLASH.Create 1. 0x0--0xFFF /Write", 1)
expect(tokens.len()).to_be_greater_than(3)
```

</details>

#### lexes print with string

- lexes print with string
- lexes print with string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes print with string")
step("lexes print with string")
val tokens = lex_cmm_line("  PRINT \"hello world\"", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes write with file channel

- lexes write with file channel
- lexes write with file channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes write with file channel")
step("lexes write with file channel")
val tokens = lex_cmm_line("  WRITE #1 \"data\"", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes range expression

- lexes range expression
- lexes range expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes range expression")
step("lexes range expression")
val tokens = lex_cmm_line("  0x1000--0x1FFF", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

### CMM Lexer - Full Source

#### lexes multi-line CMM source

- lexes multi-line CMM source
- lexes multi-line CMM source


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes multi-line CMM source")
step("lexes multi-line CMM source")
val source = "; comment\nstart:\n  SYStem.CPU ARM\n  ENDDO\n"
val tokens = lex_cmm_source(source)
# Should have: Comment, Newline, Label, Newline, DotCommand, Identifier, Newline, Identifier, Newline, Eof
expect(tokens.len()).to_be_greater_than(4)
```

</details>

#### lexes empty source

- lexes empty source
- lexes empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes empty source")
step("lexes empty source")
val tokens = lex_cmm_source("")
# At minimum there should be an Eof token
expect(tokens.len()).to_be_greater_than(0)
```

</details>

#### lexes source with line continuation

- lexes source with line continuation
- lexes source with line continuation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes source with line continuation")
step("lexes source with line continuation")
val source = "  Data.dump \\\n  0x1000\n"
val tokens = lex_cmm_source(source)
expect(tokens.len()).to_be_greater_than(2)
```

</details>

#### lexes real-world flash script

- lexes real-world flash script
- lexes real-world flash script


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lexes real-world flash script")
step("lexes real-world flash script")
val source = "; Flash programming\nFlashSetup:\n  LOCAL &size\n  ENTRY &size\n  FLASH.RESet\n  FLASH.Create 1. 0x0--0xFFF\n  RETURN\n"
val tokens = lex_cmm_source(source)
expect(tokens.len()).to_be_greater_than(10)
```

</details>

### CMM Lexer - Edge Cases

#### handles whitespace-only line

- handles whitespace-only line
- handles whitespace-only line
   - Expected: tokens.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles whitespace-only line")
step("handles whitespace-only line")
val tokens = lex_cmm_line("   ", 1)
expect(tokens.len()).to_equal(0)
```

</details>

#### handles tab whitespace

- handles tab whitespace
- handles tab whitespace
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles tab whitespace")
step("handles tab whitespace")
val tokens = lex_cmm_line("\tStep", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### preserves line numbers

- preserves line numbers
- preserves line numbers
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves line numbers")
step("preserves line numbers")
val tokens = lex_cmm_line("  Step", 42)
expect(tokens.len()).to_equal(1)
```

</details>

#### handles classic NOT operator N:

- handles classic NOT operator N:
- handles classic NOT operator N:
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles classic NOT operator N:")
step("handles classic NOT operator N:")
# N: is the classic NOT prefix operator
val tokens = lex_cmm_line("  N:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### handles slash as division when not followed by alpha

- handles slash as division when not followed by alpha
- handles slash as division when not followed by alpha
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles slash as division when not followed by alpha")
step("handles slash as division when not followed by alpha")
# / alone (not followed by alpha) should be Slash operator, not Option
val tokens = lex_cmm_line("  /", 1)
expect(tokens.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 95 |
| Active scenarios | 95 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-CMM-LSP-CMM-LEXER-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `434978bf1158c846a3ac9afb5bc5141df4deb2e6bdd99425487e787994baa2c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `434978bf1158c846a3ac9afb5bc5141df4deb2e6bdd99425487e787994baa2c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `434978bf1158c846a3ac9afb5bc5141df4deb2e6bdd99425487e787994baa2c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/cmm_lsp/cmm_lexer_spec.spl
mirror: doc/06_spec/feature/usage/cmm_lsp/cmm_lexer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cmm_lsp/cmm_lexer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cmm_lsp/cmm_lexer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cmm_lsp/cmm_lexer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 84 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/cmm_lsp/cmm_lexer_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexes semicolon comment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_lexer_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexes double-slash comment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_lexer_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexes semicolon comment with no trailing text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
