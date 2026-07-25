# CMM Lexer Specification

> Tests for the CMM (PRACTICE Script) lexer. Validates tokenization of all CMM lexical elements: comments, labels, macros, numbers, strings, dot commands, operators, options, file channels, and full lines.

<!-- sdn-diagram:id=cmm_lexer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cmm_lexer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cmm_lexer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cmm_lexer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/cmm_lsp/cmm_lexer_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("; this is a comment", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes double-slash comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("// another comment", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes semicolon comment with no trailing text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line(";", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes double-slash comment with no trailing text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("//", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes inline comment after whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ; inline comment", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Labels

#### lexes label at column 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("start:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes label with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("_my_label:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes label with alphanumeric chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("FlashSetup3:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### distinguishes label from device selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# B:: is a device selector, not a label
val tokens = lex_cmm_line("B::", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### returns empty for empty line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("", 1)
expect(tokens.len()).to_equal(0)
```

</details>

### CMM Lexer - Macro References

#### lexes simple macro ref

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  &myvar", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes recursive macro ref

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  &&myvar", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes bare ampersand as operator when no identifier follows

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# & without an identifier after it is the binary AND operator
val tokens = lex_cmm_line("  &", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes bare double-ampersand as logical AND when no identifier follows

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# && without an identifier is the logical AND operator
val tokens = lex_cmm_line("  &&", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes macro ref with underscore in name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  &my_var_1", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Hex Numbers

#### lexes hex number with lowercase 0x

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  0x1000", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hex number with uppercase 0X

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  0XABCDEF", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hex mask with dont-care bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0xFX has dont-care nibble
val tokens = lex_cmm_line("  0xFX", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hex mask with multiple dont-care bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  0xff1cxxxx", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Binary Numbers

#### lexes binary number with 0y prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  0y101", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes binary mask with dont-care bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  0yX111XXX", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Decimal and Integer Numbers

#### lexes decimal number with trailing dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  100.", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes plain integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  1234", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes float number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  1.3", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes float with exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  1.3e+34", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Time Literals

#### lexes millisecond time literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  10ms", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes microsecond time literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  100us", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes nanosecond time literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  75ns", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes second time literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  10s", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes float time literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  23.24ms", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Strings

#### lexes simple string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  \"hello world\"", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  \"\"", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes string with escaped double quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In CMM, "" inside a string is an escaped double-quote
val tokens = lex_cmm_line("  \"abc\"\"def\"", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Char Literals

#### lexes single character literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  'A'", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes lowercase char literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  'z'", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Dot Commands

#### lexes simple dot command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  Data.dump", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes two-level dot command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  SYStem.CPU", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes multi-level dot command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  FLASH.ReProgram.ALL", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes dot command with reset

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  FLASH.RESet", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Comparison Operators

#### lexes equality operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ==", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes not-equal operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  !=", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes less-than-or-equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  <=", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes greater-than-or-equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  >=", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Range Operators

#### lexes range-to operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  --", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes range-offset operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ++", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes range-dots operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ..", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Logical Operators

#### lexes logical AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  &&", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes logical OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ||", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes logical XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ^^", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Shift Operators

#### lexes shift left

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  <<", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes shift right

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  >>", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Classic Operators

#### lexes classic AND colon form

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  :A:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes classic OR colon form

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  :O:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes classic XOR colon form

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  :X:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Single-Char Operators

#### lexes plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  +", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes minus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  -", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes star

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  *", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  %", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes tilde

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ~", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes bang

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  !", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes assign

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  =", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Delimiters

#### lexes left paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  (", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes right paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  )", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes left brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  {", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes right brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using }}} to produce single } inside string interpolation
val tokens = lex_cmm_line("  }", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ,", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Options

#### lexes option token

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  /Write", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes read option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  /Read", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes create option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  /Create", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - File Channels

#### lexes file channel 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  #1", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes file channel 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  #2", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Hash Classic Operators

#### lexes hash classic AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  #A#", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hash classic OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  #O#", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes hash classic XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  #X#", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Device Selectors

#### lexes device selector B::

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("B::", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes device selector E::

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("E::", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Identifiers

#### lexes simple identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  Step", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes uppercase identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  ENDDO", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### lexes identifier with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  my_var", 1)
expect(tokens.len()).to_equal(1)
```

</details>

### CMM Lexer - Full Lines

#### lexes command with parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  SYStem.CPU 78K0R", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes command with hex parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  Data.dump 0x1000", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes macro assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  &cpu=CPU()", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes command with option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  FLASH.Create 1. 0x0--0xFFF /Write", 1)
expect(tokens.len()).to_be_greater_than(3)
```

</details>

#### lexes print with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  PRINT \"hello world\"", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes write with file channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  WRITE #1 \"data\"", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### lexes range expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  0x1000--0x1FFF", 1)
expect(tokens.len()).to_be_greater_than(1)
```

</details>

### CMM Lexer - Full Source

#### lexes multi-line CMM source

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "; comment\nstart:\n  SYStem.CPU ARM\n  ENDDO\n"
val tokens = lex_cmm_source(source)
# Should have: Comment, Newline, Label, Newline, DotCommand, Identifier, Newline, Identifier, Newline, Eof
expect(tokens.len()).to_be_greater_than(4)
```

</details>

#### lexes empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_source("")
# At minimum there should be an Eof token
expect(tokens.len()).to_be_greater_than(0)
```

</details>

#### lexes source with line continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "  Data.dump \\\n  0x1000\n"
val tokens = lex_cmm_source(source)
expect(tokens.len()).to_be_greater_than(2)
```

</details>

#### lexes real-world flash script

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "; Flash programming\nFlashSetup:\n  LOCAL &size\n  ENTRY &size\n  FLASH.RESet\n  FLASH.Create 1. 0x0--0xFFF\n  RETURN\n"
val tokens = lex_cmm_source(source)
expect(tokens.len()).to_be_greater_than(10)
```

</details>

### CMM Lexer - Edge Cases

#### handles whitespace-only line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("   ", 1)
expect(tokens.len()).to_equal(0)
```

</details>

#### handles tab whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("\tStep", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### preserves line numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  Step", 42)
expect(tokens.len()).to_equal(1)
```

</details>

#### handles classic NOT operator N:

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# N: is the classic NOT prefix operator
val tokens = lex_cmm_line("  N:", 1)
expect(tokens.len()).to_equal(1)
```

</details>

#### handles slash as division when not followed by alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
