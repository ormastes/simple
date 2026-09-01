# lexer_intensive_spec

> Purpose: Prove that core.lexer (intensive).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 60 | 60 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lexer_intensive_spec

Purpose: Prove that core.lexer (intensive).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/lexer_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that core.lexer (intensive).
Audience: COMP-CORE maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### core.lexer (intensive)

#### handles string escapes and unknown escapes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles string escapes and unknown escapes
- Verify: handles string escapes and unknown escapes
   - Expected: kinds[0] equals `TOK_STRING_LIT`
   - Expected: text contains `\n`
   - Expected: text contains `\t`
   - Expected: text contains `\r`
   - Expected: text contains `\\`
   - Expected: text contains `"`
   - Expected: text contains `'`
   - Expected: text contains `\\q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles string escapes and unknown escapes")
step("Verify: handles string escapes and unknown escapes")
# @req: REQ-COMP-CORE-CORE-LEXER-INTENSIVE-001
val src = "\"" + "a" + "\\n" + "\\t" + "\\r" + "\\\\" + "\\\"" + "\\'" + "\\0" + "\\q" + "\""
var kinds = collect_kinds(src)
expect(kinds[0]).to_equal(TOK_STRING_LIT)
var texts = collect_texts(src)
val text = texts[0]
expect(text.contains("\n")).to_equal(true)
expect(text.contains("\t")).to_equal(true)
expect(text.contains("\r")).to_equal(true)
expect(text.contains("\\")).to_equal(true)
expect(text.contains("\"" )).to_equal(true)
expect(text.contains("'")).to_equal(true)
# Unknown escape preserved as \q
expect(text.contains("\\q")).to_equal(true)
```

</details>

#### reports unterminated strings

- reports unterminated strings
- Verify: reports unterminated strings
   - Expected: find_kind(kinds, TOK_ERROR) is true
   - Expected: texts[0] contains `unterminated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("reports unterminated strings")
step("Verify: reports unterminated strings")
var kinds = collect_kinds("\"unterminated\n")
expect(find_kind(kinds, TOK_ERROR)).to_equal(true)
var texts = collect_texts("\"unterminated\n")
expect(texts[0].contains("unterminated")).to_equal(true)
```

</details>

#### emits attribute token for #[

- emits attribute token for #[
- Verify: emits attribute token for #[
   - Expected: find_kind(kinds, TOK_HASH_LBRACKET) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("emits attribute token for #[")
step("Verify: emits attribute token for #[")
var kinds = collect_kinds("#[test]\n")
expect(find_kind(kinds, TOK_HASH_LBRACKET)).to_equal(true)
```

</details>

#### emits dedent at EOF when needed

- emits dedent at EOF when needed
- Verify: emits dedent at EOF when needed
   - Expected: find_kind(kinds, TOK_INDENT) is true
   - Expected: find_kind(kinds, TOK_DEDENT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("emits dedent at EOF when needed")
step("Verify: emits dedent at EOF when needed")
var kinds = collect_kinds("fn main():\n    val x = 1")
expect(find_kind(kinds, TOK_INDENT)).to_equal(true)
expect(find_kind(kinds, TOK_DEDENT)).to_equal(true)
```

</details>

#### suppresses newline inside parentheses

- suppresses newline inside parentheses
- Verify: suppresses newline inside parentheses
   - Expected: newlines equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("suppresses newline inside parentheses")
step("Verify: suppresses newline inside parentheses")
var kinds = collect_kinds("val x = (1 +\n 2)\n")
val newlines = count_kind(kinds, TOK_NEWLINE)
expect(newlines).to_equal(1)
```

</details>

#### reports unexpected characters

- reports unexpected characters
- Verify: reports unexpected characters
   - Expected: find_kind(kinds, TOK_ERROR) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("reports unexpected characters")
step("Verify: reports unexpected characters")
var kinds = collect_kinds("$\n")
expect(find_kind(kinds, TOK_ERROR)).to_equal(true)
```

</details>

#### handles empty source

- handles empty source
- Verify: handles empty source
   - Expected: kinds.len() equals `1`
   - Expected: kinds[0] equals `TOK_EOF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles empty source")
step("Verify: handles empty source")
var kinds = collect_kinds("")
expect(kinds.len()).to_equal(1)
expect(kinds[0]).to_equal(TOK_EOF)
```

</details>

#### handles single quote strings

- handles single quote strings
- Verify: handles single quote strings
   - Expected: kinds[0] equals `TOK_STRING_LIT`
   - Expected: texts[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single quote strings")
step("Verify: handles single quote strings")
var kinds = collect_kinds("'hello'\n")
expect(kinds[0]).to_equal(TOK_STRING_LIT)
var texts = collect_texts("'hello'\n")
expect(texts[0]).to_equal("hello")
```

</details>

#### handles exponent with plus sign

- handles exponent with plus sign
- Verify: handles exponent with plus sign
   - Expected: kinds[0] equals `TOK_FLOAT_LIT`
   - Expected: texts[0] equals `1e+10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles exponent with plus sign")
step("Verify: handles exponent with plus sign")
var kinds = collect_kinds("1e+10\n")
expect(kinds[0]).to_equal(TOK_FLOAT_LIT)
var texts = collect_texts("1e+10\n")
expect(texts[0]).to_equal("1e+10")
```

</details>

#### handles exponent with minus sign

- handles exponent with minus sign
- Verify: handles exponent with minus sign
   - Expected: kinds[0] equals `TOK_FLOAT_LIT`
   - Expected: texts[0] equals `1e-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles exponent with minus sign")
step("Verify: handles exponent with minus sign")
var kinds = collect_kinds("1e-5\n")
expect(kinds[0]).to_equal(TOK_FLOAT_LIT)
var texts = collect_texts("1e-5\n")
expect(texts[0]).to_equal("1e-5")
```

</details>

#### handles uppercase exponent

- handles uppercase exponent
- Verify: handles uppercase exponent
   - Expected: kinds[0] equals `TOK_FLOAT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles uppercase exponent")
step("Verify: handles uppercase exponent")
var kinds = collect_kinds("1E10\n")
expect(kinds[0]).to_equal(TOK_FLOAT_LIT)
```

</details>

#### handles number with underscore separators

- handles number with underscore separators
- Verify: handles number with underscore separators
   - Expected: kinds[0] equals `TOK_INT_LIT`
   - Expected: texts[0] equals `1_000_000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles number with underscore separators")
step("Verify: handles number with underscore separators")
var kinds = collect_kinds("1_000_000\n")
expect(kinds[0]).to_equal(TOK_INT_LIT)
var texts = collect_texts("1_000_000\n")
expect(texts[0]).to_equal("1_000_000")
```

</details>

#### handles float decimal with underscores

- handles float decimal with underscores
- Verify: handles float decimal with underscores
   - Expected: kinds[0] equals `TOK_FLOAT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles float decimal with underscores")
step("Verify: handles float decimal with underscores")
var kinds = collect_kinds("1_234.567_8\n")
expect(kinds[0]).to_equal(TOK_FLOAT_LIT)
```

</details>

#### handles zero as regular number

- handles zero as regular number
- Verify: handles zero as regular number
   - Expected: kinds[0] equals `TOK_INT_LIT`
   - Expected: texts[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles zero as regular number")
step("Verify: handles zero as regular number")
var kinds = collect_kinds("0\n")
expect(kinds[0]).to_equal(TOK_INT_LIT)
var texts = collect_texts("0\n")
expect(texts[0]).to_equal("0")
```

</details>

#### handles tab indentation

- handles tab indentation
- Verify: handles tab indentation
   - Expected: find_kind(kinds, TOK_INDENT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles tab indentation")
step("Verify: handles tab indentation")
var kinds = collect_kinds("fn f():\n\tval x = 1\n")
expect(find_kind(kinds, TOK_INDENT)).to_equal(true)
```

</details>

#### handles multiple dedent levels

- handles multiple dedent levels
- Verify: handles multiple dedent levels
   - Expected: dedents >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles multiple dedent levels")
step("Verify: handles multiple dedent levels")
val src = "fn f():\n    if true:\n        val x = 1\nval y = 2\n"
var kinds = collect_kinds(src)
val dedents = count_kind(kinds, TOK_DEDENT)
expect(dedents >= 2).to_equal(true)
```

</details>

#### handles spread operator ...

- handles spread operator ...
- Verify: handles spread operator ...
   - Expected: find_kind(kinds, TOK_DOTDOTDOT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles spread operator ...")
step("Verify: handles spread operator ...")
var kinds = collect_kinds("...\n")
expect(find_kind(kinds, TOK_DOTDOTDOT)).to_equal(true)
```

</details>

#### handles inclusive range ..=

- handles inclusive range ..=
- Verify: handles inclusive range ..=
   - Expected: find_kind(kinds, TOK_DOTDOT_EQ) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles inclusive range ..=")
step("Verify: handles inclusive range ..=")
var kinds = collect_kinds("0..=10\n")
expect(find_kind(kinds, TOK_DOTDOT_EQ)).to_equal(true)
```

</details>

#### handles single dot

- handles single dot
- Verify: handles single dot
   - Expected: find_kind(kinds, TOK_DOT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single dot")
step("Verify: handles single dot")
var kinds = collect_kinds("a.b\n")
expect(find_kind(kinds, TOK_DOT)).to_equal(true)
```

</details>

#### handles arrow operator

- handles arrow operator
- Verify: handles arrow operator
   - Expected: find_kind(kinds, TOK_ARROW) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles arrow operator")
step("Verify: handles arrow operator")
var kinds = collect_kinds("fn f() -> i64\n")
expect(find_kind(kinds, TOK_ARROW)).to_equal(true)
```

</details>

#### handles fat arrow operator

- handles fat arrow operator
- Verify: handles fat arrow operator
   - Expected: find_kind(kinds, TOK_FAT_ARROW) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles fat arrow operator")
step("Verify: handles fat arrow operator")
var kinds = collect_kinds("x => y\n")
expect(find_kind(kinds, TOK_FAT_ARROW)).to_equal(true)
```

</details>

#### handles plus assign

- handles plus assign
- Verify: handles plus assign
   - Expected: find_kind(kinds, TOK_PLUS_ASSIGN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles plus assign")
step("Verify: handles plus assign")
var kinds = collect_kinds("x += 1\n")
expect(find_kind(kinds, TOK_PLUS_ASSIGN)).to_equal(true)
```

</details>

#### handles minus assign

- handles minus assign
- Verify: handles minus assign
   - Expected: find_kind(kinds, TOK_MINUS_ASSIGN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles minus assign")
step("Verify: handles minus assign")
var kinds = collect_kinds("x -= 1\n")
expect(find_kind(kinds, TOK_MINUS_ASSIGN)).to_equal(true)
```

</details>

#### handles star assign

- handles star assign
- Verify: handles star assign
   - Expected: find_kind(kinds, TOK_STAR_ASSIGN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles star assign")
step("Verify: handles star assign")
var kinds = collect_kinds("x *= 2\n")
expect(find_kind(kinds, TOK_STAR_ASSIGN)).to_equal(true)
```

</details>

#### handles slash assign

- handles slash assign
- Verify: handles slash assign
   - Expected: find_kind(kinds, TOK_SLASH_ASSIGN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles slash assign")
step("Verify: handles slash assign")
var kinds = collect_kinds("x /= 2\n")
expect(find_kind(kinds, TOK_SLASH_ASSIGN)).to_equal(true)
```

</details>

#### handles single plus

- handles single plus
- Verify: handles single plus
   - Expected: find_kind(kinds, TOK_PLUS) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single plus")
step("Verify: handles single plus")
var kinds = collect_kinds("1 + 2\n")
expect(find_kind(kinds, TOK_PLUS)).to_equal(true)
```

</details>

#### handles single minus

- handles single minus
- Verify: handles single minus
   - Expected: find_kind(kinds, TOK_MINUS) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single minus")
step("Verify: handles single minus")
var kinds = collect_kinds("1 - 2\n")
expect(find_kind(kinds, TOK_MINUS)).to_equal(true)
```

</details>

#### handles single star

- handles single star
- Verify: handles single star
   - Expected: find_kind(kinds, TOK_STAR) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single star")
step("Verify: handles single star")
var kinds = collect_kinds("1 * 2\n")
expect(find_kind(kinds, TOK_STAR)).to_equal(true)
```

</details>

#### handles single slash

- handles single slash
- Verify: handles single slash
   - Expected: find_kind(kinds, TOK_SLASH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single slash")
step("Verify: handles single slash")
var kinds = collect_kinds("1 / 2\n")
expect(find_kind(kinds, TOK_SLASH)).to_equal(true)
```

</details>

#### handles percent operator

- handles percent operator
- Verify: handles percent operator
   - Expected: find_kind(kinds, TOK_PERCENT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles percent operator")
step("Verify: handles percent operator")
var kinds = collect_kinds("7 % 3\n")
expect(find_kind(kinds, TOK_PERCENT)).to_equal(true)
```

</details>

#### handles equals operator

- handles equals operator
- Verify: handles equals operator
   - Expected: find_kind(kinds, TOK_EQ) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles equals operator")
step("Verify: handles equals operator")
var kinds = collect_kinds("a == b\n")
expect(find_kind(kinds, TOK_EQ)).to_equal(true)
```

</details>

#### handles not equals operator

- handles not equals operator
- Verify: handles not equals operator
   - Expected: find_kind(kinds, TOK_NEQ) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles not equals operator")
step("Verify: handles not equals operator")
var kinds = collect_kinds("a != b\n")
expect(find_kind(kinds, TOK_NEQ)).to_equal(true)
```

</details>

#### handles single bang (not)

- handles single bang (not)
- Verify: handles single bang (not)
   - Expected: find_kind(kinds, TOK_NOT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single bang (not)")
step("Verify: handles single bang (not)")
var kinds = collect_kinds("!x\n")
expect(find_kind(kinds, TOK_NOT)).to_equal(true)
```

</details>

#### handles less than

- handles less than
- Verify: handles less than
   - Expected: find_kind(kinds, TOK_LT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles less than")
step("Verify: handles less than")
var kinds = collect_kinds("a < b\n")
expect(find_kind(kinds, TOK_LT)).to_equal(true)
```

</details>

#### handles greater than

- handles greater than
- Verify: handles greater than
   - Expected: find_kind(kinds, TOK_GT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles greater than")
step("Verify: handles greater than")
var kinds = collect_kinds("a > b\n")
expect(find_kind(kinds, TOK_GT)).to_equal(true)
```

</details>

#### handles less or equal

- handles less or equal
- Verify: handles less or equal
   - Expected: find_kind(kinds, TOK_LEQ) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles less or equal")
step("Verify: handles less or equal")
var kinds = collect_kinds("a <= b\n")
expect(find_kind(kinds, TOK_LEQ)).to_equal(true)
```

</details>

#### handles greater or equal

- handles greater or equal
- Verify: handles greater or equal
   - Expected: find_kind(kinds, TOK_GEQ) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles greater or equal")
step("Verify: handles greater or equal")
var kinds = collect_kinds("a >= b\n")
expect(find_kind(kinds, TOK_GEQ)).to_equal(true)
```

</details>

#### handles single assign

- handles single assign
- Verify: handles single assign
   - Expected: find_kind(kinds, TOK_ASSIGN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single assign")
step("Verify: handles single assign")
var kinds = collect_kinds("x = 1\n")
expect(find_kind(kinds, TOK_ASSIGN)).to_equal(true)
```

</details>

#### handles single question mark

- handles single question mark
- Verify: handles single question mark
   - Expected: find_kind(kinds, TOK_QUESTION) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single question mark")
step("Verify: handles single question mark")
var kinds = collect_kinds("opt?\n")
expect(find_kind(kinds, TOK_QUESTION)).to_equal(true)
```

</details>

#### handles single pipe

- handles single pipe
- Verify: handles single pipe
   - Expected: find_kind(kinds, TOK_PIPE) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles single pipe")
step("Verify: handles single pipe")
var kinds = collect_kinds("a | b\n")
expect(find_kind(kinds, TOK_PIPE)).to_equal(true)
```

</details>

#### handles at symbol

- handles at symbol
- Verify: handles at symbol
   - Expected: find_kind(kinds, TOK_AT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles at symbol")
step("Verify: handles at symbol")
var kinds = collect_kinds("@decorator\n")
expect(find_kind(kinds, TOK_AT)).to_equal(true)
```

</details>

#### handles semicolon

- handles semicolon
- Verify: handles semicolon
   - Expected: find_kind(kinds, TOK_SEMICOLON) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles semicolon")
step("Verify: handles semicolon")
var kinds = collect_kinds("x; y\n")
expect(find_kind(kinds, TOK_SEMICOLON)).to_equal(true)
```

</details>

#### handles colon

- handles colon
- Verify: handles colon
   - Expected: find_kind(kinds, TOK_COLON) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles colon")
step("Verify: handles colon")
var kinds = collect_kinds("x: i64\n")
expect(find_kind(kinds, TOK_COLON)).to_equal(true)
```

</details>

#### handles comma

- handles comma
- Verify: handles comma
   - Expected: find_kind(kinds, TOK_COMMA) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles comma")
step("Verify: handles comma")
var kinds = collect_kinds("a, b, c\n")
expect(find_kind(kinds, TOK_COMMA)).to_equal(true)
```

</details>

#### handles parentheses

- handles parentheses
- Verify: handles parentheses
   - Expected: find_kind(kinds, TOK_LPAREN) is true
   - Expected: find_kind(kinds, TOK_RPAREN) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles parentheses")
step("Verify: handles parentheses")
var kinds = collect_kinds("(1 + 2)\n")
expect(find_kind(kinds, TOK_LPAREN)).to_equal(true)
expect(find_kind(kinds, TOK_RPAREN)).to_equal(true)
```

</details>

#### handles brackets

- handles brackets
- Verify: handles brackets
   - Expected: find_kind(kinds, TOK_LBRACKET) is true
   - Expected: find_kind(kinds, TOK_RBRACKET) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles brackets")
step("Verify: handles brackets")
var kinds = collect_kinds("[1, 2]\n")
expect(find_kind(kinds, TOK_LBRACKET)).to_equal(true)
expect(find_kind(kinds, TOK_RBRACKET)).to_equal(true)
```

</details>

#### handles braces

- handles braces
- Verify: handles braces
   - Expected: find_kind(kinds, TOK_LBRACE) is true
   - Expected: find_kind(kinds, TOK_RBRACE) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles braces")
step("Verify: handles braces")
var kinds = collect_kinds("{key: val}\n")
expect(find_kind(kinds, TOK_LBRACE)).to_equal(true)
expect(find_kind(kinds, TOK_RBRACE)).to_equal(true)
```

</details>

#### handles nested brackets with depth tracking

- handles nested brackets with depth tracking
- Verify: handles nested brackets with depth tracking
   - Expected: lbrackets equals `3`
   - Expected: rbrackets equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles nested brackets with depth tracking")
step("Verify: handles nested brackets with depth tracking")
var kinds = collect_kinds("[[1], [2]]\n")
val lbrackets = count_kind(kinds, TOK_LBRACKET)
val rbrackets = count_kind(kinds, TOK_RBRACKET)
expect(lbrackets).to_equal(3)
expect(rbrackets).to_equal(3)
```

</details>

#### handles newline suppression in brackets

- handles newline suppression in brackets
- Verify: handles newline suppression in brackets
   - Expected: newlines equals `1)  # Only final newline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles newline suppression in brackets")
step("Verify: handles newline suppression in brackets")
var kinds = collect_kinds("[\n1,\n2\n]\n")
val newlines = count_kind(kinds, TOK_NEWLINE)
expect(newlines).to_equal(1)  # Only final newline
```

</details>

#### handles newline suppression in braces

- handles newline suppression in braces
- Verify: handles newline suppression in braces
   - Expected: newlines equals `1)  # Only final newline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles newline suppression in braces")
step("Verify: handles newline suppression in braces")
var kinds = collect_kinds("{\nkey:\nval\n}\n")
val newlines = count_kind(kinds, TOK_NEWLINE)
expect(newlines).to_equal(1)  # Only final newline
```

</details>

#### handles underscore as token

- handles underscore as token
- Verify: handles underscore as token
   - Expected: find_kind(kinds, TOK_UNDERSCORE) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles underscore as token")
step("Verify: handles underscore as token")
var kinds = collect_kinds("_ = 1\n")
expect(find_kind(kinds, TOK_UNDERSCORE)).to_equal(true)
```

</details>

#### handles keywords true/false/nil

- handles keywords true/false/nil
- Verify: handles keywords true/false/nil
   - Expected: find_kind(kinds, TOK_BOOL_LIT) is true
   - Expected: find_kind(kinds, TOK_NIL_LIT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles keywords true/false/nil")
step("Verify: handles keywords true/false/nil")
var kinds = collect_kinds("true false nil\n")
expect(find_kind(kinds, TOK_BOOL_LIT)).to_equal(true)
expect(find_kind(kinds, TOK_NIL_LIT)).to_equal(true)
```

</details>

#### handles range operator

- handles range operator
- Verify: handles range operator
   - Expected: find_kind(kinds, TOK_DOTDOT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles range operator")
step("Verify: handles range operator")
var kinds = collect_kinds("0..10\n")
expect(find_kind(kinds, TOK_DOTDOT)).to_equal(true)
```

</details>

#### handles binary literal with underscores

- handles binary literal with underscores
- Verify: handles binary literal with underscores
   - Expected: kinds[0] equals `TOK_INT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles binary literal with underscores")
step("Verify: handles binary literal with underscores")
var kinds = collect_kinds("0b1010_1100\n")
expect(kinds[0]).to_equal(TOK_INT_LIT)
```

</details>

#### handles hex literal with underscores

- handles hex literal with underscores
- Verify: handles hex literal with underscores
   - Expected: kinds[0] equals `TOK_INT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles hex literal with underscores")
step("Verify: handles hex literal with underscores")
var kinds = collect_kinds("0xDEAD_BEEF\n")
expect(kinds[0]).to_equal(TOK_INT_LIT)
```

</details>

#### handles octal literal with underscores

- handles octal literal with underscores
- Verify: handles octal literal with underscores
   - Expected: kinds[0] equals `TOK_INT_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles octal literal with underscores")
step("Verify: handles octal literal with underscores")
var kinds = collect_kinds("0o755\n")
expect(kinds[0]).to_equal(TOK_INT_LIT)
```

</details>

#### handles blank line between indented blocks

- handles blank line between indented blocks
- Verify: handles blank line between indented blocks
   - Expected: find_kind(kinds, TOK_IDENT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles blank line between indented blocks")
step("Verify: handles blank line between indented blocks")
val src = "fn f():\n    val x = 1\n\n    val y = 2\n"
var kinds = collect_kinds(src)
expect(find_kind(kinds, TOK_IDENT)).to_equal(true)
```

</details>

#### handles comment-only line in indented block

- handles comment-only line in indented block
- Verify: handles comment-only line in indented block
   - Expected: find_kind(kinds, TOK_KW_VAL) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles comment-only line in indented block")
step("Verify: handles comment-only line in indented block")
val src = "fn f():\n    # comment\n    val x = 1\n"
var kinds = collect_kinds(src)
expect(find_kind(kinds, TOK_KW_VAL)).to_equal(true)
```

</details>

#### handles .? operator

- handles .? operator
- Verify: handles .? operator
   - Expected: find_kind(kinds, TOK_DOT_QUESTION) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles .? operator")
step("Verify: handles .? operator")
var kinds = collect_kinds("a.?\n")
# TOK_QUESTION_DOT (131) is `?.`; `.?` is TOK_DOT_QUESTION (133).
# `collect_kinds("a.?\n")` is [TOK_IDENT, 133, TOK_NEWLINE, TOK_EOF].
expect(find_kind(kinds, TOK_DOT_QUESTION)).to_equal(true)
```

</details>

#### handles string at EOF without newline

- handles string at EOF without newline
- Verify: handles string at EOF without newline
   - Expected: kinds[0] equals `TOK_STRING_LIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles string at EOF without newline")
step("Verify: handles string at EOF without newline")
var kinds = collect_kinds("\"hello\"")
expect(kinds[0]).to_equal(TOK_STRING_LIT)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 60 |
| Active scenarios | 60 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER_CORE`
- `REQ-COMP-CORE-CORE-LEXER-INTENSIVE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bca72bddf770cf26ecdfb9ceeadecbd08966e35e8a8a441c162a3bfee5b88195`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bca72bddf770cf26ecdfb9ceeadecbd08966e35e8a8a441c162a3bfee5b88195`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bca72bddf770cf26ecdfb9ceeadecbd08966e35e8a8a441c162a3bfee5b88195`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler_core/lexer_intensive_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/lexer_intensive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/lexer_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/lexer_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/lexer_intensive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler_core/lexer_intensive_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles string escapes and unknown escapes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/lexer_intensive_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports unterminated strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/lexer_intensive_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits attribute token for #[' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
