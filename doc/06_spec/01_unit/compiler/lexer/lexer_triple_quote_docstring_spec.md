# Lexer Triple Quote Docstring Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Triple Quote Docstring Specification

## Scenarios

### CoreLexer triple-quoted strings

#### joins each character slice once without immutable prefix growth

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler/10.frontend/core/lexer_struct.spl") ?? ""
val start = source.find("fn char_slice(start: i64, end: i64) -> text:") ?? -1
val end = source.find("fn token_kind() -> i64:") ?? -1
val body = if start >= 0 and end > start: source.substring(start, end) else: ""
expect(body).to_contain("parts.push(self.source_chars[i])")
expect(body).to_contain("parts.join(\"\")")
expect(body.contains("result = result + self.source_chars[i]")).to_be(false)
```

</details>

#### keeps exact parser token text without offset reconstruction

- parser init
- tokens push
- parser advance
   - Expected: tokens.join("|") equals `21:val|6:LIMIT|161::|6:i64|100:=|1:128|180:|190:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
parser_init("# —\nval LIMIT: i64 = 128\n")
var tokens: [text] = []
for i in 0..16:
    tokens.push("{par_kind_get()}:" + par_text_get())
    if par_kind_get() == 190:
        break
    parser_advance()
expect(tokens.join("|")).to_equal("21:val|6:LIMIT|161::|6:i64|100:=|1:128|180:|190:")
```

</details>

#### keeps a direct integer suffix after token construction

- lex init
   - Expected: lex_next() equals `7`
   - Expected: lex_token_text() equals `0`
   - Expected: lex_cur_suffix_get() equals `u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lex_init("0u32")
expect(lex_next()).to_equal(7)
expect(lex_token_text()).to_equal("0")
expect(lex_cur_suffix_get()).to_equal("u32")
```

</details>

#### lexes a multi-line docstring as one string token

- lex init
- kinds push
- string text = lex token text
   - Expected: error_count equals `0`
   - Expected: string_text contains `line one`
   - Expected: string_text contains `line two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn f() -> i64:\n    \"\"\"line one\n    line two\n    \"\"\"\n    1\n"
lex_init(src)
var kinds: [i64] = []
var string_text = ""
var error_count = 0
for i in 0..40:
    val k = lex_next()
    if k == 0:
        break
    kinds.push(k)
    if k == 3 and string_text == "":
        string_text = lex_token_text()
    if k == 191:
        error_count = error_count + 1
# No Error tokens, and the docstring is one String token containing
# both lines.
expect(error_count).to_equal(0)
expect(string_text.contains("line one")).to_equal(true)
expect(string_text.contains("line two")).to_equal(true)
```

</details>

#### lexes a single-line triple-quoted string as one token

- lex init
- found = lex token text
   - Expected: errors equals `0`
   - Expected: found equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lex_init("val x = \"\"\"abc\"\"\"\n")
var found = ""
var errors = 0
for i in 0..20:
    val k = lex_next()
    if k == 0:
        break
    if k == 3:
        found = lex_token_text()
    if k == 191:
        errors = errors + 1
expect(errors).to_equal(0)
expect(found).to_equal("abc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_triple_quote_docstring_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CoreLexer triple-quoted strings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
