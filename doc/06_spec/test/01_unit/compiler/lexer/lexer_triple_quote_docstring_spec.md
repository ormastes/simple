# Lexer Triple Quote Docstring Specification

> <details>

<!-- sdn-diagram:id=lexer_triple_quote_docstring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_triple_quote_docstring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_triple_quote_docstring_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lexer_triple_quote_docstring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Triple Quote Docstring Specification

## Scenarios

### CoreLexer triple-quoted strings

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CoreLexer triple-quoted strings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
