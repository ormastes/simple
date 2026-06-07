# Blink CSS Parser Specification

> Tests for the flat CSS rule-list parser. Covers selector extraction, declaration parsing, !important detection, multi-rule sheets, and error-recovery when the input is malformed.

<!-- sdn-diagram:id=css_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=css_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

css_parser_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=css_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink CSS Parser Specification

Tests for the flat CSS rule-list parser. Covers selector extraction, declaration parsing, !important detection, multi-rule sheets, and error-recovery when the input is malformed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/01_unit/lib/blink/css_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the flat CSS rule-list parser. Covers selector extraction,
declaration parsing, !important detection, multi-rule sheets, and
error-recovery when the input is malformed.

## Design notes

- Tokens are constructed directly — no round-trip through tokenize_css.
- Whitespace is already absent from the token stream (tokenizer skips it).
- Selector text is reconstructed by space-joining token texts.

## Scenarios

### parse_css

#### empty token list produces empty stylesheet

1. CssToken
   - Expected: sheet.rules.len() equals `0`
   - Expected: sheet.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Eof, text: "", line: 1, column: 1)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(0)
expect(sheet.errors.len()).to_equal(0)
```

</details>

#### single rule \

1. CssToken
2. CssToken
3. CssToken
4. CssToken
5. CssToken
6. CssToken
7. CssToken
8. CssToken
9. CssToken
   - Expected: sheet.rules.len() equals `1`
   - Expected: rule.selector equals `. foo`
   - Expected: rule.declarations.len() equals `1`
   - Expected: decl.property equals `color`
   - Expected: decl.value equals `red`
   - Expected: not_important is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tokens: Delim(".") Identifier("foo") Delim("{") Identifier("color") Delim(":") Identifier("red") Delim(";") Delim("}") Eof
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Delim,      text: ".",     line: 1, column: 1),
    CssToken(kind: CssTokenKind.Identifier,  text: "foo",  line: 1, column: 2),
    CssToken(kind: CssTokenKind.Delim,       text: "{",    line: 1, column: 6),
    CssToken(kind: CssTokenKind.Identifier,  text: "color",line: 1, column: 8),
    CssToken(kind: CssTokenKind.Delim,       text: ":",    line: 1, column: 13),
    CssToken(kind: CssTokenKind.Identifier,  text: "red",  line: 1, column: 15),
    CssToken(kind: CssTokenKind.Delim,       text: ";",    line: 1, column: 18),
    CssToken(kind: CssTokenKind.Delim,       text: "}",    line: 1, column: 20),
    CssToken(kind: CssTokenKind.Eof,         text: "",     line: 1, column: 21)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)
val rule = sheet.rules[0]
expect(rule.selector).to_equal(". foo")
expect(rule.declarations.len()).to_equal(1)
val decl = rule.declarations[0]
expect(decl.property).to_equal("color")
expect(decl.value).to_equal("red")
val not_important = decl.important == false
expect(not_important).to_equal(true)
```

</details>

#### rule with multiple declarations produces correct count

1. CssToken
2. CssToken
3. CssToken
4. CssToken
5. CssToken
6. CssToken
7. CssToken
8. CssToken
9. CssToken
10. CssToken
11. CssToken
12. CssToken
13. CssToken
14. CssToken
15. CssToken
16. CssToken
17. CssToken
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.rules[0].declarations.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# .bar { margin: 0; padding: 4px; display: flex; }
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Delim,      text: ".",       line: 1, column: 1),
    CssToken(kind: CssTokenKind.Identifier,  text: "bar",    line: 1, column: 2),
    CssToken(kind: CssTokenKind.Delim,       text: "{",      line: 1, column: 6),
    CssToken(kind: CssTokenKind.Identifier,  text: "margin", line: 1, column: 8),
    CssToken(kind: CssTokenKind.Delim,       text: ":",      line: 1, column: 14),
    CssToken(kind: CssTokenKind.Number,      text: "0",      line: 1, column: 16),
    CssToken(kind: CssTokenKind.Delim,       text: ";",      line: 1, column: 17),
    CssToken(kind: CssTokenKind.Identifier,  text: "padding",line: 1, column: 19),
    CssToken(kind: CssTokenKind.Delim,       text: ":",      line: 1, column: 26),
    CssToken(kind: CssTokenKind.Identifier,  text: "4px",   line: 1, column: 28),
    CssToken(kind: CssTokenKind.Delim,       text: ";",      line: 1, column: 31),
    CssToken(kind: CssTokenKind.Identifier,  text: "display",line: 1, column: 33),
    CssToken(kind: CssTokenKind.Delim,       text: ":",      line: 1, column: 40),
    CssToken(kind: CssTokenKind.Identifier,  text: "flex",   line: 1, column: 42),
    CssToken(kind: CssTokenKind.Delim,       text: ";",      line: 1, column: 46),
    CssToken(kind: CssTokenKind.Delim,       text: "}",      line: 1, column: 48),
    CssToken(kind: CssTokenKind.Eof,         text: "",       line: 1, column: 49)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)
expect(sheet.rules[0].declarations.len()).to_equal(3)
```

</details>

#### declaration with !important sets important=true

1. CssToken
2. CssToken
3. CssToken
4. CssToken
5. CssToken
6. CssToken
7. CssToken
8. CssToken
9. CssToken
10. CssToken
   - Expected: sheet.rules.len() equals `1`
   - Expected: decl.value equals `blue`
   - Expected: decl.important is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# h1 { color: blue !important; }
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Identifier,  text: "h1",        line: 1, column: 1),
    CssToken(kind: CssTokenKind.Delim,       text: "{",         line: 1, column: 4),
    CssToken(kind: CssTokenKind.Identifier,  text: "color",     line: 1, column: 6),
    CssToken(kind: CssTokenKind.Delim,       text: ":",         line: 1, column: 11),
    CssToken(kind: CssTokenKind.Identifier,  text: "blue",      line: 1, column: 13),
    CssToken(kind: CssTokenKind.Delim,       text: "!",         line: 1, column: 18),
    CssToken(kind: CssTokenKind.Identifier,  text: "important", line: 1, column: 19),
    CssToken(kind: CssTokenKind.Delim,       text: ";",         line: 1, column: 28),
    CssToken(kind: CssTokenKind.Delim,       text: "}",         line: 1, column: 30),
    CssToken(kind: CssTokenKind.Eof,         text: "",          line: 1, column: 31)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)
val decl = sheet.rules[0].declarations[0]
expect(decl.value).to_equal("blue")
expect(decl.important).to_equal(true)
```

</details>

#### two rules produces 2 CssStyleRule entries

1. CssToken
2. CssToken
3. CssToken
4. CssToken
5. CssToken
6. CssToken
7. CssToken
8. CssToken
9. CssToken
10. CssToken
11. CssToken
12. CssToken
13. CssToken
14. CssToken
15. CssToken
   - Expected: sheet.rules.len() equals `2`
   - Expected: sheet.rules[0].selector equals `a`
   - Expected: sheet.rules[1].selector equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# a { color: red; } b { color: blue; }
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Identifier,  text: "a",     line: 1, column: 1),
    CssToken(kind: CssTokenKind.Delim,       text: "{",     line: 1, column: 3),
    CssToken(kind: CssTokenKind.Identifier,  text: "color", line: 1, column: 5),
    CssToken(kind: CssTokenKind.Delim,       text: ":",     line: 1, column: 10),
    CssToken(kind: CssTokenKind.Identifier,  text: "red",   line: 1, column: 12),
    CssToken(kind: CssTokenKind.Delim,       text: ";",     line: 1, column: 15),
    CssToken(kind: CssTokenKind.Delim,       text: "}",     line: 1, column: 17),
    CssToken(kind: CssTokenKind.Identifier,  text: "b",     line: 2, column: 1),
    CssToken(kind: CssTokenKind.Delim,       text: "{",     line: 2, column: 3),
    CssToken(kind: CssTokenKind.Identifier,  text: "color", line: 2, column: 5),
    CssToken(kind: CssTokenKind.Delim,       text: ":",     line: 2, column: 10),
    CssToken(kind: CssTokenKind.Identifier,  text: "blue",  line: 2, column: 12),
    CssToken(kind: CssTokenKind.Delim,       text: ";",     line: 2, column: 16),
    CssToken(kind: CssTokenKind.Delim,       text: "}",     line: 2, column: 18),
    CssToken(kind: CssTokenKind.Eof,         text: "",      line: 2, column: 19)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(2)
expect(sheet.rules[0].selector).to_equal("a")
expect(sheet.rules[1].selector).to_equal("b")
```

</details>

#### malformed input (missing {) records error, skips, continues

1. CssToken
2. CssToken
3. CssToken
   - Expected: sheet.rules.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "color red" with no braces — missing `{`, then a valid rule "p { font: sans; }"
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Identifier,  text: "color", line: 1, column: 1),
    CssToken(kind: CssTokenKind.Identifier,  text: "red",   line: 1, column: 7),
    CssToken(kind: CssTokenKind.Eof,         text: "",      line: 1, column: 10)
]
val sheet = parse_css(tokens)
# Reaches Eof without `{` — error should be recorded, no rules
expect(sheet.errors.len()).to_be_greater_than(0)
expect(sheet.rules.len()).to_equal(0)
```

</details>

#### property and value text are extracted correctly

1. CssToken
2. CssToken
3. CssToken
4. CssToken
5. CssToken
6. CssToken
7. CssToken
8. CssToken
   - Expected: sheet.rules.len() equals `1`
   - Expected: decl.property equals `background-color`
   - Expected: decl.value equals `336699`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# div { background-color: #336699; }
# Hash token strips the `#`, so text is "336699"
val tokens: [CssToken] = [
    CssToken(kind: CssTokenKind.Identifier,  text: "div",             line: 1, column: 1),
    CssToken(kind: CssTokenKind.Delim,       text: "{",               line: 1, column: 5),
    CssToken(kind: CssTokenKind.Identifier,  text: "background-color",line: 1, column: 7),
    CssToken(kind: CssTokenKind.Delim,       text: ":",               line: 1, column: 23),
    CssToken(kind: CssTokenKind.Hash,        text: "336699",          line: 1, column: 25),
    CssToken(kind: CssTokenKind.Delim,       text: ";",               line: 1, column: 31),
    CssToken(kind: CssTokenKind.Delim,       text: "}",               line: 1, column: 33),
    CssToken(kind: CssTokenKind.Eof,         text: "",                line: 1, column: 34)
]
val sheet = parse_css(tokens)
expect(sheet.rules.len()).to_equal(1)
val decl = sheet.rules[0].declarations[0]
expect(decl.property).to_equal("background-color")
expect(decl.value).to_equal("336699")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
