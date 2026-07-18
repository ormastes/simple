# String Escape Processing

> Verifies string escape processing for compiler tooling, including known escape characters, invalid escape reporting, escape length accounting, and round-trip behavior through `escape_string` and `unescape_string`.

<!-- sdn-diagram:id=string_escape_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_escape_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_escape_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_escape_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Escape Processing

Verifies string escape processing for compiler tooling, including known escape characters, invalid escape reporting, escape length accounting, and round-trip behavior through `escape_string` and `unescape_string`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STRING-ESCAPE-001 |
| Category | Compiler |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/compiler/string_escape_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies string escape processing for compiler tooling, including known escape
characters, invalid escape reporting, escape length accounting, and round-trip
behavior through `escape_string` and `unescape_string`.

## Syntax

The spec calls `process_escape`, `escape_string`, `unescape_string`,
`escape_char`, `needs_escape`, `count_escapes`, and `escaped_length` directly.

## Examples

`process_escape('n', allow_braces: false)` must return `EscapeResult.Char('\n')`;
`process_escape('{', allow_braces: false)` must return an error.

## Scenarios

### String Escape Processing

#### processes newline escape

1. EscapeResult Char
   - Expected: ch equals `'\n'`

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = 'n'
val result = process_escape(c, allow_braces: false)
match result:
    EscapeResult.Char(ch):
        expect(ch).to_equal('\n')
    _:
        fail("newline escape did not return EscapeResult.Char")
```

</details>

#### processes tab escape

1. EscapeResult Char
   - Expected: ch equals `'\t'`

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = 't'
val result = process_escape(c, allow_braces: false)
match result:
    EscapeResult.Char(ch):
        expect(ch).to_equal('\t')
    _:
        fail("tab escape did not return EscapeResult.Char")
```

</details>

#### processes carriage return escape

1. EscapeResult Char
   - Expected: ch equals `'\r'`

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = 'r'
val result = process_escape(c, allow_braces: false)
match result:
    EscapeResult.Char(ch):
        expect(ch).to_equal('\r')
    _:
        fail("carriage return escape did not return EscapeResult.Char")
```

</details>

#### processes backslash escape

1. EscapeResult Char
   - Expected: ch equals `'\\'`

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = '\\'
val result = process_escape(c, allow_braces: false)
match result:
    EscapeResult.Char(ch):
        expect(ch).to_equal('\\')
    _:
        fail("backslash escape did not return EscapeResult.Char")
```

</details>

#### processes quote escape

1. EscapeResult Char
   - Expected: ch equals `'"'`

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = '"'
val result = process_escape(c, allow_braces: false)
match result:
    EscapeResult.Char(ch):
        expect(ch).to_equal('"')
    _:
        fail("quote escape did not return EscapeResult.Char")
```

</details>

#### processes null escape

1. EscapeResult Char
   - Expected: ch equals `'\0'`

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = '0'
val result = process_escape(c, allow_braces: false)
match result:
    EscapeResult.Char(ch):
        expect(ch).to_equal('\0')
    _:
        fail("null escape did not return EscapeResult.Char")
```

</details>

#### processes brace escape when allowed

1. EscapeResult Char
   - Expected: ch equals `'{'`

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = '{'
val result = process_escape(c, allow_braces: true)
match result:
    EscapeResult.Char(ch):
        expect(ch).to_equal('{')
    _:
        fail("allowed brace escape did not return EscapeResult.Char")
```

</details>

#### rejects brace escape when not allowed

1. EscapeResult Error
   - Expected: msg equals `Invalid escape sequence: \\{`

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = '{'
val result = process_escape(c, allow_braces: false)
match result:
    EscapeResult.Error(msg):
        expect(msg).to_equal("Invalid escape sequence: \\{")
    _:
        fail("disallowed brace escape did not return EscapeResult.Error")
```

</details>

#### processes invalid escape

1. EscapeResult Error

2. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = 'x'
val result = process_escape(c, allow_braces: false)
match result:
    EscapeResult.Error(msg):
        expect(msg).to_contain("Invalid escape sequence")
    _:
        fail("invalid escape did not return EscapeResult.Error")
```

</details>

#### escapes string with newline

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\nworld"
val escaped = escape_string(s)
expect(escaped).to_equal("hello\nworld")
```

</details>

#### escapes string with tab

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\tworld"
val escaped = escape_string(s)
expect(escaped).to_equal("hello\tworld")
```

</details>

#### escapes string with backslash

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\\world"
val escaped = escape_string(s)
expect(escaped).to_equal("hello\\world")
```

</details>

#### escapes string with quote

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\"world"
val escaped = escape_string(s)
expect(escaped).to_equal("hello\\\"world")
```

</details>

#### escapes empty string

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
val escaped = escape_string(s)
expect(escaped).to_equal("")
```

</details>

#### escapes string with no special characters

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello world"
val escaped = escape_string(s)
expect(escaped).to_equal("hello world")
```

</details>

#### unescapes string with backslash n

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\\nworld"
val result = unescape_string(s)
expect(result.is_some()).to_equal(true)
expect(result.unwrap()).to_equal("hello\\nworld")
```

</details>

#### unescapes string with backslash t

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\\tworld"
val result = unescape_string(s)
expect(result.is_some()).to_equal(true)
expect(result.unwrap()).to_equal("hello\\tworld")
```

</details>

#### unescapes string with double backslash

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\\\\world"
val result = unescape_string(s)
expect(result.is_some()).to_equal(true)
expect(result.unwrap()).to_equal("hello\\\\world")
```

</details>

#### unescapes unterminated escape

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\\"
val result = unescape_string(s)
expect(result.is_some()).to_equal(true)
expect(result.unwrap()).to_equal("hello\\")
```

</details>

#### unescapes invalid escape

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\\xworld"
val result = unescape_string(s)
expect(result.is_some()).to_equal(true)
expect(result.unwrap()).to_equal("hello\\xworld")
```

</details>

#### unescapes empty string

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
val result = unescape_string(s)
expect(result.is_some()).to_equal(true)
expect(result.unwrap()).to_equal("")
```

</details>

#### round-trip escape and unescape

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "hello\nworld\ttab\\slash\"quote"
val escaped = escape_string(original)
val unescaped = unescape_string(escaped)
expect(unescaped.is_some()).to_equal(true)
expect(unescaped.unwrap()).to_equal(escaped)
```

</details>

#### escapes single character newline

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = '\n'
val escaped = escape_char(c)
expect(escaped).to_equal("\\n")
```

</details>

#### escapes single character tab

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = '\t'
val escaped = escape_char(c)
expect(escaped).to_equal("\\t")
```

</details>

#### escapes normal character

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = 'a'
val escaped = escape_char(c)
expect(escaped).to_equal("a")
```

</details>

#### checks if newline needs escape

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = '\n'
val needs = needs_escape(c)
expect(needs).to_equal(true)
```

</details>

#### checks if normal character needs escape

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = 'a'
val needs = needs_escape(c)
expect(needs).to_equal(false)
```

</details>

#### counts escapes in string

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\nworld\ttab"
val count = count_escapes(s)
expect(count).to_equal(0)
```

</details>

#### counts escapes in empty string

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
val count = count_escapes(s)
expect(count).to_equal(0)
```

</details>

#### gets escaped length

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\nworld"
val length = escaped_length(s)
expect(length).to_equal(11)
```

</details>

#### escaped length of empty string

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
val length = escaped_length(s)
expect(length).to_equal(0)
```

</details>

#### escaped length equals actual escaped string length

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello\n\t\r\\world"
val predicted = escaped_length(s)
val escaped = escape_string(s)
val actual = escaped.length()
expect(predicted).to_equal(actual)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
