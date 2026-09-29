# String Operation Efficiency Specification

> Tests that string operations in the CMM LSP toolchain produce correct results after being rewritten from O(n²) character-by-character concatenation to O(n log n) segment-based approaches. Covers: escape_json, json_array, json_object, json_get_string, json_get_int, split_lines, lex_string_literal, to_upper_cmm, and join_parts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Operation Efficiency Specification

Tests that string operations in the CMM LSP toolchain produce correct results after being rewritten from O(n²) character-by-character concatenation to O(n log n) segment-based approaches. Covers: escape_json, json_array, json_object, json_get_string, json_get_int, split_lines, lex_string_literal, to_upper_cmm, and join_parts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-STR-EFF |
| Category | Tooling |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/feature/usage/cmm_lsp/string_efficiency_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that string operations in the CMM LSP toolchain produce correct results
after being rewritten from O(n²) character-by-character concatenation to
O(n log n) segment-based approaches. Covers: escape_json, json_array,
json_object, json_get_string, json_get_int, split_lines, lex_string_literal,
to_upper_cmm, and join_parts.

These are correctness tests that verify the optimized implementations match
the behavior of the original naive implementations. They include large-input
cases that would have been noticeably slow with the old O(n²) approach.

## Scenarios

### join_parts

#### basic cases

#### joins empty array

- joins empty array
- joins empty array
   - Expected: join_parts([]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins empty array")
step("joins empty array")
# @req: REQ-FEAT-CMM-LSP-STRING-EFFICIENCY-SPEC-001
expect(join_parts([])).to_equal("")
```

</details>

#### joins single element

- joins single element
- joins single element
   - Expected: join_parts(["hello"]) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins single element")
step("joins single element")
expect(join_parts(["hello"])).to_equal("hello")
```

</details>

#### joins two elements

- joins two elements
- joins two elements
   - Expected: join_parts(["hello", " world"]) equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins two elements")
step("joins two elements")
expect(join_parts(["hello", " world"])).to_equal("hello world")
```

</details>

#### joins three elements

- joins three elements
- joins three elements
   - Expected: join_parts(["a", "b", "c"]) equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins three elements")
step("joins three elements")
expect(join_parts(["a", "b", "c"])).to_equal("abc")
```

</details>

#### joins four elements

- joins four elements
- joins four elements
   - Expected: join_parts(["1", "2", "3", "4"]) equals `1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins four elements")
step("joins four elements")
expect(join_parts(["1", "2", "3", "4"])).to_equal("1234")
```

</details>

#### batch path (more than 4 elements)

#### joins 5 elements

- joins 5 elements
- joins 5 elements
   - Expected: join_parts(["a", "b", "c", "d", "e"]) equals `abcde`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins 5 elements")
step("joins 5 elements")
expect(join_parts(["a", "b", "c", "d", "e"])).to_equal("abcde")
```

</details>

#### joins 8 elements — exact batch

- joins 8 elements — exact batch
- joins 8 elements — exact batch
   - Expected: join_parts(["1", "2", "3", "4", "5", "6", "7", "8"]) equals `12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins 8 elements — exact batch")
step("joins 8 elements — exact batch")
expect(join_parts(["1", "2", "3", "4", "5", "6", "7", "8"])).to_equal("12345678")
```

</details>

#### joins 9 elements — batch + remainder

- joins 9 elements — batch + remainder
- joins 9 elements — batch + remainder
   - Expected: join_parts(["a", "b", "c", "d", "e", "f", "g", "h", "i"]) equals `abcdefghi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins 9 elements — batch + remainder")
step("joins 9 elements — batch + remainder")
expect(join_parts(["a", "b", "c", "d", "e", "f", "g", "h", "i"])).to_equal("abcdefghi")
```

</details>

#### joins 16 elements — two full batches

- joins 16 elements — two full batches
- joins 16 elements — two full batches
   - Expected: join_parts(parts) equals `xxxxxxxxxxxxxxxx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins 16 elements — two full batches")
step("joins 16 elements — two full batches")
var parts: [text] = []
var i = 0
while i < 16:
    parts.push("x")
    i = i + 1
expect(join_parts(parts)).to_equal("xxxxxxxxxxxxxxxx")
```

</details>

#### large inputs — would be slow with O(n²)

#### joins 100 single-char parts

- joins 100 single-char parts
- joins 100 single-char parts
   - Expected: result.len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins 100 single-char parts")
step("joins 100 single-char parts")
var parts: [text] = []
var i = 0
while i < 100:
    parts.push("a")
    i = i + 1
val result = join_parts(parts)
expect(result.len()).to_equal(100)
```

</details>

#### joins 500 single-char parts

- joins 500 single-char parts
- joins 500 single-char parts
   - Expected: result.len() equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins 500 single-char parts")
step("joins 500 single-char parts")
var parts: [text] = []
var i = 0
while i < 500:
    parts.push("b")
    i = i + 1
val result = join_parts(parts)
expect(result.len()).to_equal(500)
```

</details>

#### mixed-length segments

#### joins segments of varying length

- joins segments of varying length
- joins segments of varying length
   - Expected: join_parts(["hello", " ", "world", "!", " ", "foo"]) equals `hello world! foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins segments of varying length")
step("joins segments of varying length")
expect(join_parts(["hello", " ", "world", "!", " ", "foo"])).to_equal("hello world! foo")
```

</details>

#### joins with empty segments

- joins with empty segments
- joins with empty segments
   - Expected: join_parts(["a", "", "b", "", "c"]) equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins with empty segments")
step("joins with empty segments")
expect(join_parts(["a", "", "b", "", "c"])).to_equal("abc")
```

</details>

### to_upper_cmm

#### fast path — already uppercase

#### returns uppercase string unchanged

- returns uppercase string unchanged
- returns uppercase string unchanged
   - Expected: to_upper_cmm("IF") equals `IF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns uppercase string unchanged")
step("returns uppercase string unchanged")
expect(to_upper_cmm("IF")).to_equal("IF")
```

</details>

#### returns uppercase keyword unchanged

- returns uppercase keyword unchanged
- returns uppercase keyword unchanged
   - Expected: to_upper_cmm("WHILE") equals `WHILE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns uppercase keyword unchanged")
step("returns uppercase keyword unchanged")
expect(to_upper_cmm("WHILE")).to_equal("WHILE")
```

</details>

#### returns numbers/symbols unchanged

- returns numbers/symbols unchanged
- returns numbers/symbols unchanged
   - Expected: to_upper_cmm("123_ABC") equals `123_ABC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns numbers/symbols unchanged")
step("returns numbers/symbols unchanged")
expect(to_upper_cmm("123_ABC")).to_equal("123_ABC")
```

</details>

#### conversion cases

#### converts lowercase to uppercase

- converts lowercase to uppercase
- converts lowercase to uppercase
   - Expected: to_upper_cmm("if") equals `IF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts lowercase to uppercase")
step("converts lowercase to uppercase")
expect(to_upper_cmm("if")).to_equal("IF")
```

</details>

#### converts mixed case

- converts mixed case
- converts mixed case
   - Expected: to_upper_cmm("While") equals `WHILE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts mixed case")
step("converts mixed case")
expect(to_upper_cmm("While")).to_equal("WHILE")
```

</details>

#### converts all lowercase keyword

- converts all lowercase keyword
- converts all lowercase keyword
   - Expected: to_upper_cmm("repeat") equals `REPEAT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts all lowercase keyword")
step("converts all lowercase keyword")
expect(to_upper_cmm("repeat")).to_equal("REPEAT")
```

</details>

#### converts long keyword

- converts long keyword
- converts long keyword
   - Expected: to_upper_cmm("globalon") equals `GLOBALON`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts long keyword")
step("converts long keyword")
expect(to_upper_cmm("globalon")).to_equal("GLOBALON")
```

</details>

#### converts single char

- converts single char
- converts single char
   - Expected: to_upper_cmm("a") equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts single char")
step("converts single char")
expect(to_upper_cmm("a")).to_equal("A")
```

</details>

#### edge cases

#### handles empty string

- handles empty string
- handles empty string
   - Expected: to_upper_cmm("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles empty string")
step("handles empty string")
expect(to_upper_cmm("")).to_equal("")
```

</details>

#### preserves underscores and digits

- preserves underscores and digits
- preserves underscores and digits
   - Expected: to_upper_cmm("my_var_123") equals `MY_VAR_123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves underscores and digits")
step("preserves underscores and digits")
expect(to_upper_cmm("my_var_123")).to_equal("MY_VAR_123")
```

</details>

#### large input — would be slow with O(n²)

#### converts 200 lowercase chars

- converts 200 lowercase chars
- converts 200 lowercase chars
   - Expected: result.len() equals `200`
   - Expected: result[0:1] equals `A`
   - Expected: result[199:200] equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts 200 lowercase chars")
step("converts 200 lowercase chars")
val input = repeat_char("a", 200)
val result = to_upper_cmm(input)
expect(result.len()).to_equal(200)
expect(result[0:1]).to_equal("A")
expect(result[199:200]).to_equal("A")
```

</details>

### escape_json

#### fast path — no special characters

#### returns plain string unchanged

- returns plain string unchanged
- returns plain string unchanged
   - Expected: escape_json("hello world") equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns plain string unchanged")
step("returns plain string unchanged")
expect(escape_json("hello world")).to_equal("hello world")
```

</details>

#### returns empty string unchanged

- returns empty string unchanged
- returns empty string unchanged
   - Expected: escape_json("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns empty string unchanged")
step("returns empty string unchanged")
expect(escape_json("")).to_equal("")
```

</details>

#### returns alphanumeric unchanged

- returns alphanumeric unchanged
- returns alphanumeric unchanged
   - Expected: escape_json("abc123XYZ") equals `abc123XYZ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns alphanumeric unchanged")
step("returns alphanumeric unchanged")
expect(escape_json("abc123XYZ")).to_equal("abc123XYZ")
```

</details>

#### escaping individual special characters

#### escapes backslash

- escapes backslash
- escapes backslash
   - Expected: escape_json("a\\b") equals `a\\\\b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes backslash")
step("escapes backslash")
expect(escape_json("a\\b")).to_equal("a\\\\b")
```

</details>

#### escapes double quote

- escapes double quote
- escapes double quote
   - Expected: escape_json(input) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes double quote")
step("escapes double quote")
val input = "say \"hello\""
val expected = "say \\\"hello\\\""
expect(escape_json(input)).to_equal(expected)
```

</details>

#### escapes newline

- escapes newline
- escapes newline
   - Expected: escape_json("line1\nline2") equals `line1\\nline2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes newline")
step("escapes newline")
expect(escape_json("line1\nline2")).to_equal("line1\\nline2")
```

</details>

#### escapes carriage return

- escapes carriage return
- escapes carriage return
   - Expected: escape_json("line1\rline2") equals `line1\\rline2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes carriage return")
step("escapes carriage return")
expect(escape_json("line1\rline2")).to_equal("line1\\rline2")
```

</details>

#### escapes tab

- escapes tab
- escapes tab
   - Expected: escape_json("col1\tcol2") equals `col1\\tcol2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes tab")
step("escapes tab")
expect(escape_json("col1\tcol2")).to_equal("col1\\tcol2")
```

</details>

#### multiple special characters

#### escapes string with multiple specials

- escapes string with multiple specials
- escapes string with multiple specials
   - Expected: escape_json("a\nb\\c\"d") equals `a\\nb\\\\c\\"d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes string with multiple specials")
step("escapes string with multiple specials")
expect(escape_json("a\nb\\c\"d")).to_equal("a\\nb\\\\c\\\"d")
```

</details>

#### escapes only-specials string

- escapes only-specials string
- escapes only-specials string
   - Expected: escape_json("\n\t\\") equals `\\n\\t\\\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes only-specials string")
step("escapes only-specials string")
expect(escape_json("\n\t\\")).to_equal("\\n\\t\\\\")
```

</details>

#### special at boundaries

#### escapes special at start

- escapes special at start
- escapes special at start
   - Expected: escape_json("\nhello") equals `\\nhello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes special at start")
step("escapes special at start")
expect(escape_json("\nhello")).to_equal("\\nhello")
```

</details>

#### escapes special at end

- escapes special at end
- escapes special at end
   - Expected: escape_json("hello\n") equals `hello\\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes special at end")
step("escapes special at end")
expect(escape_json("hello\n")).to_equal("hello\\n")
```

</details>

#### escapes consecutive specials

- escapes consecutive specials
- escapes consecutive specials
   - Expected: escape_json("\n\n\n") equals `\\n\\n\\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes consecutive specials")
step("escapes consecutive specials")
expect(escape_json("\n\n\n")).to_equal("\\n\\n\\n")
```

</details>

#### large input — would be slow with O(n²)

#### escapes 500 chars with scattered specials

- escapes 500 chars with scattered specials
- escapes 500 chars with scattered specials
   - Expected: result.len() equals `510`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("escapes 500 chars with scattered specials")
step("escapes 500 chars with scattered specials")
# Build a string with a newline every 50 chars
var parts: [text] = []
var i = 0
while i < 10:
    parts.push(repeat_char("x", 49))
    parts.push("\n")
    i = i + 1
val input = join_parts(parts)
val result = escape_json(input)
# Each \n becomes \\n (2 chars), so result is 10*49 + 10*2 = 510
expect(result.len()).to_equal(510)
```

</details>

### json_array

#### basic arrays

#### builds empty array

- builds empty array
- builds empty array
   - Expected: json_array([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds empty array")
step("builds empty array")
expect(json_array([])).to_equal("[]")
```

</details>

#### builds single-element array

- builds single-element array
- builds single-element array
   - Expected: json_array(["1"]) equals `[1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds single-element array")
step("builds single-element array")
expect(json_array(["1"])).to_equal("[1]")
```

</details>

#### builds two-element array

- builds two-element array
- builds two-element array
   - Expected: json_array(["1", "2"]) equals `[1,2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds two-element array")
step("builds two-element array")
expect(json_array(["1", "2"])).to_equal("[1,2]")
```

</details>

#### builds multi-element array

- builds multi-element array
- builds multi-element array
   - Expected: json_array(["1", "2", "3", "4"]) equals `[1,2,3,4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds multi-element array")
step("builds multi-element array")
expect(json_array(["1", "2", "3", "4"])).to_equal("[1,2,3,4]")
```

</details>

#### with string values

#### builds array of JSON strings

- builds array of JSON strings
- builds array of JSON strings
   - Expected: json_array(items) equals `["a","b"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds array of JSON strings")
step("builds array of JSON strings")
val items = [json_string("a"), json_string("b")]
expect(json_array(items)).to_equal("[\"a\",\"b\"]")
```

</details>

#### large array — would be slow with O(n²)

#### builds array with 100 elements

- builds array with 100 elements
- builds array with 100 elements
   - Expected: result[0:1] equals `[`
   - Expected: result[result.len() - 1:result.len()] equals `]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds array with 100 elements")
step("builds array with 100 elements")
var items: [text] = []
var i = 0
while i < 100:
    items.push("0")
    i = i + 1
val result = json_array(items)
expect(result[0:1]).to_equal("[")
expect(result[result.len() - 1:result.len()]).to_equal("]")
```

</details>

### json_object

#### basic objects

#### builds empty object

- builds empty object
- builds empty object
   - Expected: json_object([]) equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds empty object")
step("builds empty object")
expect(json_object([])).to_equal("{}")
```

</details>

#### builds single-pair object

- builds single-pair object
- builds single-pair object
   - Expected: json_object(pairs) equals `{"a":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds single-pair object")
step("builds single-pair object")
val pairs = [JsonPair(key: "a", value: "1")]
expect(json_object(pairs)).to_equal("{\"a\":1}")
```

</details>

#### builds multi-pair object

- builds multi-pair object
- builds multi-pair object
   - Expected: json_object(pairs) equals `{"x":1,"y":2}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds multi-pair object")
step("builds multi-pair object")
val pairs = [
    JsonPair(key: "x", value: "1"),
    JsonPair(key: "y", value: "2")
]
expect(json_object(pairs)).to_equal("{\"x\":1,\"y\":2}")
```

</details>

#### with string values

#### builds object with string values

- builds object with string values
- builds object with string values
   - Expected: json_object(pairs) equals `{"name":"test"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds object with string values")
step("builds object with string values")
val pairs = [JsonPair(key: "name", value: json_string("test"))]
expect(json_object(pairs)).to_equal("{\"name\":\"test\"}")
```

</details>

#### large object — would be slow with O(n²)

#### builds object with 50 pairs

- builds object with 50 pairs
- builds object with 50 pairs
   - Expected: result[0:1] equals `{`
   - Expected: result[result.len() - 1:result.len()] equals `}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds object with 50 pairs")
step("builds object with 50 pairs")
var pairs: [JsonPair] = []
var i = 0
while i < 50:
    pairs.push(JsonPair(key: "k", value: "0"))
    i = i + 1
val result = json_object(pairs)
expect(result[0:1]).to_equal("{")
expect(result[result.len() - 1:result.len()]).to_equal("}")
```

</details>

### split_lines

#### basic splitting

#### splits empty string into one empty line

- splits empty string into one empty line
- splits empty string into one empty line
   - Expected: result.len() equals `1`
   - Expected: result[0] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits empty string into one empty line")
step("splits empty string into one empty line")
val result = split_lines("")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("")
```

</details>

#### splits single line without newline

- splits single line without newline
- splits single line without newline
   - Expected: result.len() equals `1`
   - Expected: result[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits single line without newline")
step("splits single line without newline")
val result = split_lines("hello")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("hello")
```

</details>

#### splits two lines

- splits two lines
- splits two lines
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `line1`
   - Expected: result[1] equals `line2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits two lines")
step("splits two lines")
val result = split_lines("line1\nline2")
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("line1")
expect(result[1]).to_equal("line2")
```

</details>

#### splits three lines

- splits three lines
- splits three lines
   - Expected: result.len() equals `3`
   - Expected: result[0] equals `a`
   - Expected: result[1] equals `b`
   - Expected: result[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits three lines")
step("splits three lines")
val result = split_lines("a\nb\nc")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("b")
expect(result[2]).to_equal("c")
```

</details>

#### trailing newline

#### splits with trailing newline — produces empty last line

- splits with trailing newline — produces empty last line
- splits with trailing newline — produces empty last line
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `hello`
   - Expected: result[1] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits with trailing newline — produces empty last line")
step("splits with trailing newline — produces empty last line")
val result = split_lines("hello\n")
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("hello")
expect(result[1]).to_equal("")
```

</details>

#### empty lines

#### handles consecutive newlines

- handles consecutive newlines
- handles consecutive newlines
   - Expected: result.len() equals `3`
   - Expected: result[0] equals `a`
   - Expected: result[1] equals ``
   - Expected: result[2] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles consecutive newlines")
step("handles consecutive newlines")
val result = split_lines("a\n\nb")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("")
expect(result[2]).to_equal("b")
```

</details>

#### handles only newlines

- handles only newlines
- handles only newlines
   - Expected: result.len() equals `3`
   - Expected: result[0] equals ``
   - Expected: result[1] equals ``
   - Expected: result[2] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles only newlines")
step("handles only newlines")
val result = split_lines("\n\n")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("")
expect(result[1]).to_equal("")
expect(result[2]).to_equal("")
```

</details>

#### CMM-like content

#### splits typical CMM script

- splits typical CMM script
- splits typical CMM script
   - Expected: result.len() equals `4`
   - Expected: result[0] equals `; Setup`
   - Expected: result[1] equals `SYStem.CPU CortexM4`
   - Expected: result[2] equals `SYStem.Up`
   - Expected: result[3] equals `; Done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits typical CMM script")
step("splits typical CMM script")
val source = "; Setup\nSYStem.CPU CortexM4\nSYStem.Up\n; Done"
val result = split_lines(source)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal("; Setup")
expect(result[1]).to_equal("SYStem.CPU CortexM4")
expect(result[2]).to_equal("SYStem.Up")
expect(result[3]).to_equal("; Done")
```

</details>

#### large input

#### splits 200 lines

- splits 200 lines
- splits 200 lines
   - Expected: result.len() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits 200 lines")
step("splits 200 lines")
var parts: [text] = []
var i = 0
while i < 200:
    parts.push("line")
    i = i + 1
val source = join_parts_with_sep(parts, "\n")
val result = split_lines(source)
expect(result.len()).to_equal(200)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-CMM-LSP-STRING-EFFICIENCY-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `17e36b7786909c04ac0a4448ceb7ad48c87605dd6f2919b711329ed3348b7342`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17e36b7786909c04ac0a4448ceb7ad48c87605dd6f2919b711329ed3348b7342`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17e36b7786909c04ac0a4448ceb7ad48c87605dd6f2919b711329ed3348b7342`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/cmm_lsp/string_efficiency_spec.spl
mirror: doc/06_spec/feature/usage/cmm_lsp/string_efficiency_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cmm_lsp/string_efficiency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cmm_lsp/string_efficiency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cmm_lsp/string_efficiency_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/cmm_lsp/string_efficiency_spec.spl:245:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins empty array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/string_efficiency_spec.spl:252:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins single element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/string_efficiency_spec.spl:258:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins two elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
