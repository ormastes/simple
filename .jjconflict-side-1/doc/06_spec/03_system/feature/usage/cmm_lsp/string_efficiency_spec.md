# String Operation Efficiency Specification

> Tests that string operations in the CMM LSP toolchain produce correct results after being rewritten from O(n²) character-by-character concatenation to O(n log n) segment-based approaches. Covers: escape_json, json_array, json_object, json_get_string, json_get_int, split_lines, lex_string_literal, to_upper_cmm, and join_parts.

<!-- sdn-diagram:id=string_efficiency_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_efficiency_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_efficiency_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_efficiency_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/cmm_lsp/string_efficiency_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts([])).to_equal("")
```

</details>

#### joins single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["hello"])).to_equal("hello")
```

</details>

#### joins two elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["hello", " world"])).to_equal("hello world")
```

</details>

#### joins three elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["a", "b", "c"])).to_equal("abc")
```

</details>

#### joins four elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["1", "2", "3", "4"])).to_equal("1234")
```

</details>

#### batch path (more than 4 elements)

#### joins 5 elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["a", "b", "c", "d", "e"])).to_equal("abcde")
```

</details>

#### joins 8 elements — exact batch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["1", "2", "3", "4", "5", "6", "7", "8"])).to_equal("12345678")
```

</details>

#### joins 9 elements — batch + remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["a", "b", "c", "d", "e", "f", "g", "h", "i"])).to_equal("abcdefghi")
```

</details>

#### joins 16 elements — two full batches

1. parts push
   - Expected: join_parts(parts) equals `xxxxxxxxxxxxxxxx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. parts push
   - Expected: result.len() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. parts push
   - Expected: result.len() equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["hello", " ", "world", "!", " ", "foo"])).to_equal("hello world! foo")
```

</details>

#### joins with empty segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(join_parts(["a", "", "b", "", "c"])).to_equal("abc")
```

</details>

### to_upper_cmm

#### fast path — already uppercase

#### returns uppercase string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("IF")).to_equal("IF")
```

</details>

#### returns uppercase keyword unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("WHILE")).to_equal("WHILE")
```

</details>

#### returns numbers/symbols unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("123_ABC")).to_equal("123_ABC")
```

</details>

#### conversion cases

#### converts lowercase to uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("if")).to_equal("IF")
```

</details>

#### converts mixed case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("While")).to_equal("WHILE")
```

</details>

#### converts all lowercase keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("repeat")).to_equal("REPEAT")
```

</details>

#### converts long keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("globalon")).to_equal("GLOBALON")
```

</details>

#### converts single char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("a")).to_equal("A")
```

</details>

#### edge cases

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("")).to_equal("")
```

</details>

#### preserves underscores and digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_upper_cmm("my_var_123")).to_equal("MY_VAR_123")
```

</details>

#### large input — would be slow with O(n²)

#### converts 200 lowercase chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("hello world")).to_equal("hello world")
```

</details>

#### returns empty string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("")).to_equal("")
```

</details>

#### returns alphanumeric unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("abc123XYZ")).to_equal("abc123XYZ")
```

</details>

#### escaping individual special characters

#### escapes backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("a\\b")).to_equal("a\\\\b")
```

</details>

#### escapes double quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "say \"hello\""
val expected = "say \\\"hello\\\""
expect(escape_json(input)).to_equal(expected)
```

</details>

#### escapes newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("line1\nline2")).to_equal("line1\\nline2")
```

</details>

#### escapes carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("line1\rline2")).to_equal("line1\\rline2")
```

</details>

#### escapes tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("col1\tcol2")).to_equal("col1\\tcol2")
```

</details>

#### multiple special characters

#### escapes string with multiple specials

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("a\nb\\c\"d")).to_equal("a\\nb\\\\c\\\"d")
```

</details>

#### escapes only-specials string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("\n\t\\")).to_equal("\\n\\t\\\\")
```

</details>

#### special at boundaries

#### escapes special at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("\nhello")).to_equal("\\nhello")
```

</details>

#### escapes special at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("hello\n")).to_equal("hello\\n")
```

</details>

#### escapes consecutive specials

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("\n\n\n")).to_equal("\\n\\n\\n")
```

</details>

#### large input — would be slow with O(n²)

#### escapes 500 chars with scattered specials

1. parts push
2. parts push
   - Expected: result.len() equals `510`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array([])).to_equal("[]")
```

</details>

#### builds single-element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array(["1"])).to_equal("[1]")
```

</details>

#### builds two-element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array(["1", "2"])).to_equal("[1,2]")
```

</details>

#### builds multi-element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_array(["1", "2", "3", "4"])).to_equal("[1,2,3,4]")
```

</details>

#### with string values

#### builds array of JSON strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [json_string("a"), json_string("b")]
expect(json_array(items)).to_equal("[\"a\",\"b\"]")
```

</details>

#### large array — would be slow with O(n²)

#### builds array with 100 elements

1. items push
   - Expected: result[0:1] equals `[`
   - Expected: result[result.len() - 1:result.len()] equals `]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(json_object([])).to_equal("{}")
```

</details>

#### builds single-pair object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = [JsonPair(key: "a", value: "1")]
expect(json_object(pairs)).to_equal("{\"a\":1}")
```

</details>

#### builds multi-pair object

1. JsonPair
2. JsonPair
   - Expected: json_object(pairs) equals `{"x":1,"y":2}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = [
    JsonPair(key: "x", value: "1"),
    JsonPair(key: "y", value: "2")
]
expect(json_object(pairs)).to_equal("{\"x\":1,\"y\":2}")
```

</details>

#### with string values

#### builds object with string values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = [JsonPair(key: "name", value: json_string("test"))]
expect(json_object(pairs)).to_equal("{\"name\":\"test\"}")
```

</details>

#### large object — would be slow with O(n²)

#### builds object with 50 pairs

1. pairs push
   - Expected: result[0:1] equals `{`
   - Expected: result[result.len() - 1:result.len()] equals `}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_lines("")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("")
```

</details>

#### splits single line without newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_lines("hello")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("hello")
```

</details>

#### splits two lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_lines("line1\nline2")
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("line1")
expect(result[1]).to_equal("line2")
```

</details>

#### splits three lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_lines("a\nb\nc")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("b")
expect(result[2]).to_equal("c")
```

</details>

#### trailing newline

#### splits with trailing newline — produces empty last line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_lines("hello\n")
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("hello")
expect(result[1]).to_equal("")
```

</details>

#### empty lines

#### handles consecutive newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_lines("a\n\nb")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("")
expect(result[2]).to_equal("b")
```

</details>

#### handles only newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_lines("\n\n")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("")
expect(result[1]).to_equal("")
expect(result[2]).to_equal("")
```

</details>

#### CMM-like content

#### splits typical CMM script

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. parts push
   - Expected: result.len() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
