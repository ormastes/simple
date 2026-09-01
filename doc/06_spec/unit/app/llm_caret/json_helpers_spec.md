# json_helpers_spec

> Purpose: Prove that JSON Escaping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# json_helpers_spec

Purpose: Prove that JSON Escaping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_caret/json_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that JSON Escaping.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### JSON Escaping

#### escapes plain text unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- escapes plain text unchanged
- Verify: escapes plain text unchanged
   - Expected: escape_json_text("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes plain text unchanged")
step("Verify: escapes plain text unchanged")
# @req: REQ-APP-LLM-CARET-001
expect(escape_json_text("hello")).to_equal("hello")
```

</details>

#### escapes double quotes

- escapes double quotes
- Verify: escapes double quotes
   - Expected: escape_json_text("say \"hi\"") equals `say \\"hi\\"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes double quotes")
step("Verify: escapes double quotes")
expect(escape_json_text("say \"hi\"")).to_equal("say \\\"hi\\\"")
```

</details>

#### escapes backslashes

- escapes backslashes
- Verify: escapes backslashes
   - Expected: escape_json_text("a\\b") equals `a\\\\b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes backslashes")
step("Verify: escapes backslashes")
expect(escape_json_text("a\\b")).to_equal("a\\\\b")
```

</details>

#### escapes newlines

- escapes newlines
- Verify: escapes newlines
   - Expected: escape_json_text("line1\nline2") equals `line1\\nline2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes newlines")
step("Verify: escapes newlines")
expect(escape_json_text("line1\nline2")).to_equal("line1\\nline2")
```

</details>

#### escapes tabs

- escapes tabs
- Verify: escapes tabs
   - Expected: escape_json_text("a\tb") equals `a\\tb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes tabs")
step("Verify: escapes tabs")
expect(escape_json_text("a\tb")).to_equal("a\\tb")
```

</details>

### JSON Building

#### builds single-pair object

- builds single-pair object
- Verify: builds single-pair object


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds single-pair object")
step("Verify: builds single-pair object")
val result = jo1(_pair("key", _str("val")))
expect(result).to_start_with(_lb())
expect(result).to_end_with(_rb())
```

</details>

#### builds two-pair object

- builds two-pair object
- Verify: builds two-pair object


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds two-pair object")
step("Verify: builds two-pair object")
val result = jo2(_pair("a", _str("1")), _pair("b", _str("2")))
expect(result).to_contain(",")
expect(result).to_contain("\"a\"")
expect(result).to_contain("\"b\"")
```

</details>

#### builds three-pair object

- builds three-pair object
- Verify: builds three-pair object


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds three-pair object")
step("Verify: builds three-pair object")
val result = jo3(_pair("a", _str("1")), _pair("b", _str("2")), _pair("c", _str("3")))
expect(result).to_start_with(_lb())
expect(result).to_end_with(_rb())
expect(result).to_contain("\"c\"")
```

</details>

#### builds four-pair object

- builds four-pair object
- Verify: builds four-pair object
   - Expected: extract_json_value(result, "d") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds four-pair object")
step("Verify: builds four-pair object")
val result = jo4(_pair("a", "1"), _pair("b", "2"), _pair("c", "3"), _pair("d", "4"))
expect(extract_json_value(result, "d")).to_equal("4")
```

</details>

#### builds five-pair object

- builds five-pair object
- Verify: builds five-pair object
   - Expected: extract_json_value(result, "e") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds five-pair object")
step("Verify: builds five-pair object")
val result = jo5(_pair("a", "1"), _pair("b", "2"), _pair("c", "3"), _pair("d", "4"), _pair("e", "5"))
expect(extract_json_value(result, "e")).to_equal("5")
```

</details>

#### builds six-pair object

- builds six-pair object
- Verify: builds six-pair object
   - Expected: extract_json_value(result, "f") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds six-pair object")
step("Verify: builds six-pair object")
val result = jo6(_pair("a", "1"), _pair("b", "2"), _pair("c", "3"), _pair("d", "4"), _pair("e", "5"), _pair("f", "6"))
expect(extract_json_value(result, "f")).to_equal("6")
```

</details>

#### builds array from items

- builds array from items
- Verify: builds array from items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds array from items")
step("Verify: builds array from items")
val result = ja([_str("a"), _str("b"), _str("c")])
expect(result).to_start_with("[")
expect(result).to_end_with("]")
expect(result).to_contain("\"a\"")
expect(result).to_contain(",")
```

</details>

#### builds empty array

- builds empty array
- Verify: builds empty array
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds empty array")
step("Verify: builds empty array")
val result = ja([])
expect(result).to_equal("[]")
```

</details>

### JSON Substring Search

#### finds a needle at the start

- finds a needle at the start
- Verify: finds a needle at the start
   - Expected: json_find("abcdef", "abc") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a needle at the start")
step("Verify: finds a needle at the start")
expect(json_find("abcdef", "abc")).to_equal(0)
```

</details>

#### finds a needle in the middle

- finds a needle in the middle
- Verify: finds a needle in the middle
   - Expected: json_find("abcdef", "cd") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a needle in the middle")
step("Verify: finds a needle in the middle")
expect(json_find("abcdef", "cd")).to_equal(2)
```

</details>

#### finds a needle at index 3

- finds a needle at index 3
- Verify: finds a needle at index 3
   - Expected: json_find("abcdef", "d") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a needle at index 3")
step("Verify: finds a needle at index 3")
# Index 3 is the exact value the seed's Option<i64> tag-box collides
# with the nil sentinel on; json_find exists to avoid that.
expect(json_find("abcdef", "d")).to_equal(3)
```

</details>

#### returns -1 when absent

- returns -1 when absent
- Verify: returns -1 when absent
   - Expected: json_find("abcdef", "xyz") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 when absent")
step("Verify: returns -1 when absent")
expect(json_find("abcdef", "xyz")).to_equal(-1)
```

</details>

#### returns -1 when the needle is longer than the haystack

- returns -1 when the needle is longer than the haystack
- Verify: returns -1 when the needle is longer than the haystack
   - Expected: json_find("ab", "abcdef") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 when the needle is longer than the haystack")
step("Verify: returns -1 when the needle is longer than the haystack")
expect(json_find("ab", "abcdef")).to_equal(-1)
```

</details>

#### returns 0 for an empty needle

- returns 0 for an empty needle
- Verify: returns 0 for an empty needle
   - Expected: json_find("abcdef", "") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for an empty needle")
step("Verify: returns 0 for an empty needle")
expect(json_find("abcdef", "")).to_equal(0)
```

</details>

### JSON Integer Parsing

#### parses a positive integer

- parses a positive integer
- Verify: parses a positive integer
   - Expected: json_parse_int("42") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a positive integer")
step("Verify: parses a positive integer")
expect(json_parse_int("42")).to_equal(42)
```

</details>

#### parses zero

- parses zero
- Verify: parses zero
   - Expected: json_parse_int("0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses zero")
step("Verify: parses zero")
expect(json_parse_int("0")).to_equal(0)
```

</details>

#### parses a negative integer

- parses a negative integer
- Verify: parses a negative integer
   - Expected: json_parse_int("-17") equals `-17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a negative integer")
step("Verify: parses a negative integer")
expect(json_parse_int("-17")).to_equal(-17)
```

</details>

#### parses a multi-digit integer

- parses a multi-digit integer
- Verify: parses a multi-digit integer
   - Expected: json_parse_int("12345") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a multi-digit integer")
step("Verify: parses a multi-digit integer")
expect(json_parse_int("12345")).to_equal(12345)
```

</details>

#### PINS DEFECT: skips embedded non-digits instead of rejecting

- PINS DEFECT: skips embedded non-digits instead of rejecting
- Verify: PINS DEFECT: skips embedded non-digits instead of rejecting
   - Expected: json_parse_int("1a2") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PINS DEFECT: skips embedded non-digits instead of rejecting")
step("Verify: PINS DEFECT: skips embedded non-digits instead of rejecting")
expect(json_parse_int("1a2")).to_equal(12)
```

</details>

#### PINS DEFECT: returns 0 for a wholly non-numeric string

- PINS DEFECT: returns 0 for a wholly non-numeric string
- Verify: PINS DEFECT: returns 0 for a wholly non-numeric string
   - Expected: json_parse_int("abc") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PINS DEFECT: returns 0 for a wholly non-numeric string")
step("Verify: PINS DEFECT: returns 0 for a wholly non-numeric string")
expect(json_parse_int("abc")).to_equal(0)
```

</details>

### JSON Parsing

#### extracts string value

- extracts string value
- Verify: extracts string value
   - Expected: result equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts string value")
step("Verify: extracts string value")
val json = jo1(_pair("name", _str("Alice")))
val result = extract_json_string(json, "name")
expect(result).to_equal("Alice")
```

</details>

#### returns empty for missing key

- returns empty for missing key
- Verify: returns empty for missing key
   - Expected: extract_json_string(json, "missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for missing key")
step("Verify: returns empty for missing key")
val json = jo1(_pair("name", _str("Alice")))
expect(extract_json_string(json, "missing")).to_equal("")
```

</details>

#### extracts a string value containing an escaped quote

- extracts a string value containing an escaped quote
- Verify: extracts a string value containing an escaped quote
   - Expected: extract_json_string(json, "name") equals `say \\"hi\\"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts a string value containing an escaped quote")
step("Verify: extracts a string value containing an escaped quote")
# The shipped extractor tracks backslash escapes; this is the behaviour
# that std.mcp.helpers' same-named function does NOT have.
val json = jo1(_pair("name", _str("say \"hi\"")))
expect(extract_json_string(json, "name")).to_equal("say \\\"hi\\\"")
```

</details>

#### extracts a string whose escaped quote is the last char (backslash before closing quote)

- extracts a string whose escaped quote is the last char (backslash before closing quote)
- Verify: escaped quote directly before the closing quote
   - Expected: extract_json_string(json, "name") equals `end\\"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts a string whose escaped quote is the last char (backslash before closing quote)")
step("Verify: escaped quote directly before the closing quote")
val json = jo1(_pair("name", _str("end\"")))
expect(extract_json_string(json, "name")).to_equal("end\\\"")
```

</details>

#### extracts a string ending in an escaped backslash

- extracts a string ending in an escaped backslash
- Verify: backslash at end resets escape state before the closing quote
   - Expected: extract_json_string(json, "name") equals `dir\\\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts a string ending in an escaped backslash")
step("Verify: backslash at end resets escape state before the closing quote")
val json = jo1(_pair("name", _str("dir\\")))
expect(extract_json_string(json, "name")).to_equal("dir\\\\")
```

</details>

#### extracts a string containing a double backslash

- extracts a string containing a double backslash
- Verify: double backslash in the middle is kept verbatim
   - Expected: extract_json_string(json, "name") equals `a\\\\b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts a string containing a double backslash")
step("Verify: double backslash in the middle is kept verbatim")
val json = jo1(_pair("name", _str("a\\b")))
expect(extract_json_string(json, "name")).to_equal("a\\\\b")
```

</details>

#### extracts a string containing a unicode escape

- extracts a string containing a unicode escape
- Verify: \\u escape sequence is kept verbatim
   - Expected: extract_json_string(json, "name") equals `caf\\u00e9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts a string containing a unicode escape")
step("Verify: \\u escape sequence is kept verbatim")
val json = jo1(_pair("name", "\"caf\\u00e9\""))
expect(extract_json_string(json, "name")).to_equal("caf\\u00e9")
```

</details>

#### extracts numeric value

- extracts numeric value
- Verify: extracts numeric value
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts numeric value")
step("Verify: extracts numeric value")
val json = jo2(_pair("count", "42"), _pair("name", _str("test")))
val result = extract_json_value(json, "count")
expect(result).to_equal("42")
```

</details>

#### returns null for a missing raw value

- returns null for a missing raw value
- Verify: returns null for a missing raw value
   - Expected: extract_json_value(json, "missing") equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns null for a missing raw value")
step("Verify: returns null for a missing raw value")
val json = jo1(_pair("count", "42"))
expect(extract_json_value(json, "missing")).to_equal("null")
```

</details>

#### extracts integer value

- extracts integer value
- Verify: extracts integer value
   - Expected: extract_json_int(json, "count") equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts integer value")
step("Verify: extracts integer value")
val json = jo1(_pair("count", "99"))
expect(extract_json_int(json, "count")).to_equal(99)
```

</details>

#### returns 0 for missing int

- returns 0 for missing int
- Verify: returns 0 for missing int
   - Expected: extract_json_int(json, "missing") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for missing int")
step("Verify: returns 0 for missing int")
val json = jo1(_pair("name", _str("test")))
expect(extract_json_int(json, "missing")).to_equal(0)
```

</details>

#### extracts a negative integer value

- extracts a negative integer value
- Verify: extracts a negative integer value
   - Expected: extract_json_int(json, "delta") equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts a negative integer value")
step("Verify: extracts a negative integer value")
val json = jo1(_pair("delta", "-5"))
expect(extract_json_int(json, "delta")).to_equal(-5)
```

</details>

#### extracts boolean value

- extracts boolean value
- Verify: extracts boolean value
   - Expected: extract_json_bool(json, "active") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts boolean value")
step("Verify: extracts boolean value")
val json = jo1(_pair("active", "true"))
expect(extract_json_bool(json, "active")).to_equal(true)
```

</details>

#### extracts false boolean

- extracts false boolean
- Verify: extracts false boolean
   - Expected: extract_json_bool(json, "active") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts false boolean")
step("Verify: extracts false boolean")
val json = jo1(_pair("active", "false"))
expect(extract_json_bool(json, "active")).to_equal(false)
```

</details>

#### extracts nested string

- extracts nested string
- Verify: extracts nested string
   - Expected: extract_nested_string(json, "user", "name") equals `Bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts nested string")
step("Verify: extracts nested string")
val inner = jo1(_pair("name", _str("Bob")))
val json = jo1(_pair("user", inner))
expect(extract_nested_string(json, "user", "name")).to_equal("Bob")
```

</details>

#### returns empty for a missing outer key in a nested lookup

- returns empty for a missing outer key in a nested lookup
- Verify: returns empty for a missing outer key in a nested lookup
   - Expected: extract_nested_string(json, "missing", "name") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for a missing outer key in a nested lookup")
step("Verify: returns empty for a missing outer key in a nested lookup")
val inner = jo1(_pair("name", _str("Bob")))
val json = jo1(_pair("user", inner))
expect(extract_nested_string(json, "missing", "name")).to_equal("")
```

</details>

### Message JSON

#### builds single message

- builds single message
- Verify: builds single message


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds single message")
step("Verify: builds single message")
val result = build_message_json("user", "Hello")
expect(result).to_contain("\"role\"")
expect(result).to_contain("\"user\"")
expect(result).to_contain("\"content\"")
expect(result).to_contain("\"Hello\"")
```

</details>

#### round-trips a message through the extractors

- round-trips a message through the extractors
- Verify: round-trips a message through the extractors
   - Expected: extract_json_string(result, "role") equals `user`
   - Expected: extract_json_string(result, "content") equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a message through the extractors")
step("Verify: round-trips a message through the extractors")
val result = build_message_json("user", "Hello")
expect(extract_json_string(result, "role")).to_equal("user")
expect(extract_json_string(result, "content")).to_equal("Hello")
```

</details>

#### builds messages array

- builds messages array
- Verify: builds messages array


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds messages array")
step("Verify: builds messages array")
val result = build_messages_json(["user", "assistant"], ["Hi", "Hello!"])
expect(result).to_start_with("[")
expect(result).to_end_with("]")
expect(result).to_contain("\"user\"")
expect(result).to_contain("\"assistant\"")
```

</details>

#### pads missing content with an empty string

- pads missing content with an empty string
- Verify: pads missing content with an empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads missing content with an empty string")
step("Verify: pads missing content with an empty string")
val result = build_messages_json(["user", "assistant"], ["Hi"])
expect(result).to_contain("\"assistant\"")
expect(result).to_contain("\"\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-LLM-CARET-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `40e0027aa688776fb4d1b0ca151ada8d0aa3287fad9040706208a18d151be4a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40e0027aa688776fb4d1b0ca151ada8d0aa3287fad9040706208a18d151be4a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40e0027aa688776fb4d1b0ca151ada8d0aa3287fad9040706208a18d151be4a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/llm_caret/json_helpers_spec.spl
mirror: doc/06_spec/unit/app/llm_caret/json_helpers_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_caret/json_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_caret/json_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_caret/json_helpers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/llm_caret/json_helpers_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes plain text unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/json_helpers_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes double quotes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_caret/json_helpers_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes backslashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
