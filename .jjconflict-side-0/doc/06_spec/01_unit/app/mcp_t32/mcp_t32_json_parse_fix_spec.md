# Mcp T32 Json Parse Fix Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_json_parse_fix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_json_parse_fix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_json_parse_fix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_json_parse_fix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Json Parse Fix Specification

## Scenarios

### Bug 2 - t32_find_substring

#### finds needle at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_find_substring("hello world", "hello")
expect(result).to_equal(0)
```

</details>

#### finds needle in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_find_substring("hello world", "world")
expect(result).to_equal(6)
```

</details>

#### returns -1 when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_find_substring("hello world", "xyz")
expect(result).to_equal(-1)
```

</details>

#### returns 0 for empty needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_find_substring("hello", "")
expect(result).to_equal(0)
```

</details>

#### handles needle longer than haystack

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_find_substring("hi", "hello world")
expect(result).to_equal(-1)
```

</details>

#### finds JSON key pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_find_substring("{\"method\":\"initialize\"}", "\"method\"")
expect(result).to_equal(1)
```

</details>

#### returns -1 for empty haystack with non-empty needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_find_substring("", "abc")
expect(result).to_equal(-1)
```

</details>

#### returns 0 for both empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_find_substring("", "")
expect(result).to_equal(0)
```

</details>

### Bug 3 - t32_json_string_after_key

#### compact JSON (no spaces)

#### extracts string value from compact JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":\"value\"}"
val result = t32_json_string_after_key(json, "key")
expect(result).to_equal("value")
```

</details>

#### extracts from multi-field compact JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"a\":\"1\",\"b\":\"2\"}"
val result_a = t32_json_string_after_key(json, "a")
val result_b = t32_json_string_after_key(json, "b")
expect(result_a).to_equal("1")
expect(result_b).to_equal("2")
```

</details>

#### space after colon

#### extracts string value with space after colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\": \"value\"}"
val result = t32_json_string_after_key(json, "key")
expect(result).to_equal("value")
```

</details>

#### extracts from multi-field JSON with spaces after colons

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\": \"initialize\", \"id\": \"req-1\"}"
val result = t32_json_string_after_key(json, "method")
expect(result).to_equal("initialize")
```

</details>

#### space before and after colon

#### extracts string value with spaces around colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\" : \"value\"}"
val result = t32_json_string_after_key(json, "key")
expect(result).to_equal("value")
```

</details>

#### escaped strings

#### handles escaped quotes in value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":\"val\\\"ue\"}"
val result = t32_json_string_after_key(json, "key")
expect(result).to_equal("val\"ue")
```

</details>

#### handles newlines in value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":\"line1\\nline2\"}"
val result = t32_json_string_after_key(json, "key")
expect(result).to_equal("line1\nline2")
```

</details>

#### handles backslash in value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":\"path\\\\dir\"}"
val result = t32_json_string_after_key(json, "key")
expect(result).to_equal("path\\dir")
```

</details>

#### edge cases

#### returns empty string for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"a\":\"1\"}"
val result = t32_json_string_after_key(json, "nonexistent")
expect(result).to_equal("")
```

</details>

#### returns empty string for non-string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":42}"
val result = t32_json_string_after_key(json, "key")
expect(result).to_equal("")
```

</details>

### Bug 3 - t32_request_raw_field

#### objects

#### extracts nested object with compact colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":{\"a\":1}}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("{\"a\":1}")
```

</details>

#### extracts nested object with space-colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\" : {\"a\":1}}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("{\"a\":1}")
```

</details>

#### arrays

#### extracts array with compact colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":[1,2,3]}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("[1,2,3]")
```

</details>

#### extracts array with space-colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\" : [1,2,3]}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("[1,2,3]")
```

</details>

#### scalars

#### extracts number with compact colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":42}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("42")
```

</details>

#### extracts number with space-colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\" : 42}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("42")
```

</details>

#### extracts boolean true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":true}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("true")
```

</details>

#### extracts boolean false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":false}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("false")
```

</details>

#### extracts null

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":null}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("null")
```

</details>

#### missing

#### returns null for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"a\":1}"
val result = t32_request_raw_field(json, "nonexistent")
expect(result).to_equal("null")
```

</details>

#### strings

#### extracts quoted string raw

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"key\":\"hello\"}"
val result = t32_request_raw_field(json, "key")
expect(result).to_equal("\"hello\"")
```

</details>

### Bug 4 - t32_request_id_text

#### extracts numeric id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"id\":1,\"method\":\"initialize\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("1")
```

</details>

#### extracts string id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"id\":\"req-1\",\"method\":\"test\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("\"req-1\"")
```

</details>

#### extracts id with space after colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"id\": 1, \"method\": \"test\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("1")
```

</details>

#### extracts id with spaces around colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"id\" : 1, \"method\" : \"test\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("1")
```

</details>

#### returns null for missing id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\":\"notifications/initialized\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("null")
```

</details>

#### extracts id when not first field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"test\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("42")
```

</details>

#### handles id in presence of session_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"params\":{\"arguments\":{\"session_id\":\"x\"}},\"id\":5}"
val result = t32_request_id_text(json)
expect(result).to_equal("5")
```

</details>

#### extracts null id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"id\":null,\"method\":\"test\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("null")
```

</details>

#### extracts string id with space after colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"id\": \"req-42\", \"method\": \"test\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("\"req-42\"")
```

</details>

#### extracts large numeric id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"jsonrpc\":\"2.0\",\"id\":999999,\"method\":\"initialize\"}"
val result = t32_request_id_text(json)
expect(result).to_equal("999999")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_json_parse_fix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bug 2 - t32_find_substring
- Bug 3 - t32_json_string_after_key
- Bug 3 - t32_request_raw_field
- Bug 4 - t32_request_id_text

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
