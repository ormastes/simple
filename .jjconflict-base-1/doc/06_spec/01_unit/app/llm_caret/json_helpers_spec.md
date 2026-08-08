# Json Helpers Specification

> <details>

<!-- sdn-diagram:id=json_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=json_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

json_helpers_spec -> std
json_helpers_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=json_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Helpers Specification

## Scenarios

### JSON Escaping

#### escapes plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json_text("hello")).to_equal("hello")
```

</details>

#### escapes double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json_text("say \"hi\"")).to_equal("say \\\"hi\\\"")
```

</details>

#### escapes backslashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json_text("a\\b")).to_equal("a\\\\b")
```

</details>

#### escapes newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json_text("line1\nline2")).to_equal("line1\\nline2")
```

</details>

#### escapes tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json_text("a\tb")).to_equal("a\\tb")
```

</details>

### JSON Building

#### builds string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### builds key-value pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jp("name", js("Alice"))
expect(result).to_contain("\"name\"")
expect(result).to_contain("\"Alice\"")
```

</details>

#### builds single-pair object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo1(jp("key", js("val")))
expect(result).to_start_with(LB())
expect(result).to_end_with(RB())
```

</details>

#### builds two-pair object

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo2(jp("a", js("1")), jp("b", js("2")))
expect(result).to_contain(",")
expect(result).to_contain("\"a\"")
expect(result).to_contain("\"b\"")
```

</details>

#### builds array from items

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ja([js("a"), js("b"), js("c")])
expect(result).to_start_with("[")
expect(result).to_end_with("]")
expect(result).to_contain("\"a\"")
expect(result).to_contain(",")
```

</details>

#### builds empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ja([])
expect(result).to_equal("[]")
```

</details>

### JSON Parsing

#### extracts string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("name", js("Alice")))
val result = extract_json_string(json, "name")
expect(result).to_equal("Alice")
```

</details>

#### returns empty for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("name", js("Alice")))
expect(extract_json_string(json, "missing")).to_equal("")
```

</details>

#### extracts numeric value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("count", "42"), jp("name", js("test")))
val result = extract_json_value(json, "count")
expect(result).to_equal("42")
```

</details>

#### extracts integer value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("count", "99"))
expect(extract_json_int(json, "count")).to_equal(99)
```

</details>

#### returns 0 for missing int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("name", js("test")))
expect(extract_json_int(json, "missing")).to_equal(0)
```

</details>

#### extracts boolean value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("active", "true"))
expect(extract_json_bool(json, "active")).to_equal(true)
```

</details>

#### extracts false boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("active", "false"))
expect(extract_json_bool(json, "active")).to_equal(false)
```

</details>

#### extracts nested string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = jo1(jp("name", js("Bob")))
val json = jo1(jp("user", inner))
expect(extract_nested_string(json, "user", "name")).to_equal("Bob")
```

</details>

### Message JSON

#### builds single message

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = build_message_json("user", "Hello")
expect(result).to_contain("\"role\"")
expect(result).to_contain("\"user\"")
expect(result).to_contain("\"content\"")
expect(result).to_contain("\"Hello\"")
```

</details>

#### builds messages array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = build_messages_json(["user", "assistant"], ["Hi", "Hello!"])
expect(result).to_start_with("[")
expect(result).to_end_with("]")
expect(result).to_contain("\"user\"")
expect(result).to_contain("\"assistant\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/json_helpers_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JSON Escaping
- JSON Building
- JSON Parsing
- Message JSON

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
