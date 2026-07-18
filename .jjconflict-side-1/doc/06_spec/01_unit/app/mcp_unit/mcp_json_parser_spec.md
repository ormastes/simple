# Mcp Json Parser Specification

> <details>

<!-- sdn-diagram:id=mcp_json_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_json_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_json_parser_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_json_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Json Parser Specification

## Scenarios

### JSON String Extraction

#### when extracting simple string values

#### extracts method from JSON-RPC request

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo3(jp("jsonrpc", js("2.0")), jp("id", js("1")), jp("method", js("initialize")))
val method = extract_json_string(json, "method")
expect(method).to_equal("initialize")
```

</details>

#### extracts jsonrpc version

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("jsonrpc", js("2.0")), jp("id", js("1")))
val version = extract_json_string(json, "jsonrpc")
expect(version).to_equal("2.0")
```

</details>

#### returns empty string for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("jsonrpc", js("2.0")))
val missing = extract_json_string(json, "nonexistent")
expect(missing).to_equal("")
```

</details>

#### when handling special characters

#### handles strings with slashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("path", js("src/app/mcp/main.spl")))
val path = extract_json_string(json, "path")
expect(path).to_contain("/")
expect(path).to_equal("src/app/mcp/main.spl")
```

</details>

#### handles empty string values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("empty", js("")))
val empty = extract_json_string(json, "empty")
expect(empty).to_equal("")
```

</details>

### JSON Value Extraction

#### when extracting numeric values

#### extracts numeric ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("jsonrpc", js("2.0")), jp("id", "42"))
val id = extract_json_value(json, "id")
expect(id).to_equal("42")
```

</details>

#### extracts boolean-like values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("isError", "true"))
val value = extract_json_value(json, "isError")
expect(value).to_equal("true")
```

</details>

#### when extracting object values

#### stops at comma delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("id", "1"), jp("method", js("test")))
val id = extract_json_value(json, "id")
expect(id).to_equal("1")
```

</details>

#### returns null for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("method", js("test")))
val missing = extract_json_value(json, "nonexistent")
expect(missing).to_equal("null")
```

</details>

### Nested JSON Extraction

#### when accessing nested objects

#### extracts nested string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = jo1(jp("name", js("read_code")))
val json = jo1(jp("params", inner))
val name = extract_nested_string(json, "params", "name")
expect(name).to_equal("read_code")
```

</details>

#### extracts nested path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = jo1(jp("uri", js("file:///path/to/file.spl")))
val json = jo1(jp("params", inner))
val uri = extract_nested_string(json, "params", "uri")
expect(uri).to_contain("file://")
```

</details>

#### returns empty for missing nested key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("params", LB() + RB()))
val missing = extract_nested_string(json, "params", "nonexistent")
expect(missing).to_equal("")
```

</details>

### JSON Parser Edge Cases

#### when handling escape characters

#### escapes newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("line1{NL}line2")
expect(escaped.contains(NL)).to_equal(false)
```

</details>

#### escapes tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("col1\tcol2")
expect(escaped.contains("\t")).to_equal(false)
```

</details>

#### preserves normal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("hello world")
expect(escaped).to_equal("hello world")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("")
expect(escaped).to_equal("")
```

</details>

#### when building search patterns

#### builds quoted key pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "method"
val pattern = Q() + key + Q() + ":"
expect(pattern.contains("method")).to_equal(true)
expect(pattern.contains(":")).to_equal(true)
```

</details>

### JSON Builder Round-Trip

#### when building and extracting

#### round-trips string values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("name", js("Alice")))
val extracted = extract_json_string(json, "name")
expect(extracted).to_equal("Alice")
```

</details>

#### round-trips nested values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = jo2(jp("file", js("test.spl")), jp("line", "42"))
val json = jo1(jp("params", inner))
val file = extract_nested_string(json, "params", "file")
expect(file).to_equal("test.spl")
```

</details>

#### round-trips multiple fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo3(jp("a", js("1")), jp("b", js("2")), jp("c", js("3")))
expect(extract_json_string(json, "a")).to_equal("1")
expect(extract_json_string(json, "b")).to_equal("2")
expect(extract_json_string(json, "c")).to_equal("3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_json_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JSON String Extraction
- JSON Value Extraction
- Nested JSON Extraction
- JSON Parser Edge Cases
- JSON Builder Round-Trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
