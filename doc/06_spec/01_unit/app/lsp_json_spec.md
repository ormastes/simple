# Lsp Json Specification

> <details>

<!-- sdn-diagram:id=lsp_json_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_json_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_json_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_json_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Json Specification

## Scenarios

### LSP JSON helpers

### escape_json

#### escapes quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_json("hello \"world\"")
expect(result).to_contain("\\\"")
```

</details>

#### escapes newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_json("line1\nline2")
expect(result).to_contain("\\n")
```

</details>

#### passes through plain text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = escape_json("hello world")
expect(result).to_equal("hello world")
```

</details>

### extract_field

#### extracts string field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\":\"Alice\",\"age\":30}"
val result = extract_field(json, "name")
expect(result).to_equal("Alice")
```

</details>

#### extracts numeric field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\":\"Alice\",\"age\":30}"
val result = extract_field(json, "age")
expect(result).to_equal("30")
```

</details>

#### returns empty for missing field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\":\"Alice\"}"
val result = extract_field(json, "missing")
expect(result).to_equal("")
```

</details>

### extract_id

#### extracts numeric id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"initialize\"}"
val result = extract_id(json)
expect(result).to_equal("42")
```

</details>

#### extracts string id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"jsonrpc\":\"2.0\",\"id\":\"abc\",\"method\":\"test\"}"
val result = extract_id(json)
expect(result).to_equal("\"abc\"")
```

</details>

### extract_nested

#### extracts field from params

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\":\"hover\",\"params\":{\"textDocument\":{\"uri\":\"file:///test.spl\"},\"position\":{\"line\":5}}}"
val result = extract_nested(json, "line")
expect(result).to_equal("5")
```

</details>

### make_json_result

#### creates valid JSON-RPC response

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_json_result("1", "null")
expect(result).to_contain("jsonrpc")
expect(result).to_contain("2.0")
expect(result).to_contain("\"id\":1")
expect(result).to_contain("\"result\":null")
```

</details>

### JSON builders

#### js wraps in quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### jp creates key-value pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jp("name", js("Alice"))
expect(result).to_equal("\"name\":\"Alice\"")
```

</details>

#### jo1 wraps single property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo1(jp("x", "1"))
expect(result).to_equal("{\"x\":1}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp_json_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LSP JSON helpers
- escape_json
- extract_field
- extract_id
- extract_nested
- make_json_result
- JSON builders

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
