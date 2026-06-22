# Mcp T32 Json Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_json_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_json_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_json_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_json_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Json Specification

## Scenarios

### T32 MCP JSON Helpers

#### wraps string in quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tjs("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### escapes quotes in string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tjs("say \"hi\"")
expect(result).to_contain("\\\"")
```

</details>

#### escapes newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tjs("line1\nline2")
expect(result).to_contain("\\n")
```

</details>

#### creates key-value pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tjp("name", tjs("test"))
expect(result).to_start_with("\"name\"")
expect(result).to_contain("\"test\"")
```

</details>

#### creates JSON object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tjo1(tjp("key", tjs("val")))
expect(result).to_start_with("{")
expect(result).to_end_with("}")
```

</details>

#### parses initialize method with shared extractor behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{},\"clientInfo\":{\"name\":\"probe\",\"version\":\"1.0\"}}}"
expect(lsp_extract_field(json, "method")).to_equal("initialize")
```

</details>

#### parses numeric id with shared extractor behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"initialize\"}"
expect(lsp_extract_id(json)).to_equal("42")
```

</details>

#### parses nested params fields with shared extractor behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\":\"tools/call\",\"params\":{\"name\":\"cmm_parse\",\"arguments\":{\"source\":\"do main\"}}}"
expect(lsp_extract_nested(json, "name")).to_equal("cmm_parse")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_json_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP JSON Helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
