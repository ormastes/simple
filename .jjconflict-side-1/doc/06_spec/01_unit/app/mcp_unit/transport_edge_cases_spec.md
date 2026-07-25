# Transport Edge Cases Specification

> <details>

<!-- sdn-diagram:id=transport_edge_cases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transport_edge_cases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transport_edge_cases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transport_edge_cases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transport Edge Cases Specification

## Scenarios

### MCP transport_edge_cases

#### maps transport-facing error categories to JSON-RPC codes

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = error_handler_source()

expect(src).to_contain("case ErrorCategory.ParseError: -32700")
expect(src).to_contain("case ErrorCategory.InvalidRequest: -32600")
expect(src).to_contain("case ErrorCategory.MethodNotFound: -32601")
expect(src).to_contain("case ErrorCategory.InvalidParams: -32602")
expect(src).to_contain("case ErrorCategory.InternalError: -32603")
```

</details>

#### bounds hostile transport payload dimensions

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = error_handler_source()

expect(src).to_contain("max_content_length: 1048576")
expect(src).to_contain("max_string_length: 65536")
expect(src).to_contain("max_uri_length: 2048")
expect(src).to_contain("max_tool_name_length: 256")
expect(src).to_contain("max_array_length: 1000")
expect(src).to_contain("Content length cannot be negative")
expect(src).to_contain("Array length cannot be negative")
```

</details>

#### rejects malformed URI schemes and tool names before dispatch

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = error_handler_source()

expect(src).to_contain("fn validate_uri(uri: text) -> McpError?:")
expect(src).to_contain("URI cannot be empty")
expect(src).to_contain("Invalid URI scheme")
expect(src).to_contain("fn validate_tool_name(name: text) -> McpError?:")
expect(src).to_contain("Tool name cannot be empty")
expect(src).to_contain("Tool name contains invalid character")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/transport_edge_cases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP transport_edge_cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
