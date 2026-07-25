# Simple Lsp Mcp Stdio Specification

> <details>

<!-- sdn-diagram:id=simple_lsp_mcp_stdio_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_lsp_mcp_stdio_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_lsp_mcp_stdio_spec -> std
simple_lsp_mcp_stdio_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_lsp_mcp_stdio_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Lsp Mcp Stdio Specification

## Scenarios

### Simple LSP MCP stdio

#### mirrors Claude-style JSONL requests with JSONL responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = lsp_mcp_jsonl(lsp_init_body("1")) + lsp_mcp_jsonl(lsp_tools_body("2"))
val output = send_lsp_mcp(input)
expect(output.starts_with("{\"jsonrpc\":\"2.0\"")).to_equal(true)
expect(output.contains("Content-Length:")).to_equal(false)
expect(output.contains("\"serverInfo\":{\"name\":\"simple-lsp-mcp\"")).to_equal(true)
expect(output.contains("\"name\":\"lsp_definition\"")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)
```

</details>

#### keeps Content-Length framing for framed MCP clients

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = lsp_mcp_msg(lsp_init_body("1")) + lsp_mcp_msg(lsp_tools_body("2"))
val output = send_lsp_mcp(input)
expect(output.starts_with("Content-Length: ")).to_equal(true)
expect(output.contains("\"serverInfo\":{\"name\":\"simple-lsp-mcp\"")).to_equal(true)
expect(output.contains("\"name\":\"lsp_definition\"")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/simple_lsp_mcp_stdio_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple LSP MCP stdio

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
