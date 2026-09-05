# Mcp Debug Log Tree Stdio Specification

> <details>

<!-- sdn-diagram:id=mcp_debug_log_tree_stdio_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_debug_log_tree_stdio_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_debug_log_tree_stdio_spec -> std
mcp_debug_log_tree_stdio_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_debug_log_tree_stdio_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Debug Log Tree Stdio Specification

## Scenarios

### MCP Stdio Debug Log Tree

#### returns JSON tree and keeps session alive

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = init_request() + initialized_notification() + tools_call_request("2", "debug_log_enable", "{\"pattern\":\"*\"}") + tools_call_request("3", "debug_log_tree", "{\"format\":\"json\",\"mode\":\"human\"}") + shutdown_request("4")
val output = send_mcp(input)

expect(output.contains("\"id\":\"3\"")).to_equal(true)
expect(output.contains("\"format\":\"json\"")).to_equal(true)
expect(output.contains("\"mode\":\"human\"")).to_equal(true)
expect(output.contains("\"tree\":[")).to_equal(true)
expect(output.contains("\"id\":\"4\"")).to_equal(true)
```

</details>

#### returns compact LLM text mode and keeps session alive

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = init_request() + initialized_notification() + tools_call_request("2", "debug_log_enable", "{\"pattern\":\"*\"}") + tools_call_request("3", "debug_log_tree", "{\"format\":\"text\",\"mode\":\"llm\"}") + shutdown_request("4")
val output = send_mcp(input)

expect(output.contains("\"id\":\"3\"")).to_equal(true)
expect(output.contains("\"format\":\"text\"")).to_equal(true)
expect(output.contains("\"mode\":\"llm\"")).to_equal(true)
expect(output.contains("log_tree mode=llm")).to_equal(true)
expect(output.contains("\"id\":\"4\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/mcp_debug_log_tree_stdio_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Stdio Debug Log Tree

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
