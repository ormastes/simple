# MCP Protocol Runtime

> Exercise initialize, tools/list, and an unknown tools/call request through the

<!-- sdn-diagram:id=mcp_stdio_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_stdio_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_stdio_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_stdio_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Protocol Runtime

Exercise initialize, tools/list, and an unknown tools/call request through the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Source | `test/02_integration/app/mcp_stdio_integration_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirements

**Requirements:** N/A

- The server accepts Content-Length framing and JSONL transport.
- Initialize and tools/list return valid full-server responses.
- Unknown tools return tool-level errors rather than JSON-RPC failures.

## Plan

Exercise initialize, tools/list, and an unknown tools/call request through the
installed wrapper with the full tool set enabled.

## Design

The spec writes protocol input to a temporary file and drives the production
stdio wrapper through a shell pipe.

## Research

N/A

## Scenarios

### MCP Protocol Runtime

#### generates a correlated core wrapper from tracked setup source

1. Extract the generated wrapper directly from tracked `scripts/setup/setup.shs`.
   - Expected: numeric and string IDs remain correlated and nested `params.id` values are ignored.

#### preserves numeric and string request ids in the production core wrapper

1. Send numeric initialize ID `17` through the default wrapper.
   - Expected: the response contains numeric ID `17`, not `null`.
2. Send string tools/list ID `request-alpha` through the default wrapper.
   - Expected: the response contains string ID `request-alpha`, not `null`.

#### handles initialize, tools/list, and unknown-tool MCP startup flows

1. Initialize the full MCP server.
   - Expected: protocol version `2025-06-18`, server `simple-mcp-full`, and no JSON-RPC error.
2. List tools over Content-Length framing.
   - Expected: valid frames containing tool schemas.
3. List tools over JSONL framing.
   - Expected: the full tool set includes `debug_create_session`.
4. Return a tool-level error for an unknown tool.
   - Expected: `isError` is true and the response contains `Unknown tool` without a JSON-RPC error.

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
