# MCP CLI Passthrough Diagnostics Regression

> Verifies that diagnostic MCP tools which are classified as CLI passthrough still

<!-- sdn-diagram:id=mcp_cli_passthrough_diag_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_cli_passthrough_diag_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_cli_passthrough_diag_spec -> std
mcp_cli_passthrough_diag_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_cli_passthrough_diag_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP CLI Passthrough Diagnostics Regression

Verifies that diagnostic MCP tools which are classified as CLI passthrough still

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/mcp_cli_passthrough_diag_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that diagnostic MCP tools which are classified as CLI passthrough still
return their intended MCP payloads instead of leaking unrelated `simple query`
usage errors from the host CLI surface.

## Scenarios

### MCP CLI passthrough diagnostics regression

#### simple_symbols returns symbol output instead of query usage error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = tool_call_request("sym-1", "simple_symbols", "{\"path\":\"test/system/mcp/fixtures/tiny_valid.spl\"}")
val output = send_mcp(init_request("init-1") + initialized_notification() + req)
expect(output.contains("\"id\":\"sym-1\"")).to_equal(true)
expect(output.contains("-- symbols in test/system/mcp/fixtures/tiny_valid.spl --")).to_equal(true)
expect(output.contains("fn add")).to_equal(true)
expect(output.contains("query requires --generated")).to_equal(false)
```

</details>

#### simple_diagnostics returns structured content instead of query usage error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = tool_call_request("diag-1", "simple_diagnostics", "{\"path\":\"test/system/mcp/fixtures/tiny_valid.spl\"}")
val output = send_mcp(init_request("init-2") + initialized_notification() + req)
expect(output.contains("\"id\":\"diag-1\"")).to_equal(true)
expect(output.contains("\"structuredContent\":{\"path\":\"test/system/mcp/fixtures/tiny_valid.spl\"")).to_equal(true)
expect(output.contains("\"diagnostics\":[")).to_equal(true)
expect(output.contains("query requires --generated")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
