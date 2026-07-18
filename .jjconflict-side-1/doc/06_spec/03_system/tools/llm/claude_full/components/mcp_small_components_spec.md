# Claude Full MCP Small Components

> Modern SSpec coverage for local MCP menu, warning, reconnect, tool, and approval helpers.

<!-- sdn-diagram:id=mcp_small_components_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_small_components_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_small_components_spec -> std
mcp_small_components_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_small_components_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP Small Components

Modern SSpec coverage for local MCP menu, warning, reconnect, tool, and approval helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/mcp_small_components_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Modern SSpec coverage for local MCP menu, warning, reconnect, tool, and approval helpers.

## Scenarios

### Claude full MCP small component parity

#### should render agent and stdio menu decisions

- Render agent auth options
   - Expected: mcpAgentMenuOptions(agent)[0] equals `auth:Authenticate`
- Render stdio menu options
   - Expected: mcpStdioMenuOptions(stdio)[0] equals `tools:View tools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render agent auth options")
val agent = MCPAgentServerState.new("github", "http", "https://mcp.example", "", ["reviewer"], true, false, false, "", "")
expect(mcpAgentMenuOptions(agent)[0]).to_equal("auth:Authenticate")
expect(mcpAgentServerSummary(agent)).to_contain("github")

step("Render stdio menu options")
val stdio = MCPStdioServerState.new("fs", "connected", "node", ["server.js"], 2, 1, 0, false, false)
expect(mcpStdioMenuOptions(stdio)[0]).to_equal("tools:View tools")
expect(mcpStdioCapabilitiesSummary(stdio)).to_contain("tools=2")
```

</details>

#### should render diagnostics and reconnect state

- Format parsing warnings
- Format reconnect messages
   - Expected: mcpReconnectVisibleState(reconnect) equals `error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Format parsing warnings")
val issue = McpValidationIssue.new("project", "fatal", "bad-server", "servers.bad", "bad config")
expect(mcpParsingWarningsSummary("project", [issue])).to_contain("errors=1")
expect(mcpParsingIssueLine(issue)).to_contain("bad-server")

step("Format reconnect messages")
val reconnect = MCPReconnectState.new("fs", "needs-auth", "", false)
expect(mcpReconnectCompletionMessage(reconnect)).to_contain("requires authentication")
expect(mcpReconnectVisibleState(reconnect)).to_equal("error")
```

</details>

#### should render tool list and detail helpers

- Render list annotations
   - Expected: mcpToolListDescriptionColor(listItem) equals `error`
- Render tool detail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render list annotations")
val listItem = MCPToolListItem.new("mcp__fs__write", "write", false, true, true)
expect(mcpToolListDescription(listItem)).to_contain("destructive")
expect(mcpToolListDescriptionColor(listItem)).to_equal("error")

step("Render tool detail")
val parameter = MCPToolParameter.new("path", "string", "Target path", true)
val detail = MCPToolDetailState.new("fs", "mcp__fs__read", "read", "Read file", true, false, false, [parameter])
expect(mcpToolDetailTitle(detail)).to_contain("read-only")
expect(mcpToolParameterLine(parameter)).to_contain("required")
```

</details>

#### should apply MCP server approval choices

- Approve all project servers
   - Expected: updated.enabled_servers.len() equals `1`
   - Expected: updated.enable_all_project_servers is true
- Reject a project server


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Approve all project servers")
val settings = MCPServerApprovalSettings.new([], [], false)
val updated = mcpApprovalApply("github", "yes_all", settings)
expect(updated.enabled_servers.len()).to_equal(1)
expect(updated.enable_all_project_servers).to_equal(true)

step("Reject a project server")
expect(mcpApprovalSummary("bad", "no", settings)).to_contain("disabled=1")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: mcpAgentServerMenuSourceLinesModeled() equals `182`
   - Expected: mcpParsingWarningsSourceLinesModeled() equals `212`
   - Expected: mcpReconnectSourceLinesModeled() equals `166`
   - Expected: mcpStdioServerMenuSourceLinesModeled() equals `176`
   - Expected: mcpToolDetailViewSourceLinesModeled() equals `211`
   - Expected: mcpToolListViewSourceLinesModeled() equals `140`
   - Expected: mcpServerApprovalDialogSourceLinesModeled() equals `114`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(mcpAgentServerMenuSourceLinesModeled()).to_equal(182)
expect(mcpParsingWarningsSourceLinesModeled()).to_equal(212)
expect(mcpReconnectSourceLinesModeled()).to_equal(166)
expect(mcpStdioServerMenuSourceLinesModeled()).to_equal(176)
expect(mcpToolDetailViewSourceLinesModeled()).to_equal(211)
expect(mcpToolListViewSourceLinesModeled()).to_equal(140)
expect(mcpServerApprovalDialogSourceLinesModeled()).to_equal(114)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
