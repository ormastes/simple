# Claude Full MCP List And Settings

> Modern SSpec coverage for MCP list-panel and settings parity models.

<!-- sdn-diagram:id=mcp_list_settings_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_list_settings_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_list_settings_spec -> std
mcp_list_settings_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_list_settings_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP List And Settings

Modern SSpec coverage for MCP list-panel and settings parity models.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/mcp_list_settings_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Modern SSpec coverage for MCP list-panel and settings parity models.

## Scenarios

### Claude full MCP list and settings parity

#### should organize MCP list rows and selection

- Build scoped and agent selectable items
   - Expected: items.len() equals `5`
   - Expected: items[0].serverName equals `fs`
   - Expected: items[1].serverName equals `github`
   - Expected: items[2].serverName equals `memory`
   - Expected: items[3].serverName equals `reviewer-mcp`
   - Expected: items[4].serverName equals `ide`
- Render selected list rows
   - Expected: render.title equals `Manage MCP servers`
   - Expected: render.subtitle equals `5 servers`
   - Expected: render.selectedName equals `reviewer-mcp`
   - Expected: mcpListPanelSelectAction(items, 3) equals `agent-server:reviewer-mcp`
   - Expected: mcpListPanelKeybindingAction("confirm:next", 4, items.len()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build scoped and agent selectable items")
val fs = MCPListPanelServerInfo.new("fs", "connected", "stdio", "project", "stdio", false)
val remote = MCPListPanelServerInfo.new("github", "needs-auth", "http", "user", "http", false)
val claudeAi = MCPListPanelServerInfo.new("memory", "connected", "claudeai-proxy", "user", "claudeai-proxy", false)
val dynamic = MCPListPanelServerInfo.new("ide", "connected", "stdio", "dynamic", "stdio", false)
val agent = MCPListPanelAgentServerInfo.new("reviewer-mcp", ["reviewer"], true)
val items = mcpListPanelBuildSelectableItems([remote, dynamic, fs, claudeAi], [agent])
expect(items.len()).to_equal(5)
expect(items[0].serverName).to_equal("fs")
expect(items[1].serverName).to_equal("github")
expect(items[2].serverName).to_equal("memory")
expect(items[3].serverName).to_equal("reviewer-mcp")
expect(items[4].serverName).to_equal("ide")

step("Render selected list rows")
val render = mcpListPanelRender([remote, dynamic, fs, claudeAi], [agent], 3, false)
expect(render.title).to_equal("Manage MCP servers")
expect(render.subtitle).to_equal("5 servers")
expect(render.selectedName).to_equal("reviewer-mcp")
expect(render.rows[0]).to_contain("Project MCPs")
expect(render.rows[1]).to_contain("fs")
expect(render.rows[5]).to_contain("memory")
expect(render.rows[7]).to_contain("@reviewer")
expect(mcpListPanelSelectAction(items, 3)).to_equal("agent-server:reviewer-mcp")
expect(mcpListPanelKeybindingAction("confirm:next", 4, items.len())).to_equal(0)
```

</details>

#### should model status, footer, and source-line helpers

- Format status and failed footer
   - Expected: mcpListPanelStatusText(reconnecting) equals `reconnecting (2/5)...`
   - Expected: mcpListPanelConfigPath("local") equals `.claude/settings.local.json`
- Check modeled TypeScript source floor
   - Expected: mcpListPanelModeledSourceLines() equals `503`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Format status and failed footer")
val reconnecting = MCPListPanelServerInfo.reconnecting("fs", "project", 2, 5)
val failed = MCPListPanelServerInfo.new("broken", "failed", "stdio", "project", "stdio", false)
expect(mcpListPanelStatusText(reconnecting)).to_equal("reconnecting (2/5)...")
expect(mcpListPanelFooter([failed], false)).to_contain("claude --debug")
expect(mcpListPanelConfigPath("local")).to_equal(".claude/settings.local.json")

step("Check modeled TypeScript source floor")
expect(mcpListPanelModeledSourceLines()).to_equal(503)
```

</details>

#### should prepare settings clients and agents

- Filter internal clients and prepare auth state
   - Expected: prepared.len() equals `2`
   - Expected: prepared[0].name equals `fs`
   - Expected: prepared[1].name equals `github`
   - Expected: prepared[1].transport equals `http`
   - Expected: prepared[1].isAuthenticated is true
- Extract agent-only MCP servers
   - Expected: agents.len() equals `1`
   - Expected: agents[0].name equals `github-agent`
   - Expected: agents[0].sourceAgents[0] equals `reviewer`
   - Expected: agents[0].needsAuth is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Filter internal clients and prepare auth state")
val ide = MCPSettingsClient.new("ide", "connected", "stdio", "project", false, true)
val github = MCPSettingsClient.new("github", "connected", "http", "user", false, true)
val fs = MCPSettingsClient.new("fs", "pending", "stdio", "project", false, false)
val prepared = mcpSettingsPrepareServers([ide, github, fs], true)
expect(prepared.len()).to_equal(2)
expect(prepared[0].name).to_equal("fs")
expect(prepared[1].name).to_equal("github")
expect(prepared[1].transport).to_equal("http")
expect(prepared[1].isAuthenticated).to_equal(true)

step("Extract agent-only MCP servers")
val agents = mcpSettingsExtractAgentServers([MCPSettingsAgentDefinition.new("reviewer", ["github-agent"], ["github-agent"])])
expect(agents.len()).to_equal(1)
expect(agents[0].name).to_equal("github-agent")
expect(agents[0].sourceAgents[0]).to_equal("reviewer")
expect(agents[0].needsAuth).to_equal(true)
```

</details>

#### should route settings views to component models

- Route server and tool views
   - Expected: mcpSettingsRenderDecision(mcpSettingsSelectServer("github"), [remote, stdio], [], [tool]).component equals `MCPRemoteServerMenu`
   - Expected: mcpSettingsRenderDecision(mcpSettingsSelectServer("fs"), [remote, stdio], [], [tool]).component equals `MCPStdioServerMenu`
   - Expected: mcpSettingsRenderDecision(mcpSettingsSelectTool("github", 0), [remote, stdio], [], [tool]).component equals `MCPToolDetailView`
- Route missing tool and agent views
   - Expected: missingTool.component equals `MCPToolListView`
   - Expected: missingTool.message equals `missing tool`
   - Expected: mcpSettingsRenderDecision(mcpSettingsSelectAgentServer("github-agent"), [remote], [agent], []).component equals `MCPAgentServerMenu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route server and tool views")
val remote = MCPSettingsPreparedServer.new("github", "github", "user", "http", true, "http", "connected")
val stdio = MCPSettingsPreparedServer.new("fs", "fs", "project", "stdio", false, "stdio", "connected")
val tool = MCPSettingsTool.new("read", "github")
expect(mcpSettingsRenderDecision(mcpSettingsSelectServer("github"), [remote, stdio], [], [tool]).component).to_equal("MCPRemoteServerMenu")
expect(mcpSettingsRenderDecision(mcpSettingsSelectServer("fs"), [remote, stdio], [], [tool]).component).to_equal("MCPStdioServerMenu")
expect(mcpSettingsRenderDecision(mcpSettingsSelectTool("github", 0), [remote, stdio], [], [tool]).component).to_equal("MCPToolDetailView")

step("Route missing tool and agent views")
val agent = MCPListPanelAgentServerInfo.new("github-agent", ["reviewer"], false)
val missingTool = mcpSettingsRenderDecision(mcpSettingsSelectTool("github", 4), [remote, stdio], [], [tool])
expect(missingTool.component).to_equal("MCPToolListView")
expect(missingTool.message).to_equal("missing tool")
expect(mcpSettingsRenderDecision(mcpSettingsSelectAgentServer("github-agent"), [remote], [agent], []).component).to_equal("MCPAgentServerMenu")
```

</details>

#### should expose settings completion and source-line helpers

- Render no-server completion
   - Expected: mcpSettingsShouldCompleteNoServers([], 1, 0) is false
- Check modeled TypeScript source floor
   - Expected: mcpSettingsModeledSourceLines() equals `397`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render no-server completion")
expect(mcpSettingsCompletionMessage([], [], [])).to_contain("No MCP servers configured")
expect(mcpSettingsShouldCompleteNoServers([], 1, 0)).to_equal(false)

step("Check modeled TypeScript source floor")
expect(mcpSettingsModeledSourceLines()).to_equal(397)
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
