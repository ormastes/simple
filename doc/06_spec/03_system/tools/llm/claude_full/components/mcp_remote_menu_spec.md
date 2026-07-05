# Claude Full MCP Remote Menu

> Modern SSpec coverage for the MCP remote server menu parity model.

<!-- sdn-diagram:id=mcp_remote_menu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_remote_menu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_remote_menu_spec -> std
mcp_remote_menu_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_remote_menu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP Remote Menu

Modern SSpec coverage for the MCP remote server menu parity model.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/mcp_remote_menu_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Modern SSpec coverage for the MCP remote server menu parity model.

## Scenarios

### Claude full MCP remote menu parity

#### should render connected remote server menu options

- Build a connected HTTP server
   - Expected: render.mode equals `menu`
   - Expected: render.title equals `github MCP Server`
   - Expected: render.status equals `connected`
   - Expected: render.auth equals `authenticated`
   - Expected: render.url equals `https://mcp.example`
   - Expected: render.configLocation equals `~/.claude.json`
   - Expected: render.capabilities equals `tools=3 prompts=2 resources=1`
   - Expected: render.options[0].value equals `tools`
   - Expected: render.options[1].value equals `reauth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a connected HTTP server")
val server = MCPRemoteServerInfo.new("github", "connected", "http", " https://mcp.example ", "srv_1", "user", "http", true, false)
val props = Props.new(server, 3, false)
val render = MCPRemoteServerMenuWithState(props, MCPRemoteInteractionState.idle(), 2, 1, false, "Esc")
expect(render.mode).to_equal("menu")
expect(render.title).to_equal("github MCP Server")
expect(render.status).to_equal("connected")
expect(render.auth).to_equal("authenticated")
expect(render.url).to_equal("https://mcp.example")
expect(render.configLocation).to_equal("~/.claude.json")
expect(render.capabilities).to_equal("tools=3 prompts=2 resources=1")
expect(render.options[0].value).to_equal("tools")
expect(render.options[1].value).to_equal("reauth")
```

</details>

#### should render unauthenticated and disabled actions

- Show authenticate for needs-auth remote servers
   - Expected: mcpRemoteAuthLabel(needsAuth, 0) equals `not authenticated`
   - Expected: authOptions[0].value equals `auth`
   - Expected: mcpRemoteSelectAction(needsAuth, "auth", 0) equals `authenticate`
- Show enable for disabled servers
   - Expected: mcpRemoteMenuOptions(disabled, 0)[0].value equals `toggle-enabled`
   - Expected: mcpRemoteSelectAction(disabled, "toggle-enabled", 0) equals `enable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Show authenticate for needs-auth remote servers")
val needsAuth = MCPRemoteServerInfo.new("jira", "needs-auth", "sse", "https://jira.example", "", "project", "", false, true)
val authOptions = mcpRemoteMenuOptions(needsAuth, 0)
expect(mcpRemoteAuthLabel(needsAuth, 0)).to_equal("not authenticated")
expect(authOptions[0].value).to_equal("auth")
expect(mcpRemoteSelectAction(needsAuth, "auth", 0)).to_equal("authenticate")
expect(mcpRemoteAuthCopy(needsAuth)).to_contain("identity provider")

step("Show enable for disabled servers")
val disabled = MCPRemoteServerInfo.new("jira", "disabled", "http", "https://jira.example", "", "project", "http", false, false)
expect(mcpRemoteMenuOptions(disabled, 0)[0].value).to_equal("toggle-enabled")
expect(mcpRemoteSelectAction(disabled, "toggle-enabled", 0)).to_equal("enable")
```

</details>

#### should model claude.ai authentication flows

- Build claude.ai auth URL
   - Expected: render.mode equals `claudeai-authenticating`
   - Expected: render.auth equals `managed by claude.ai`
- Model clear-auth browser flow
   - Expected: clearRender.mode equals `claudeai-clearing-auth`
   - Expected: clearRender.url equals `https://claude.ai/settings/connectors`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build claude.ai auth URL")
val proxy = MCPRemoteServerInfo.new("memory", "needs-auth", "claudeai-proxy", "", "mcprs123", "user", "claudeai-proxy", false, false)
val authState = handleClaudeAIAuth(proxy, "https://claude.ai", "org-1", "claude-code")
expect(authState.claudeAIAuthUrl).to_contain("/api/organizations/org-1/mcp/start-auth/mcpsrv123")
val render = MCPRemoteServerMenuWithState(Props.new(proxy, 0, false), authState, 0, 0, false, "Esc")
expect(render.mode).to_equal("claudeai-authenticating")
expect(render.auth).to_equal("managed by claude.ai")

step("Model clear-auth browser flow")
val clearState = handleClaudeAIClearAuth("https://claude.ai")
val clearRender = MCPRemoteServerMenuWithState(Props.new(proxy, 0, false), clearState, 0, 0, false, "Esc")
expect(clearRender.mode).to_equal("claudeai-clearing-auth")
expect(clearRender.url).to_equal("https://claude.ai/settings/connectors")
```

</details>

#### should model authentication, reconnect, and client updates

- Format auth and reconnect results
   - Expected: handleAuthenticate(server, false, "connected") equals `Authentication successful. Connected to github.`
   - Expected: handleAuthenticate(server, true, "connected") equals `Authentication successful. Reconnected to github.`
   - Expected: mcpRemoteReconnectMessage(server, "failed") equals `Failed to connect to github.`
- Update client arrays
   - Expected: updated[0].client.typeName equals `needs-auth`
   - Expected: failed[0].client.typeName equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Format auth and reconnect results")
val server = MCPRemoteServerInfo.new("github", "needs-auth", "http", "https://mcp.example", "", "user", "http", false, false)
expect(handleAuthenticate(server, false, "connected")).to_equal("Authentication successful. Connected to github.")
expect(handleAuthenticate(server, true, "connected")).to_equal("Authentication successful. Reconnected to github.")
expect(mcpRemoteReconnectMessage(server, "failed")).to_equal("Failed to connect to github.")

step("Update client arrays")
val updated = newClients([server], "github")
expect(updated[0].client.typeName).to_equal("needs-auth")
val failed = newClients_0([server], "github")
expect(failed[0].client.typeName).to_equal("failed")
```

</details>

#### should render transient states and source-line helper

- Render manual authentication state
   - Expected: authRender.mode equals `authenticating`
   - Expected: mcpRemoteCopyableUrl(authState) equals `https://auth.example`
- Render reconnecting state and line count
   - Expected: reconnectRender.mode equals `reconnecting`
   - Expected: reconnectRender.message equals `Establishing connection to MCP server`
   - Expected: mcpRemoteServerMenuSourceLinesModeled() equals `648`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render manual authentication state")
val server = MCPRemoteServerInfo.new("github", "needs-auth", "http", "https://mcp.example", "", "user", "http", false, false)
val authState = MCPRemoteInteractionState.authenticating("https://auth.example", "http://callback")
val authRender = MCPRemoteServerMenuWithState(Props.new(server, 0, false), authState, 0, 0, false, "Esc")
expect(authRender.mode).to_equal("authenticating")
expect(authRender.footer).to_contain("Manual callback URL entered")
expect(mcpRemoteCopyableUrl(authState)).to_equal("https://auth.example")

step("Render reconnecting state and line count")
val reconnectRender = MCPRemoteServerMenuWithState(Props.new(server, 0, false), MCPRemoteInteractionState.reconnecting(), 0, 0, true, "Esc")
expect(reconnectRender.mode).to_equal("reconnecting")
expect(reconnectRender.message).to_equal("Establishing connection to MCP server")
expect(mcpRemoteServerMenuSourceLinesModeled()).to_equal(648)
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
