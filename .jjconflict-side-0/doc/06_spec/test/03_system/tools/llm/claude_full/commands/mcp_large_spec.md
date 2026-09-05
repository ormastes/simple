# Claude Full MCP Large Commands

> Checks command-level parity models for large MCP command files.

<!-- sdn-diagram:id=mcp_large_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_large_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_large_spec -> std
mcp_large_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_large_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP Large Commands

Checks command-level parity models for large MCP command files.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/mcp_large_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks command-level parity models for large MCP command files.

## Scenarios

### Claude full MCP large command files

#### should model MCP add command metadata and stdio add

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = mcpAddCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("add")
expect(command.supportsNonInteractive).to_equal(true)
expect(mcpAddSourceLinesModeled()).to_equal(280)

val args = McpAddArgs.empty()
args.name = "fs"
args.target = "node"
args.trailingArgs = ["server.js"]
val result = mcpAddRun(args)
expect(result.ok).to_equal(true)
expect(result.config.kind).to_equal("stdio")
expect(result.config.scope).to_equal("local")
expect(result.modifiedPath).to_equal("local settings")
expect(mcpAddFormatConfig(result.config)).to_contain("node server.js")
```

</details>

#### should model remote MCP add validation, OAuth secret, and analytics

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val remote = McpAddArgs.empty()
remote.name = "docs"
remote.target = "https://mcp.example/mcp"
remote.scope = "project"
remote.headers = ["Authorization: Bearer token"]
remote.oauthClientId = "client"
remote.oauthClientSecret = "secret"
remote.callbackPort = "3333"
remote.fromJson = true
val result = mcpAddRun(remote)
expect(result.ok).to_equal(true)
expect(result.config.kind).to_equal("http")
expect(result.config.saveClientSecret).to_equal(true)
expect(result.eventName).to_equal("tengu_mcp_add:json:http:project")
expect(result.modifiedPath).to_equal(".mcp.json")

val bad = McpAddArgs.empty()
bad.name = "bad"
bad.target = "not-a-url"
bad.transport = "sse"
expect(mcpAddRun(bad).message).to_contain("http:// or https://")
```

</details>

#### should model XAA IdP command metadata and endpoint defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = xaaIdpCommand()
expect(command.name).to_equal("xaa-idp")
expect(command.isHidden).to_equal(true)
expect(xaaIdpCommandSourceLinesModeled()).to_equal(266)
expect(xaaIdpDefaultTokenEndpoint("https://idp.example/")).to_equal("https://idp.example/oauth/token")
```

</details>

#### should model XAA IdP success and cache-clearing failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = XaaIdpCommandInput.new("remote", "https://mcp.example/mcp", "client", "secret", "idp-client", "id-token", "")
val ok = xaaIdpRun(input, "https://idp.example", ["client_secret_post"], 200)
expect(ok.ok).to_equal(true)
expect(ok.tokenEndpoint).to_equal("https://idp.example/oauth/token")
expect(ok.authMethod).to_equal("client_secret_post")
expect(ok.eventName).to_equal(xaaIdpEventName("remote"))
expect(xaaIdpBuildBody(input, "https://mcp.example/mcp")).to_contain("requested_token_type=urn:ietf:params:oauth:token-type:id-jag")

val invalid = XaaIdpCommandInput.new("", "https://mcp.example/mcp", "client", "secret", "idp-client", "id-token", "")
expect(xaaIdpRun(invalid, "https://idp.example", [], 200).message).to_contain("server name")
val badGrant = xaaIdpRun(input, "https://idp.example", [], 401)
expect(badGrant.ok).to_equal(false)
expect(badGrant.shouldClearIdToken).to_equal(true)
val outage = xaaIdpRun(input, "https://idp.example", [], 503)
expect(outage.shouldClearIdToken).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
