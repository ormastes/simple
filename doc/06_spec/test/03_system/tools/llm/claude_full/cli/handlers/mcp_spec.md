# Claude Full CLI MCP Handler

> Checks MCP subcommand handler formatting and side-effect decisions.

<!-- sdn-diagram:id=mcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_spec -> std
mcp_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI MCP Handler

Checks MCP subcommand handler formatting and side-effect decisions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks MCP subcommand handler formatting and side-effect decisions.

## Scenarios

### Claude full cli MCP handler

#### checks server health states

- Map connection outcomes to user-visible status text
   - Expected: checkMcpServerHealth("connected", false) equals `Connected`
   - Expected: checkMcpServerHealth("needs-auth", false) equals `Needs authentication`
   - Expected: checkMcpServerHealth("failed", false) equals `Failed to connect`
   - Expected: checkMcpServerHealth("connected", true) equals `Connection error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Map connection outcomes to user-visible status text")
expect(checkMcpServerHealth("connected", false)).to_equal("Connected")
expect(checkMcpServerHealth("needs-auth", false)).to_equal("Needs authentication")
expect(checkMcpServerHealth("failed", false)).to_equal("Failed to connect")
expect(checkMcpServerHealth("connected", true)).to_equal("Connection error")
```

</details>

#### serves only after cwd is accessible

- Inaccessible cwd returns the same CLI error shape
   - Expected: missing.exitCode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inaccessible cwd returns the same CLI error shape")
val missing = mcpServeHandler("/gone", false, true, false, false)
expect(missing.exitCode).to_equal(1)
expect(missing.stderr).to_contain("Directory /gone does not exist")
val ok = mcpServeHandler("/repo", true, true, true, true)
expect(ok.stdout).to_contain("Started MCP server in /repo")
expect(ok.events).to_contain(mcpStartEventName())
```

</details>

#### removes scoped and unscoped servers

- Explicit scope removes directly and cleans secure storage for HTTP-like transports
   - Expected: scoped.modifiedFile equals `describeMcpConfigFilePath("project")`
   - Expected: scoped.secureStorageCleaned is true
- No scope reports ambiguity across all discovered scopes
   - Expected: ambiguous.exitCode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explicit scope removes directly and cleans secure storage for HTTP-like transports")
val scoped = mcpRemoveHandler("docs", "project", false, false, false, "http")
expect(scoped.stdout).to_contain("Removed MCP server docs from project config")
expect(scoped.modifiedFile).to_equal(describeMcpConfigFilePath("project"))
expect(scoped.secureStorageCleaned).to_equal(true)
step("No scope reports ambiguity across all discovered scopes")
val ambiguous = mcpRemoveHandler("docs", "", true, true, true, "stdio")
expect(ambiguous.exitCode).to_equal(1)
expect(ambiguous.stderr).to_contain("exists in multiple scopes")
expect(ambiguous.stderr).to_contain(removeSpecificScopeHint("docs", "local"))
```

</details>

#### lists configured servers with health

- Empty list prints add guidance and configured list formats by transport
   - Expected: empty.stdout equals `noServersConfiguredMessage()`
   - Expected: empty.shutdownCode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Empty list prints add guidance and configured list formats by transport")
val empty = mcpListHandler([], [])
expect(empty.stdout).to_equal(noServersConfiguredMessage())
expect(empty.shutdownCode).to_equal(0)
val stdio = McpServerConfig.stdio("fs", "local", "node", ["server.js"], ["DEBUG=1"])
val http = McpServerConfig.http("api", "user", "https://mcp.example", [], "", "", false)
val listed = mcpListHandler([stdio, http], ["Connected", "Needs authentication"])
expect(listed.stdout).to_start_with(checkingHealthMessage())
expect(listed.stdout).to_contain("fs: node server.js - Connected")
expect(listed.stdout).to_contain("api: https://mcp.example (HTTP) - Needs authentication")
```

</details>

#### gets server details

- Get output includes scope, status, transport details, and remove hint


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Get output includes scope, status, transport details, and remove hint")
val server = McpServerConfig.sse("remote", "user", "https://remote", ["Authorization: token"], "client", "7777", true)
val output = formatMcpGetOutput("remote", server, "Connected")
expect(output).to_contain("  Scope: User")
expect(output).to_contain("  Type: sse")
expect(output).to_contain("Authorization: token")
expect(output).to_contain("client_secret configured")
expect(output).to_contain(removeServerFooter("remote", "user"))
val missing = mcpGetHandler("missing", nil, "Failed to connect")
expect(missing.stderr).to_contain("No MCP server found with name: missing")
```

</details>

#### adds JSON and desktop imports

- JSON add stores client secret only for OAuth HTTP/SSE configs
   - Expected: addHttp.stdout equals `Added http MCP server remote to user config\n`
   - Expected: addHttp.savedClientSecret is true
   - Expected: addStdio.savedClientSecret is false
   - Expected: desktop.stdout equals `desktopNoServersMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("JSON add stores client secret only for OAuth HTTP/SSE configs")
val addHttp = mcpAddJsonHandler("remote", "user", "http", "https://remote", true, true, "secret", true)
expect(addHttp.stdout).to_equal("Added http MCP server remote to user config\n")
expect(addHttp.savedClientSecret).to_equal(true)
val addStdio = mcpAddJsonHandler("local", "", "stdio", "", false, true, "secret", true)
expect(addStdio.savedClientSecret).to_equal(false)
val desktop = mcpAddFromDesktopHandler("project", "darwin", 0)
expect(desktop.stdout).to_equal(desktopNoServersMessage())
expect(desktop.events).to_contain("tengu_mcp_add:desktop:darwin:project")
```

</details>

#### resets project choices

- Reset clears approvals and tells the user they will be prompted again
   - Expected: result.stdout equals `resetChoicesMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reset clears approvals and tells the user they will be prompted again")
val result = mcpResetChoicesHandler()
expect(result.stdout).to_equal(resetChoicesMessage())
expect(result.events).to_contain(mcpResetEventName())
```

</details>

#### exports source-backed constants and helpers

- Pin command names and behavior flags
   - Expected: mcpServeCommandName() equals `serve`
   - Expected: mcpRemoveCommandName() equals `remove`
   - Expected: mcpListCommandName() equals `list`
   - Expected: mcpGetCommandName() equals `get`
   - Expected: mcpAddJsonCommandName() equals `add-json`
   - Expected: mcpAddFromDesktopCommandName() equals `add-from-claude-desktop`
   - Expected: mcpResetChoicesCommandName() equals `reset-project-choices`
   - Expected: mcpDeleteEventName() equals `tengu_mcp_delete`
   - Expected: mcpListEventName() equals `tengu_mcp_list`
   - Expected: mcpGetEventName() equals `tengu_mcp_get`
   - Expected: mcpAddEventName() equals `tengu_mcp_add`
   - Expected: configSourceJson() equals `json`
   - Expected: configSourceDesktop() equals `desktop`
   - Expected: defaultConfigScope() equals `local`
   - Expected: ensureConfigScope("") equals `local`
   - Expected: getScopeLabel("project") equals `Project`
   - Expected: shouldCleanSecureStorage("sse") is true
   - Expected: shouldSaveClientSecret("sse", "https://x", true, true, "secret") is true
   - Expected: discoveredScopes(true, false, true) equals `["local", "user"]`
   - Expected: dynamicImportOnlyWhenCommandRuns() is true
   - Expected: listUsesGracefulShutdown() is true
   - Expected: getUsesGracefulShutdown() is true
   - Expected: serveChecksCwdBeforeSetup() is true
   - Expected: removeCleansSecureStorageBeforeExit() is true
   - Expected: addJsonReadsSecretBeforeWritingConfig() is true
   - Expected: desktopImportUsesKeybindingSetup() is true
   - Expected: resetChoicesClearsEnabledServers() is true
   - Expected: resetChoicesClearsDisabledServers() is true
   - Expected: resetChoicesDisablesEnableAllFlag() is true
   - Expected: connectionBatchSizeUsedForList() is true
   - Expected: internalSseIdeExcludedFromList() is true
   - Expected: cliOkUsedForMutationSuccess() is true
   - Expected: cliErrorUsedForUserErrors() is true
   - Expected: mcpHandlerSourceLinesModeled() equals `361`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin command names and behavior flags")
expect(mcpServeCommandName()).to_equal("serve")
expect(mcpRemoveCommandName()).to_equal("remove")
expect(mcpListCommandName()).to_equal("list")
expect(mcpGetCommandName()).to_equal("get")
expect(mcpAddJsonCommandName()).to_equal("add-json")
expect(mcpAddFromDesktopCommandName()).to_equal("add-from-claude-desktop")
expect(mcpResetChoicesCommandName()).to_equal("reset-project-choices")
expect(mcpDeleteEventName()).to_equal("tengu_mcp_delete")
expect(mcpListEventName()).to_equal("tengu_mcp_list")
expect(mcpGetEventName()).to_equal("tengu_mcp_get")
expect(mcpAddEventName()).to_equal("tengu_mcp_add")
expect(configSourceJson()).to_equal("json")
expect(configSourceDesktop()).to_equal("desktop")
expect(defaultConfigScope()).to_equal("local")
expect(ensureConfigScope("")).to_equal("local")
expect(getScopeLabel("project")).to_equal("Project")
expect(shouldCleanSecureStorage("sse")).to_equal(true)
expect(shouldSaveClientSecret("sse", "https://x", true, true, "secret")).to_equal(true)
expect(discoveredScopes(true, false, true)).to_equal(["local", "user"])
expect(dynamicImportOnlyWhenCommandRuns()).to_equal(true)
expect(listUsesGracefulShutdown()).to_equal(true)
expect(getUsesGracefulShutdown()).to_equal(true)
expect(serveChecksCwdBeforeSetup()).to_equal(true)
expect(removeCleansSecureStorageBeforeExit()).to_equal(true)
expect(addJsonReadsSecretBeforeWritingConfig()).to_equal(true)
expect(desktopImportUsesKeybindingSetup()).to_equal(true)
expect(resetChoicesClearsEnabledServers()).to_equal(true)
expect(resetChoicesClearsDisabledServers()).to_equal(true)
expect(resetChoicesDisablesEnableAllFlag()).to_equal(true)
expect(connectionBatchSizeUsedForList()).to_equal(true)
expect(internalSseIdeExcludedFromList()).to_equal(true)
expect(cliOkUsedForMutationSuccess()).to_equal(true)
expect(cliErrorUsedForUserErrors()).to_equal(true)
expect(mcpHandlerSourceLinesModeled()).to_equal(361)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
