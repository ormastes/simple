# Claude Full CLI MCP Handler

> Checks MCP subcommand handler formatting and side-effect decisions.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks MCP subcommand handler formatting and side-effect decisions.

## Scenarios

### Claude full cli MCP handler

#### checks server health states

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- checks server health states
- Map connection outcomes to user-visible status text
   - Expected: checkMcpServerHealth("connected", false) equals `Connected`
   - Expected: checkMcpServerHealth("needs-auth", false) equals `Needs authentication`
   - Expected: checkMcpServerHealth("failed", false) equals `Failed to connect`
   - Expected: checkMcpServerHealth("connected", true) equals `Connection error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks server health states")
step("Map connection outcomes to user-visible status text")
expect(checkMcpServerHealth("connected", false)).to_equal("Connected")
expect(checkMcpServerHealth("needs-auth", false)).to_equal("Needs authentication")
expect(checkMcpServerHealth("failed", false)).to_equal("Failed to connect")
expect(checkMcpServerHealth("connected", true)).to_equal("Connection error")
```

</details>

#### serves only after cwd is accessible

- serves only after cwd is accessible
- Inaccessible cwd returns the same CLI error shape
   - Expected: missing.exitCode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serves only after cwd is accessible")
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

- removes scoped and unscoped servers
- Explicit scope removes directly and cleans secure storage for HTTP-like transports
   - Expected: scoped.modifiedFile equals `describeMcpConfigFilePath("project")`
   - Expected: scoped.secureStorageCleaned is true
- No scope reports ambiguity across all discovered scopes
   - Expected: ambiguous.exitCode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes scoped and unscoped servers")
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

- lists configured servers with health
- Empty list prints add guidance and configured list formats by transport
   - Expected: empty.stdout equals `noServersConfiguredMessage()`
   - Expected: empty.shutdownCode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lists configured servers with health")
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

- gets server details
- Get output includes scope, status, transport details, and remove hint


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets server details")
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

- adds JSON and desktop imports
- JSON add stores client secret only for OAuth HTTP/SSE configs
   - Expected: addHttp.stdout equals `Added http MCP server remote to user config\n`
   - Expected: addHttp.savedClientSecret is true
   - Expected: addStdio.savedClientSecret is false
   - Expected: desktop.stdout equals `desktopNoServersMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds JSON and desktop imports")
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

- resets project choices
- Reset clears approvals and tells the user they will be prompted again
   - Expected: result.stdout equals `resetChoicesMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resets project choices")
step("Reset clears approvals and tells the user they will be prompted again")
val result = mcpResetChoicesHandler()
expect(result.stdout).to_equal(resetChoicesMessage())
expect(result.events).to_contain(mcpResetEventName())
```

</details>

#### exports source-backed constants and helpers

- exports source-backed constants and helpers
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

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants and helpers")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0c82d2a8f31ed867716e5ea4a045951d1d3c2704caa45b51fb05f1ec07b722d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0c82d2a8f31ed867716e5ea4a045951d1d3c2704caa45b51fb05f1ec07b722d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0c82d2a8f31ed867716e5ea4a045951d1d3c2704caa45b51fb05f1ec07b722d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks server health states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serves only after cwd is accessible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/mcp_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes scoped and unscoped servers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
