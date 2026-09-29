# Claude Full Main Slice

> Focused coverage for main.tsx entrypoint setup, settings, startup telemetry,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Main Slice

Focused coverage for main.tsx entrypoint setup, settings, startup telemetry,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/main_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for main.tsx entrypoint setup, settings, startup telemetry,
CLI/headless flow, MCP/connect, auth, shutdown, proactive/brief activation, and
teammate options.

## Scenarios

### Claude full main parity

#### should model startup settings telemetry and prefetch routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model startup settings telemetry and prefetch routes
- Check startup initialization
   - Expected: pending.target equals `remote`
   - Expected: getTeammateUtilsRoute(true) equals `teammate utils enabled`
   - Expected: getTeammatePromptAddendumRoute("brief") equals `teammate brief addendum`
   - Expected: getTeammateModeSnapshotRoute(true, "full") equals `teammate mode full`
   - Expected: logManagedSettingsRoute(true, true) equals `log managed settings verbose`
   - Expected: hasInspectArgRoute("--inspect") is true
   - Expected: isBeingDebuggedRoute(false, true) is true
   - Expected: logStartupTelemetryRoute(false, true, false) equals `startup telemetry sdk`
   - Expected: runMigrationsRoute(true, true) equals `run migrations`
   - Expected: prefetchSystemContextIfSafeRoute(false, false, true) equals `prefetch system context`
   - Expected: prefetchSystemContextIfSafeRoute(true, false, true) equals `skip unsafe prefetch`
   - Expected: startDeferredPrefetchesRoute(true, true) equals `prefetch network plugins`
   - Expected: loadSettingsFromFlagRoute(true, true) equals `load settings from flag`
   - Expected: loadSettingSourcesFromFlagRoute(false, true) equals `format setting source errors`
   - Expected: initializeEntrypointRoute(false, true) equals `initialize entrypoint`
   - Expected: initializeEntrypointRoute(true, true) equals `debug gate exits before normal setup`
   - Expected: entrypointModeRoute(true, false, false, true) equals `print forces non interactive entrypoint`
   - Expected: entrypointModeRoute(false, false, true, true) equals `sdk url non interactive entrypoint`
   - Expected: argvRewriteRoute("cc://session") equals `rewrite cc deep link`
   - Expected: argvRewriteRoute("assistant") equals `rewrite assistant pending chat`
   - Expected: preActionReadinessRoute(true, true, true, true, true) equals `preAction readiness complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model startup settings telemetry and prefetch routes")
step("Check startup initialization")
val pending = PendingConnect.new("remote", 1000)
expect(pending.target).to_equal("remote")
expect(getTeammateUtilsRoute(true)).to_equal("teammate utils enabled")
expect(getTeammatePromptAddendumRoute("brief")).to_equal("teammate brief addendum")
expect(getTeammateModeSnapshotRoute(true, "full")).to_equal("teammate mode full")
expect(logManagedSettingsRoute(true, true)).to_equal("log managed settings verbose")
expect(hasInspectArgRoute("--inspect")).to_equal(true)
expect(isBeingDebuggedRoute(false, true)).to_equal(true)
expect(logStartupTelemetryRoute(false, true, false)).to_equal("startup telemetry sdk")
expect(runMigrationsRoute(true, true)).to_equal("run migrations")
expect(prefetchSystemContextIfSafeRoute(false, false, true)).to_equal("prefetch system context")
expect(prefetchSystemContextIfSafeRoute(true, false, true)).to_equal("skip unsafe prefetch")
expect(startDeferredPrefetchesRoute(true, true)).to_equal("prefetch network plugins")
expect(loadSettingsFromFlagRoute(true, true)).to_equal("load settings from flag")
expect(loadSettingSourcesFromFlagRoute(false, true)).to_equal("format setting source errors")
expect(initializeEntrypointRoute(false, true)).to_equal("initialize entrypoint")
expect(initializeEntrypointRoute(true, true)).to_equal("debug gate exits before normal setup")
expect(entrypointModeRoute(true, false, false, true)).to_equal("print forces non interactive entrypoint")
expect(entrypointModeRoute(false, false, true, true)).to_equal("sdk url non interactive entrypoint")
expect(argvRewriteRoute("cc://session")).to_equal("rewrite cc deep link")
expect(argvRewriteRoute("assistant")).to_equal("rewrite assistant pending chat")
expect(preActionReadinessRoute(true, true, true, true, true)).to_equal("preAction readiness complete")
```

</details>

#### should model CLI run prompt and connection routes

- should model CLI run prompt and connection routes
- Check main and run modes
   - Expected: chat.headless is true
   - Expected: ssh.port equals `22`
   - Expected: mainRoute(true, false, false, false) equals `print help`
   - Expected: mainRoute(false, true, false, false) equals `print version`
   - Expected: mainRoute(false, false, true, false) equals `run headless query`
   - Expected: mainRoute(false, false, false, true) equals `launch repl`
   - Expected: printModeRoute(true, false) equals `print fast path skips subcommand parse`
   - Expected: printModeRoute(true, true) equals `print deep link parse path`
   - Expected: headlessContractRoute(true, false, false, true) equals `reject invalid headless json contract`
   - Expected: headlessContractRoute(true, false, true, true) equals `stream json headless contract`
   - Expected: headlessExecutionRoute(true, true, false) equals `runHeadless continuation`
   - Expected: getInputPromptRoute(false, false) equals `read stdin prompt`
   - Expected: getInputPromptRoute(true, true) equals `use prompt arg`
   - Expected: runRoute(false, false, false) equals `exit config error`
   - Expected: runRoute(true, true, false) equals `run command mode`
   - Expected: parseChannelEntriesRoute(1, false) equals `parsed channel entries`
   - Expected: parseChannelEntriesRoute(1, true) equals `channel parse error`
   - Expected: fileAuthRoute(true, false) equals `file flag hard error missing session token`
   - Expected: fileAuthRoute(true, true) equals `file flag authorized`
   - Expected: mcpConfigPolicyRoute(false, false, false) equals `mcp config invalid exits`
   - Expected: mcpConfigPolicyRoute(true, true, false) equals `mcp reserved name blocked`
   - Expected: connectMcpBatchRoute(2, false) equals `connect mcp batch`
   - Expected: connectMcpBatchRoute(1, true) equals `mcp connect timeout`
   - Expected: mcpRuntimeRoute(true, true, false, false) equals `interactive merge claudeai connectors`
   - Expected: mcpRuntimeRoute(false, false, false, false) equals `headless wait regular mcp`
   - Expected: mcpRuntimeRoute(true, true, true, false) equals `mcp duplicate signature cleanup`
   - Expected: claudeaiConnectRoute(true, false) equals `connect claudeai remote`
   - Expected: claudeaiConnectRoute(true, true) equals `claudeai connect timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model CLI run prompt and connection routes")
step("Check main and run modes")
val chat = PendingAssistantChat.new("hi", true)
expect(chat.headless).to_equal(true)
val ssh = PendingSSH.new("host", 22)
expect(ssh.port).to_equal(22)
expect(mainRoute(true, false, false, false)).to_equal("print help")
expect(mainRoute(false, true, false, false)).to_equal("print version")
expect(mainRoute(false, false, true, false)).to_equal("run headless query")
expect(mainRoute(false, false, false, true)).to_equal("launch repl")
expect(printModeRoute(true, false)).to_equal("print fast path skips subcommand parse")
expect(printModeRoute(true, true)).to_equal("print deep link parse path")
expect(headlessContractRoute(true, false, false, true)).to_equal("reject invalid headless json contract")
expect(headlessContractRoute(true, false, true, true)).to_equal("stream json headless contract")
expect(headlessExecutionRoute(true, true, false)).to_equal("runHeadless continuation")
expect(getInputPromptRoute(false, false)).to_equal("read stdin prompt")
expect(getInputPromptRoute(true, true)).to_equal("use prompt arg")
expect(runRoute(false, false, false)).to_equal("exit config error")
expect(runRoute(true, true, false)).to_equal("run command mode")
expect(parseChannelEntriesRoute(1, false)).to_equal("parsed channel entries")
expect(parseChannelEntriesRoute(1, true)).to_equal("channel parse error")
expect(fileAuthRoute(true, false)).to_equal("file flag hard error missing session token")
expect(fileAuthRoute(true, true)).to_equal("file flag authorized")
expect(mcpConfigPolicyRoute(false, false, false)).to_equal("mcp config invalid exits")
expect(mcpConfigPolicyRoute(true, true, false)).to_equal("mcp reserved name blocked")
expect(connectMcpBatchRoute(2, false)).to_equal("connect mcp batch")
expect(connectMcpBatchRoute(1, true)).to_equal("mcp connect timeout")
expect(mcpRuntimeRoute(true, true, false, false)).to_equal("interactive merge claudeai connectors")
expect(mcpRuntimeRoute(false, false, false, false)).to_equal("headless wait regular mcp")
expect(mcpRuntimeRoute(true, true, true, false)).to_equal("mcp duplicate signature cleanup")
expect(claudeaiConnectRoute(true, false)).to_equal("connect claudeai remote")
expect(claudeaiConnectRoute(true, true)).to_equal("claudeai connect timeout")
```

</details>

#### should model auth shutdown activation and teammate options

- should model auth shutdown activation and teammate options
- Check auth and shutdown routes
   - Expected: teammate.mode equals `brief`
   - Expected: getAccessTokenRoute(false, false, false) equals `request access token`
   - Expected: getAccessTokenRoute(true, false, false) equals `cached access token`
   - Expected: getAccessTokenRoute(false, true, false) equals `access token for remote`
   - Expected: getAccessTokenRoute(false, false, true) equals `access token failed`
   - Expected: shutdownRoute(false, false, "SIGINT") equals `shutdown from signal`
   - Expected: shutdownRoute(true, false, "") equals `run session end hooks shutdown`
   - Expected: shutdownRoute(false, true, "") equals `shutdown mcp clients`
   - Expected: remotePolicyRoute(true, false, true) equals `remote policy denied`
   - Expected: remotePolicyRoute(true, true, false) equals `remote missing descriptor hard fail`
   - Expected: remotePolicyRoute(true, true, true) equals `remote session allowed`
   - Expected: maybeActivateProactiveRoute(true, true) equals `activate proactive mode`
   - Expected: maybeActivateBriefRoute(true, true) equals `activate brief mode`
   - Expected: extractTeammateOptionsRoute(true, true) equals `teammate cowork brief`
   - Expected: extractTeammateOptionsRoute(false, false) equals `no teammate options`
   - Expected: teammateFlagValidationRoute(true, false, true) equals `teammate flags partial hard fail`
   - Expected: teammateFlagValidationRoute(true, true, true) equals `teammate flags complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model auth shutdown activation and teammate options")
step("Check auth and shutdown routes")
val teammate = TeammateOptions.new(true, "brief")
expect(teammate.mode).to_equal("brief")
expect(getAccessTokenRoute(false, false, false)).to_equal("request access token")
expect(getAccessTokenRoute(true, false, false)).to_equal("cached access token")
expect(getAccessTokenRoute(false, true, false)).to_equal("access token for remote")
expect(getAccessTokenRoute(false, false, true)).to_equal("access token failed")
expect(shutdownRoute(false, false, "SIGINT")).to_equal("shutdown from signal")
expect(shutdownRoute(true, false, "")).to_equal("run session end hooks shutdown")
expect(shutdownRoute(false, true, "")).to_equal("shutdown mcp clients")
expect(remotePolicyRoute(true, false, true)).to_equal("remote policy denied")
expect(remotePolicyRoute(true, true, false)).to_equal("remote missing descriptor hard fail")
expect(remotePolicyRoute(true, true, true)).to_equal("remote session allowed")
expect(maybeActivateProactiveRoute(true, true)).to_equal("activate proactive mode")
expect(maybeActivateBriefRoute(true, true)).to_equal("activate brief mode")
expect(extractTeammateOptionsRoute(true, true)).to_equal("teammate cowork brief")
expect(extractTeammateOptionsRoute(false, false)).to_equal("no teammate options")
expect(teammateFlagValidationRoute(true, false, true)).to_equal("teammate flags partial hard fail")
expect(teammateFlagValidationRoute(true, true, true)).to_equal("teammate flags complete")
```

</details>

#### should check modeled source floor

- should check modeled source floor
- Read source line helper
   - Expected: mainSourceLinesModeled() equals `4683`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should check modeled source floor")
step("Read source line helper")
expect(mainSourceLinesModeled()).to_equal(4683)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee1815a75afd25ee05ae7ede2de47e35e26789c08195c54f075301320b9aeabd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee1815a75afd25ee05ae7ede2de47e35e26789c08195c54f075301320b9aeabd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee1815a75afd25ee05ae7ede2de47e35e26789c08195c54f075301320b9aeabd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/tools/llm/claude_full/main_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/main_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/main_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/main_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/main_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/main_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model startup settings telemetry and prefetch routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/main_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model startup settings telemetry and prefetch routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/main_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model CLI run prompt and connection routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/main_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model CLI run prompt and connection routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/main_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model auth shutdown activation and teammate options' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/main_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model auth shutdown activation and teammate options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/main_spec.spl:105:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should check modeled source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
