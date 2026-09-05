# Claude Full Agent SDK Types

> Checks SDK type facade placeholders and AbortError class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Agent SDK Types

Checks SDK type facade placeholders and AbortError class.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks SDK type facade placeholders and AbortError class.

## Scenarios

### Claude full agent SDK types

#### exports AbortError

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports AbortError
- AbortError has the expected class identity
   - Expected: error.name equals `AbortError`
   - Expected: error.message equals `aborted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports AbortError")
step("AbortError has the expected class identity")
val error = AbortError.new("aborted")
expect(error.name).to_equal("AbortError")
expect(error.message).to_equal("aborted")
```

</details>

#### keeps SDK placeholder functions explicit

- keeps SDK placeholder functions explicit
- Facade functions keep the source not-implemented behavior
   - Expected: tool("t", "d").error equals `not implemented`
   - Expected: createSdkMcpServer("name", "1").error equals `not implemented`
   - Expected: query().error equals `query is not implemented in the SDK`
   - Expected: watchScheduledTasks("/tmp", false).error equals `not implemented`
   - Expected: buildMissedTaskNotification(2).error equals `not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps SDK placeholder functions explicit")
step("Facade functions keep the source not-implemented behavior")
expect(tool("t", "d").error).to_equal("not implemented")
expect(createSdkMcpServer("name", "1").error).to_equal("not implemented")
expect(query().error).to_equal("query is not implemented in the SDK")
expect(unstable_v2_createSession().error).to_contain("not implemented")
expect(unstable_v2_resumeSession().error).to_contain("not implemented")
expect(unstable_v2_prompt().error).to_contain("not implemented")
expect(getSessionMessages().error).to_contain("not implemented")
expect(listSessions().error).to_contain("not implemented")
expect(getSessionInfo().error).to_contain("not implemented")
expect(renameSession().error).to_contain("not implemented")
expect(tagSession().error).to_contain("not implemented")
expect(forkSession().error).to_contain("not implemented")
expect(watchScheduledTasks("/tmp", false).error).to_equal("not implemented")
expect(buildMissedTaskNotification(2).error).to_equal("not implemented")
```

</details>

#### models remote control handle shape

- models remote control handle shape
- No access token returns nil; valid options produce a handle
   - Expected: remote.sessionUrl equals `https://claude.ai/code`
   - Expected: remote.writes equals `["msg", "control_request:req"]`
   - Expected: remote.state equals `connected`
   - Expected: "missing handle" equals `handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models remote control handle shape")
step("No access token returns nil; valid options produce a handle")
val missing = connectRemoteControl(ConnectRemoteControlOptions(dir: "/repo", name: "", workerType: "", branch: "", gitRepoUrl: "", baseUrl: "https://claude.ai", orgUUID: "org", model: "model", accessToken: ""))
expect(missing).to_be_nil()
val handle = connectRemoteControl(ConnectRemoteControlOptions(dir: "/repo", name: "", workerType: "", branch: "", gitRepoUrl: "", baseUrl: "https://claude.ai", orgUUID: "org", model: "model", accessToken: "tok"))
if val Some(remote) = handle:
    remote.write("msg")
    remote.sendControlRequest("req")
    remote.onStateChange("connected", "")
    expect(remote.sessionUrl).to_equal("https://claude.ai/code")
    expect(remote.writes).to_equal(["msg", "control_request:req"])
    expect(remote.state).to_equal("connected")
else:
    expect("missing handle").to_equal("handle")
```

</details>

#### exports type facade constants

- exports type facade constants
- Pin exported type groups and documented behavior
   - Expected: exportedControlProtocolTypes() equals `["SDKControlRequest", "SDKControlResponse"]`
   - Expected: sdkBuildersUseControlTypesSubpath() is true
   - Expected: toolSupportsAnnotations() is true
   - Expected: toolSupportsSearchHint() is true
   - Expected: toolSupportsAlwaysLoad() is true
   - Expected: createSdkMcpServerLongCallTimeoutHintSeconds() equals `60`
   - Expected: v2ApiMarkedUnstable() is true
   - Expected: exampleModelId() equals `claude-sonnet-4-6`
   - Expected: sessionMessagesParseJsonlTranscript() is true
   - Expected: sessionMessagesUseParentUuidChain() is true
   - Expected: sessionMessagesCanIncludeSystemMessages() is true
   - Expected: listSessionsSupportsDir() is true
   - Expected: listSessionsSupportsLimitOffset() is true
   - Expected: getSessionInfoReturnsUndefinedWhenMissing() is true
   - Expected: renameSessionAppendsCustomTitleEntry() is true
   - Expected: tagSessionAcceptsNullToClear() is true
   - Expected: forkSessionRemapsMessageUuids() is true
   - Expected: forkSessionDoesNotCopyUndoHistory() is true
   - Expected: cronTaskFileName() equals `.claude/scheduled_tasks.json`
   - Expected: scheduledTaskEventFire() equals `fire`
   - Expected: scheduledTaskEventMissed() equals `missed`
   - Expected: watchScheduledTasksUsesDirectoryLock() is true
   - Expected: watchScheduledTasksDeletesOneShotAfterFire() is true
   - Expected: missedTasksYieldedOnInitialLoad() is true
   - Expected: connectRemoteControlInternalOnly() is true
   - Expected: connectRemoteControlSkipsBridgeGate() is true
   - Expected: connectRemoteControlRequiresOauth() is true
   - Expected: remoteControlStateReady() equals `ready`
   - Expected: remoteControlStateConnected() equals `connected`
   - Expected: remoteControlStateReconnecting() equals `reconnecting`
   - Expected: remoteControlStateFailed() equals `failed`
   - Expected: agentSdkTypesSourceLinesModeled() equals `421`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports type facade constants")
step("Pin exported type groups and documented behavior")
expect(exportedControlProtocolTypes()).to_equal(["SDKControlRequest", "SDKControlResponse"])
expect(exportedCoreRuntimeTypes()).to_contain("coreTypes")
expect(sdkBuildersUseControlTypesSubpath()).to_equal(true)
expect(toolSupportsAnnotations()).to_equal(true)
expect(toolSupportsSearchHint()).to_equal(true)
expect(toolSupportsAlwaysLoad()).to_equal(true)
expect(createSdkMcpServerLongCallTimeoutHintSeconds()).to_equal(60)
expect(v2ApiMarkedUnstable()).to_equal(true)
expect(exampleModelId()).to_equal("claude-sonnet-4-6")
expect(sessionMessagesParseJsonlTranscript()).to_equal(true)
expect(sessionMessagesUseParentUuidChain()).to_equal(true)
expect(sessionMessagesCanIncludeSystemMessages()).to_equal(true)
expect(listSessionsSupportsDir()).to_equal(true)
expect(listSessionsSupportsLimitOffset()).to_equal(true)
expect(getSessionInfoReturnsUndefinedWhenMissing()).to_equal(true)
expect(renameSessionAppendsCustomTitleEntry()).to_equal(true)
expect(tagSessionAcceptsNullToClear()).to_equal(true)
expect(forkSessionRemapsMessageUuids()).to_equal(true)
expect(forkSessionDoesNotCopyUndoHistory()).to_equal(true)
expect(cronTaskFileName()).to_equal(".claude/scheduled_tasks.json")
expect(scheduledTaskEventFire()).to_equal("fire")
expect(scheduledTaskEventMissed()).to_equal("missed")
expect(watchScheduledTasksUsesDirectoryLock()).to_equal(true)
expect(watchScheduledTasksDeletesOneShotAfterFire()).to_equal(true)
expect(missedTasksYieldedOnInitialLoad()).to_equal(true)
expect(connectRemoteControlInternalOnly()).to_equal(true)
expect(connectRemoteControlSkipsBridgeGate()).to_equal(true)
expect(connectRemoteControlRequiresOauth()).to_equal(true)
expect(remoteControlStateReady()).to_equal("ready")
expect(remoteControlStateConnected()).to_equal("connected")
expect(remoteControlStateReconnecting()).to_equal("reconnecting")
expect(remoteControlStateFailed()).to_equal("failed")
expect(agentSdkTypesSourceLinesModeled()).to_equal(421)
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

- Canonical SPipe generation for source `5c61bee06de79ba601fc4041d5c690db1a26df41c6534aaa811274712dc251bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c61bee06de79ba601fc4041d5c690db1a26df41c6534aaa811274712dc251bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c61bee06de79ba601fc4041d5c690db1a26df41c6534aaa811274712dc251bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports AbortError' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps SDK placeholder functions explicit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/entrypoints/agentSdkTypes_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models remote control handle shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
