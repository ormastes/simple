# Claude Full Agent SDK Types

> Checks SDK type facade placeholders and AbortError class.

<!-- sdn-diagram:id=agentSdkTypes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agentSdkTypes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agentSdkTypes_spec -> std
agentSdkTypes_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agentSdkTypes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks SDK type facade placeholders and AbortError class.

## Scenarios

### Claude full agent SDK types

#### exports AbortError

- AbortError has the expected class identity
   - Expected: error.name equals `AbortError`
   - Expected: error.message equals `aborted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("AbortError has the expected class identity")
val error = AbortError.new("aborted")
expect(error.name).to_equal("AbortError")
expect(error.message).to_equal("aborted")
```

</details>

#### keeps SDK placeholder functions explicit

- Facade functions keep the source not-implemented behavior
   - Expected: tool("t", "d").error equals `not implemented`
   - Expected: createSdkMcpServer("name", "1").error equals `not implemented`
   - Expected: query().error equals `query is not implemented in the SDK`
   - Expected: watchScheduledTasks("/tmp", false).error equals `not implemented`
   - Expected: buildMissedTaskNotification(2).error equals `not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- No access token returns nil; valid options produce a handle
- remote write
- remote sendControlRequest
- remote onStateChange
   - Expected: remote.sessionUrl equals `https://claude.ai/code`
   - Expected: remote.writes equals `["msg", "control_request:req"]`
   - Expected: remote.state equals `connected`
   - Expected: "missing handle" equals `handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
