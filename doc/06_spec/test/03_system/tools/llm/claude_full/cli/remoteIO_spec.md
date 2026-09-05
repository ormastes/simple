# Claude Full CLI RemoteIO

> Checks remote streaming state, CCR wiring, bridge echo, and cleanup.

<!-- sdn-diagram:id=remoteIO_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remoteIO_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remoteIO_spec -> std
remoteIO_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remoteIO_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI RemoteIO

Checks remote streaming state, CCR wiring, bridge echo, and cleanup.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/remoteIO_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks remote streaming state, CCR wiring, bridge echo, and cleanup.

## Scenarios

### Claude full cli RemoteIO

#### builds initial headers and prompt input

- Constructor state includes auth/env headers and normalized prompt chunks
   - Expected: remote.headers equals `["Authorization: Bearer tok", "x-environment-runner-version: 7"]`
   - Expected: remote.inputLines equals `["hello\n", "world\n"]`
   - Expected: remote.cleanupCount equals `1`
   - Expected: remote.keepAliveTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Constructor state includes auth/env headers and normalized prompt chunks")
val remote = RemoteIO.new("https://example/s", "tok", "7", "sid", "websocket", false, false, false, 0, ["hello\n", "world"])
expect(remote.headers).to_equal(["Authorization: Bearer tok", "x-environment-runner-version: 7"])
expect(remote.inputLines).to_equal(["hello\n", "world\n"])
expect(remote.cleanupCount).to_equal(1)
expect(remote.keepAliveTimerActive).to_equal(false)
```

</details>

#### echoes inbound data only for bridge debug

- Data always reaches input; stdout echo is bridge debug only
- remote receiveData
   - Expected: remote.inputLines equals `["event"]`
   - Expected: remote.stdoutLines equals `["event\n"]`
- quiet receiveData
   - Expected: quiet.stdoutLines equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Data always reaches input; stdout echo is bridge debug only")
val remote = RemoteIO.new("https://example/s", "", "", "sid", "websocket", true, true, false, 0, [])
remote.receiveData("event")
expect(remote.inputLines).to_equal(["event"])
expect(remote.stdoutLines).to_equal(["event\n"])
val quiet = RemoteIO.new("https://example/s", "", "", "sid", "websocket", true, false, false, 0, [])
quiet.receiveData("event")
expect(quiet.stdoutLines).to_equal([])
```

</details>

#### initializes CCR and reports lifecycle state

- CCR requires SSE and maps lifecycle states
   - Expected: remote.initializeCcr(true, "") equals `initialized`
   - Expected: remote.flushInternalEvents() equals `flushed`
   - Expected: remote.internalEventsPending equals `0`
- remote reportCommandLifecycle
- remote reportCommandLifecycle
   - Expected: remote.lifecycleReports equals `["u1:processing", "u2:processed"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("CCR requires SSE and maps lifecycle states")
val bad = RemoteIO.new("https://example/s", "", "", "sid", "websocket", false, false, true, 0, [])
expect(bad.initializeCcr(true, "")).to_contain("requires SSETransport")
val remote = RemoteIO.new("https://example/s", "", "", "sid", "sse", false, false, true, 0, [])
expect(remote.initializeCcr(true, "")).to_equal("initialized")
remote.internalEventsPending = 3
expect(remote.flushInternalEvents()).to_equal("flushed")
expect(remote.internalEventsPending).to_equal(0)
remote.reportCommandLifecycle("u1", "started")
remote.reportCommandLifecycle("u2", "completed")
expect(remote.lifecycleReports).to_equal(["u1:processing", "u2:processed"])
```

</details>

#### writes through CCR or transport and echoes bridge control requests

- Bridge parents see control_request while normal messages stay remote
- bridge write
- bridge write
   - Expected: bridge.transportWrites.len() equals `2`
   - Expected: bridge.stdoutLines equals `["{"type":"control_request"}\n"]`
- ccr write
   - Expected: ccr.ccrWrites equals `["{"text":"a\\u2028b"}"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bridge parents see control_request while normal messages stay remote")
val bridge = RemoteIO.new("https://example/s", "", "", "sid", "websocket", true, false, false, 0, [])
bridge.write("control_request", "{\"type\":\"control_request\"}")
bridge.write("assistant", "{\"type\":\"assistant\"}")
expect(bridge.transportWrites.len()).to_equal(2)
expect(bridge.stdoutLines).to_equal(["{\"type\":\"control_request\"}\n"])
val ccr = RemoteIO.new("https://example/s", "", "", "sid", "sse", false, false, true, 0, [])
ccr.write("assistant", "{\"text\":\"a b\"}")
expect(ccr.ccrWrites).to_equal(["{\"text\":\"a\\u2028b\"}"])
```

</details>

#### runs keepalive and close cleanup

- Keepalive is bridge-only and close clears timer
   - Expected: remote.keepAliveTimerActive is true
- remote sendKeepAlive
- remote close
   - Expected: remote.closed is true
   - Expected: remote.keepAliveTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keepalive is bridge-only and close clears timer")
val remote = RemoteIO.new("https://example/s", "", "", "sid", "websocket", true, false, false, 120000, [])
expect(remote.keepAliveTimerActive).to_equal(true)
remote.sendKeepAlive()
expect(remote.transportWrites).to_contain("{\"type\":\"keep_alive\"}")
remote.close()
expect(remote.closed).to_equal(true)
expect(remote.keepAliveTimerActive).to_equal(false)
```

</details>

#### exports helper contracts

- Pin source-backed constants and pure helpers
   - Expected: buildHeaders("", "") equals `[]`
   - Expected: refreshHeaders("tok", "") equals `["Authorization: Bearer tok"]`
   - Expected: normalizeInitialPromptChunk("x\n") equals `x\n`
   - Expected: trimOneTrailingNewline("x\n") equals `x`
   - Expected: ensureTrailingNewline("x") equals `x\n`
   - Expected: lifecycleDeliveryState("started") equals `processing`
   - Expected: shouldUseCcrV2("true") is true
   - Expected: ccrRequiresSseTransport() is true
   - Expected: ccrRegistersInternalEventWriter() is true
   - Expected: ccrRegistersInternalEventReaders() is true
   - Expected: ccrRegistersCommandLifecycleListener() is true
   - Expected: ccrRegistersSessionStateListener() is true
   - Expected: ccrRegistersSessionMetadataListener() is true
   - Expected: bridgeEchoesControlRequests() is true
   - Expected: bridgeEchoesAllMessagesInDebug() is true
   - Expected: keepAliveBridgeOnly() is true
   - Expected: keepAliveDisabledWhenZeroInterval() is true
   - Expected: transportConnectsAfterCallbacksWired() is true
   - Expected: dataCallbackWritesInputStream() is true
   - Expected: closeCallbackEndsInputStream() is true
   - Expected: registerCleanupClosesRemote() is true
   - Expected: remoteIoUsesPassThroughInput() is true
   - Expected: remoteIoExtendsStructuredIO() is true
   - Expected: remoteIoSupportsReplayUserMessages() is true
   - Expected: ccrInitFailureTriggersGracefulShutdown() is true
   - Expected: ccrInitFailureLogEventName() equals `cli_worker_lifecycle_init_failed`
   - Expected: keepAliveTypeName() equals `keep_alive`
   - Expected: environmentRunnerHeaderName() equals `x-environment-runner-version`
   - Expected: authorizationHeaderName() equals `Authorization`
   - Expected: ccrUseEnvName() equals `CLAUDE_CODE_USE_CCR_V2`
   - Expected: bridgeKindEnvName() equals `CLAUDE_CODE_ENVIRONMENT_KIND`
   - Expected: bridgeKindValue() equals `bridge`
   - Expected: environmentRunnerVersionEnvName() equals `CLAUDE_CODE_ENVIRONMENT_RUNNER_VERSION`
   - Expected: defaultKeepAliveDisabledValue() equals `0`
   - Expected: remoteIoSourceLinesModeled() equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source-backed constants and pure helpers")
expect(buildHeaders("", "")).to_equal([])
expect(refreshHeaders("tok", "")).to_equal(["Authorization: Bearer tok"])
expect(normalizeInitialPromptChunk("x\n")).to_equal("x\n")
expect(trimOneTrailingNewline("x\n")).to_equal("x")
expect(ensureTrailingNewline("x")).to_equal("x\n")
expect(lifecycleDeliveryState("started")).to_equal("processing")
expect(shouldUseCcrV2("true")).to_equal(true)
expect(ccrRequiresSseTransport()).to_equal(true)
expect(ccrRegistersInternalEventWriter()).to_equal(true)
expect(ccrRegistersInternalEventReaders()).to_equal(true)
expect(ccrRegistersCommandLifecycleListener()).to_equal(true)
expect(ccrRegistersSessionStateListener()).to_equal(true)
expect(ccrRegistersSessionMetadataListener()).to_equal(true)
expect(bridgeEchoesControlRequests()).to_equal(true)
expect(bridgeEchoesAllMessagesInDebug()).to_equal(true)
expect(keepAliveBridgeOnly()).to_equal(true)
expect(keepAliveDisabledWhenZeroInterval()).to_equal(true)
expect(transportConnectsAfterCallbacksWired()).to_equal(true)
expect(dataCallbackWritesInputStream()).to_equal(true)
expect(closeCallbackEndsInputStream()).to_equal(true)
expect(registerCleanupClosesRemote()).to_equal(true)
expect(remoteIoUsesPassThroughInput()).to_equal(true)
expect(remoteIoExtendsStructuredIO()).to_equal(true)
expect(remoteIoSupportsReplayUserMessages()).to_equal(true)
expect(ccrInitFailureTriggersGracefulShutdown()).to_equal(true)
expect(ccrInitFailureLogEventName()).to_equal("cli_worker_lifecycle_init_failed")
expect(noSessionTokenDebugMessage()).to_contain("No session ingress token")
expect(keepAliveDebugMessage()).to_contain("keep_alive")
expect(keepAliveTypeName()).to_equal("keep_alive")
expect(environmentRunnerHeaderName()).to_equal("x-environment-runner-version")
expect(authorizationHeaderName()).to_equal("Authorization")
expect(ccrUseEnvName()).to_equal("CLAUDE_CODE_USE_CCR_V2")
expect(bridgeKindEnvName()).to_equal("CLAUDE_CODE_ENVIRONMENT_KIND")
expect(bridgeKindValue()).to_equal("bridge")
expect(environmentRunnerVersionEnvName()).to_equal("CLAUDE_CODE_ENVIRONMENT_RUNNER_VERSION")
expect(defaultKeepAliveDisabledValue()).to_equal(0)
expect(remoteIoSourceLinesModeled()).to_equal(255)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
