# Claude Full Bridge Debug

> Mirrors the ant-only bridge debug fault injection queue used by Claude Code to

<!-- sdn-diagram:id=bridgeDebug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridgeDebug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridgeDebug_spec -> std
bridgeDebug_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridgeDebug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Debug

Mirrors the ant-only bridge debug fault injection queue used by Claude Code to

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridgeDebug_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the ant-only bridge debug fault injection queue used by Claude Code to
exercise reconnect, fatal teardown, and transient retry paths.

## Scenarios

### Claude full bridge debug fault injection

#### should register, describe, and clear the debug handle

- Create a debug state and register the active bridge handle
- state registerBridgeDebugHandle
   - Expected: state.hasBridgeDebugHandle() is true
   - Expected: state.getBridgeDebugHandle().describe() equals `env=env-1 session=session-1`
- Drive close, reconnect, and wake hooks on the registered handle
- current fireClose
- current forceReconnect
- current wakePollLoop
   - Expected: current.close_code equals `1006`
   - Expected: current.reconnect_count equals `1`
   - Expected: current.wake_count equals `1`
- Clear the handle and queued faults on teardown
- state injectBridgeFault
   - Expected: state.faultCount() equals `1`
- state clearBridgeDebugHandle
   - Expected: state.hasBridgeDebugHandle() is false
   - Expected: state.faultCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a debug state and register the active bridge handle")
val state = bridgeDebugStateNew()
val handle = bridgeDebugHandleNew("env-1", "session-1")
state.registerBridgeDebugHandle(handle)
expect(state.hasBridgeDebugHandle()).to_equal(true)
expect(state.getBridgeDebugHandle().describe()).to_equal("env=env-1 session=session-1")

step("Drive close, reconnect, and wake hooks on the registered handle")
val current = state.getBridgeDebugHandle()
current.fireClose(1006)
current.forceReconnect()
current.wakePollLoop()
expect(current.close_code).to_equal(1006)
expect(current.reconnect_count).to_equal(1)
expect(current.wake_count).to_equal(1)

step("Clear the handle and queued faults on teardown")
state.injectBridgeFault(bridgeFaultNew("pollForWork", "fatal", 404, "not_found_error", 1))
expect(state.faultCount()).to_equal(1)
state.clearBridgeDebugHandle()
expect(state.hasBridgeDebugHandle()).to_equal(false)
expect(state.faultCount()).to_equal(0)
```

</details>

#### should consume matching fatal faults before delegating to the API

- Queue a two-shot fatal poll fault
- state injectBridgeFault
   - Expected: state.faultCount() equals `1`
- Consume the first matching fault and keep the remaining shot
   - Expected: first.matched is true
   - Expected: first.fatal is true
   - Expected: first.status equals `404`
   - Expected: first.errorType equals `not_found_error`
   - Expected: first.message equals `[injected] Poll 404`
   - Expected: state.faultCount() equals `1`
- Consume the final shot and then delegate unmatched calls
   - Expected: second.matched is true
   - Expected: state.faultCount() equals `0`
   - Expected: delegated.matched is false
   - Expected: delegated.message equals `delegate:pollForWork`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Queue a two-shot fatal poll fault")
val state = bridgeDebugStateNew()
state.injectBridgeFault(bridgeFaultNew("pollForWork", "fatal", 404, "not_found_error", 2))
expect(state.faultCount()).to_equal(1)
expect(state.latestLog()).to_contain("Queued fault")

step("Consume the first matching fault and keep the remaining shot")
val first = state.wrapApiForFaultInjection("pollForWork")
expect(first.matched).to_equal(true)
expect(first.fatal).to_equal(true)
expect(first.status).to_equal(404)
expect(first.errorType).to_equal("not_found_error")
expect(first.message).to_equal("[injected] Poll 404")
expect(state.faultCount()).to_equal(1)

step("Consume the final shot and then delegate unmatched calls")
val second = state.pollForWork()
expect(second.matched).to_equal(true)
expect(state.faultCount()).to_equal(0)
val delegated = state.pollForWork()
expect(delegated.matched).to_equal(false)
expect(delegated.message).to_equal("delegate:pollForWork")
```

</details>

#### should model transient registration, reconnect, and heartbeat faults

- Queue each non-poll bridge API method
- state injectBridgeFault
- state injectBridgeFault
- state injectBridgeFault
   - Expected: state.faultCount() equals `3`
- Consume registration as a transient retryable fault
   - Expected: registration.matched is true
   - Expected: registration.fatal is false
   - Expected: registration.message equals `[injected transient] Registration 503`
- Consume reconnect as fatal and heartbeat as transient
   - Expected: reconnect.fatal is true
   - Expected: reconnect.message equals `[injected] ReconnectSession 410`
   - Expected: heartbeat.fatal is false
   - Expected: heartbeat.message equals `[injected transient] Heartbeat 502`
   - Expected: state.faultCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Queue each non-poll bridge API method")
val state = bridgeDebugStateNew()
state.injectBridgeFault(bridgeFaultNew("registerBridgeEnvironment", "transient", 503, "", 1))
state.injectBridgeFault(bridgeFaultNew("reconnectSession", "fatal", 410, "gone", 1))
state.injectBridgeFault(bridgeFaultNew("heartbeatWork", "transient", 502, "", 1))
expect(state.faultCount()).to_equal(3)

step("Consume registration as a transient retryable fault")
val registration = state.registerBridgeEnvironment()
expect(registration.matched).to_equal(true)
expect(registration.fatal).to_equal(false)
expect(registration.message).to_equal("[injected transient] Registration 503")

step("Consume reconnect as fatal and heartbeat as transient")
val reconnect = state.reconnectSession()
expect(reconnect.fatal).to_equal(true)
expect(reconnect.message).to_equal("[injected] ReconnectSession 410")
val heartbeat = state.heartbeatWork()
expect(heartbeat.fatal).to_equal(false)
expect(heartbeat.message).to_equal("[injected transient] Heartbeat 502")
expect(state.faultCount()).to_equal(0)
```

</details>

#### should normalize defensive input the same way the wrapper does

- Normalize unsupported kind and method inputs to safe defaults
   - Expected: fault.method equals `pollForWork`
   - Expected: fault.kind equals `transient`
   - Expected: fault.label() equals `pollForWork transient/500 x1`
- state injectBridgeFault
   - Expected: result.message equals `[injected transient] Poll 500`
   - Expected: normalizeBridgeFaultMethod("unknown") equals `pollForWork`
   - Expected: bridgeFaultContext("unknown") equals `Poll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normalize unsupported kind and method inputs to safe defaults")
val state = bridgeDebugStateNew()
val fault = bridgeFaultNew("unknown", "unknown", 500, "", 1)
expect(fault.method).to_equal("pollForWork")
expect(fault.kind).to_equal("transient")
expect(fault.label()).to_equal("pollForWork transient/500 x1")
state.injectBridgeFault(fault)
val result = state.wrapApiForFaultInjection("unknown")
expect(result.message).to_equal("[injected transient] Poll 500")
expect(normalizeBridgeFaultMethod("unknown")).to_equal("pollForWork")
expect(bridgeFaultContext("unknown")).to_equal("Poll")
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
