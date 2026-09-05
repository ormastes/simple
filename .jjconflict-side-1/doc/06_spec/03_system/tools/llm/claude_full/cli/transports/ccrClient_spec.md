# Claude Full CCR Client

> Checks the CCR init error, lifecycle state, request decisions, delivery queues,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CCR Client

Checks the CCR init error, lifecycle state, request decisions, delivery queues,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the CCR init error, lifecycle state, request decisions, delivery queues,
and text-delta accumulation model used by the Simple parity slice.

## Scenarios

### Claude full CCRClient

#### models CCRInitError reasons and constructor URL state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models CCRInitError reasons and constructor URL state
- Init errors carry typed reasons and the client extracts the session id
   - Expected: err.reason equals `missing_epoch`
   - Expected: err.message equals `CCRClient init failed: missing_epoch`
   - Expected: ccrInitFailReasons() equals `["no_auth_headers", "missing_epoch", "worker_register_failed"]`
   - Expected: client.sessionBaseUrl equals `https://ccr.example/v1/code/sessions/cse_123`
   - Expected: client.sessionId equals `cse_123`
   - Expected: client.heartbeatIntervalMs equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models CCRInitError reasons and constructor URL state")
step("Init errors carry typed reasons and the client extracts the session id")
val err = CCRInitError.new("missing_epoch")
expect(err.reason).to_equal("missing_epoch")
expect(err.message).to_equal("CCRClient init failed: missing_epoch")
expect(ccrInitFailReasons()).to_equal(["no_auth_headers", "missing_epoch", "worker_register_failed"])
val client = CCRClient.new("https://ccr.example/v1/code/sessions/cse_123/", ["Authorization: Bearer t"])
expect(client.sessionBaseUrl).to_equal("https://ccr.example/v1/code/sessions/cse_123")
expect(client.sessionId).to_equal("cse_123")
expect(client.heartbeatIntervalMs).to_equal(20000)
```

</details>

#### initializes only with auth headers and a worker epoch

- initializes only with auth headers and a worker epoch
- Initialization fails before side effects, then starts idle heartbeat after success
   - Expected: err.reason equals `no_auth_headers`
   - Expected: "missing error" equals `no_auth_headers`
   - Expected: err.reason equals `missing_epoch`
   - Expected: "missing error" equals `missing_epoch`
   - Expected: err.reason equals `worker_register_failed`
   - Expected: "missing error" equals `worker_register_failed`
   - Expected: ok.getWorkerEpoch() equals `42`
   - Expected: ok.currentState equals `idle`
   - Expected: ok.heartbeatStarted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes only with auth headers and a worker epoch")
step("Initialization fails before side effects, then starts idle heartbeat after success")
val missingAuth = CCRClient.new("https://ccr.example/v1/code/sessions/cse_1", [])
if val Some(err) = missingAuth.initialize(1):
    expect(err.reason).to_equal("no_auth_headers")
else:
    expect("missing error").to_equal("no_auth_headers")
val missingEpoch = CCRClient.new("https://ccr.example/v1/code/sessions/cse_1", ["Authorization: Bearer t"])
if val Some(err) = missingEpoch.initialize(-1):
    expect(err.reason).to_equal("missing_epoch")
else:
    expect("missing error").to_equal("missing_epoch")
val failedPut = CCRClient.new("https://ccr.example/v1/code/sessions/cse_1", ["Authorization: Bearer t"])
if val Some(err) = failedPut.initializeWithRegisterStatus(7, 500):
    expect(err.reason).to_equal("worker_register_failed")
else:
    expect("missing error").to_equal("worker_register_failed")
val ok = CCRClient.new("https://ccr.example/v1/code/sessions/cse_1", ["Authorization: Bearer t"])
expect(ok.initialize(42)).to_be_nil()
expect(ok.getWorkerEpoch()).to_equal(42)
expect(ok.currentState).to_equal("idle")
expect(ok.heartbeatStarted).to_equal(true)
```

</details>

#### handles request statuses and worker reporting

- handles request statuses and worker reporting
- 2xx resets auth failures, 429 returns milliseconds, 409 closes
   - Expected: client.requestStatus(204, 0).ok is true
   - Expected: client.consecutiveAuthFailures equals `0`
   - Expected: throttled.ok is false
   - Expected: throttled.retryAfterMs equals `3000`
   - Expected: client.epochMismatchCount equals `1`
   - Expected: client.workerPatches equals `["worker_status=requires_action;requires_action_details=tool=Edit", "external... (full value in folded executable source)`
   - Expected: client.deliveryEvents equals `["evt_1:processed"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles request statuses and worker reporting")
step("2xx resets auth failures, 429 returns milliseconds, 409 closes")
val client = CCRClient.new("https://ccr.example/v1/code/sessions/cse_1", ["Authorization: Bearer t"])
client.consecutiveAuthFailures = 4
expect(client.requestStatus(204, 0).ok).to_equal(true)
expect(client.consecutiveAuthFailures).to_equal(0)
val throttled = client.requestStatus(429, 3)
expect(throttled.ok).to_equal(false)
expect(throttled.retryAfterMs).to_equal(3000)
var i = 0
while i < maxConsecutiveAuthFailures():
    client.requestStatus(401, 0)
    i = i + 1
expect(client.epochMismatchCount).to_equal(1)
client.reportState("requires_action", "tool=Edit")
client.reportMetadata("task_summary=hello")
client.reportDelivery("evt_1", "processed")
expect(client.workerPatches).to_equal(["worker_status=requires_action;requires_action_details=tool=Edit", "external_metadata=task_summary=hello"])
expect(client.deliveryEvents).to_equal(["evt_1:processed"])
```

</details>

#### coalesces stream text and clears completed assistant state

- coalesces stream text and clears completed assistant state
- Text deltas emit full-so-far snapshots for the active message
   - Expected: scopeKey(started) equals `cse_1:`
   - Expected: out.len() equals `3`
   - Expected: out[1].text equals `hel`
   - Expected: out[2].text equals `hello`
   - Expected: raw[0].text equals `!`
   - Expected: state.blocks.len() < 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("coalesces stream text and clears completed assistant state")
step("Text deltas emit full-so-far snapshots for the active message")
val state = createStreamAccumulator()
val started = EventPayload.streamMessageStart("u0", "cse_1", "", "msg_1")
expect(scopeKey(started)).to_equal("cse_1:")
val out = accumulateStreamEvents([
    started,
    EventPayload.streamTextDelta("u1", "cse_1", "", 0, "hel"),
    EventPayload.streamTextDelta("u2", "cse_1", "", 0, "lo")
], state)
expect(out.len()).to_equal(3)
expect(out[1].text).to_equal("hel")
expect(out[2].text).to_equal("hello")
clearStreamAccumulatorForMessage(state, EventPayload.assistant("cse_1", "", "msg_1"))
val raw = accumulateStreamEvents([EventPayload.streamTextDelta("u3", "cse_1", "", 0, "!")], state)
expect(raw[0].text).to_equal("!")
expect(state.blocks.len() < 1).to_equal(true)
```

</details>

#### flushes stream events before non-stream writes and closes queues

- flushes stream events before non-stream writes and closes queues
- Client write path preserves ordering and marks stream snapshots ephemeral
   - Expected: client.clientEvents.len() equals `3`
   - Expected: client.clientEvents[1].ephemeral is true
   - Expected: client.clientEvents[1].payload.text equals `a`
   - Expected: client.clientEvents[2].payload.uuid equals `generated-uuid`
   - Expected: client.internalEventsPending() equals `1`
   - Expected: client.closed is true
   - Expected: client.heartbeatStarted is false
   - Expected: client.streamEventBuffer.len() < 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flushes stream events before non-stream writes and closes queues")
step("Client write path preserves ordering and marks stream snapshots ephemeral")
val client = CCRClient.new("https://ccr.example/v1/code/sessions/cse_1", ["Authorization: Bearer t"])
client.writeEvent(EventPayload.streamMessageStart("u0", "cse_1", "", "msg_1"))
client.writeEvent(EventPayload.streamTextDelta("u1", "cse_1", "", 0, "a"))
client.writeEvent(EventPayload.new("", "keep_alive"))
expect(client.clientEvents.len()).to_equal(3)
expect(client.clientEvents[1].ephemeral).to_equal(true)
expect(client.clientEvents[1].payload.text).to_equal("a")
expect(client.clientEvents[2].payload.uuid).to_equal("generated-uuid")
client.writeInternalEvent("transcript", "assistant", true, "agent_1")
expect(client.internalEventsPending()).to_equal(1)
client.close()
expect(client.closed).to_equal(true)
expect(client.heartbeatStarted).to_equal(false)
expect(client.streamEventBuffer.len() < 1).to_equal(true)
```

</details>

#### exports source-backed constants

- exports source-backed constants
- Pin CCR paths, timers, and parity accounting
   - Expected: alwaysValidStatus() is true
   - Expected: defaultHeartbeatIntervalMs() equals `20000`
   - Expected: streamEventFlushIntervalMs() equals `100`
   - Expected: requestContentTypeHeader() equals `Content-Type: application/json`
   - Expected: requestAnthropicVersionHeader() equals `anthropic-version: 2023-06-01`
   - Expected: requestUserAgentHeaderRequired() is true
   - Expected: workerPath() equals `/worker`
   - Expected: workerHeartbeatPath() equals `/worker/heartbeat`
   - Expected: workerEventsPath() equals `/worker/events`
   - Expected: workerInternalEventsPath() equals `/worker/internal-events`
   - Expected: workerDeliveryPath() equals `/worker/events/delivery`
   - Expected: streamEventsAreBuffered() is true
   - Expected: textDeltasEmitFullSnapshots() is true
   - Expected: assistantMessageClearsAccumulator() is true
   - Expected: nonStreamWriteFlushesBufferedStreamEvents() is true
   - Expected: deliveryAckRegisteredInConstructor() is true
   - Expected: initializeRequiresAuthHeaders() is true
   - Expected: initializeRequiresWorkerEpoch() is true
   - Expected: initializeStartsHeartbeatAfterWorkerPut() is true
   - Expected: requestReturnsRetryAfterMilliseconds() is true
   - Expected: authFailureThresholdExits() is true
   - Expected: closeClearsTimersQueuesAndAccumulator() is true
   - Expected: ccrClientSourceLinesModeled() equals `998`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
step("Pin CCR paths, timers, and parity accounting")
expect(alwaysValidStatus()).to_equal(true)
expect(defaultHeartbeatIntervalMs()).to_equal(20000)
expect(streamEventFlushIntervalMs()).to_equal(100)
expect(requestContentTypeHeader()).to_equal("Content-Type: application/json")
expect(requestAnthropicVersionHeader()).to_equal("anthropic-version: 2023-06-01")
expect(requestUserAgentHeaderRequired()).to_equal(true)
expect(workerPath()).to_equal("/worker")
expect(workerHeartbeatPath()).to_equal("/worker/heartbeat")
expect(workerEventsPath()).to_equal("/worker/events")
expect(workerInternalEventsPath()).to_equal("/worker/internal-events")
expect(workerDeliveryPath()).to_equal("/worker/events/delivery")
expect(streamEventsAreBuffered()).to_equal(true)
expect(textDeltasEmitFullSnapshots()).to_equal(true)
expect(assistantMessageClearsAccumulator()).to_equal(true)
expect(nonStreamWriteFlushesBufferedStreamEvents()).to_equal(true)
expect(deliveryAckRegisteredInConstructor()).to_equal(true)
expect(initializeRequiresAuthHeaders()).to_equal(true)
expect(initializeRequiresWorkerEpoch()).to_equal(true)
expect(initializeStartsHeartbeatAfterWorkerPut()).to_equal(true)
expect(requestReturnsRetryAfterMilliseconds()).to_equal(true)
expect(authFailureThresholdExits()).to_equal(true)
expect(closeClearsTimersQueuesAndAccumulator()).to_equal(true)
expect(ccrClientSourceLinesModeled()).to_equal(998)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `97a871a4db46427eda6f39baf36726c875936ccee779cf69f5a4b9aabc19381c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97a871a4db46427eda6f39baf36726c875936ccee779cf69f5a4b9aabc19381c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97a871a4db46427eda6f39baf36726c875936ccee779cf69f5a4b9aabc19381c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models CCRInitError reasons and constructor URL state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes only with auth headers and a worker epoch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/ccrClient_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles request statuses and worker reporting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
