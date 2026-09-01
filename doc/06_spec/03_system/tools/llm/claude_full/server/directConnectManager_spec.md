# Claude Full Direct Connect Session Manager

> Purpose: should connect with optional authorization header

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Direct Connect Session Manager

Purpose: should connect with optional authorization header

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should connect with optional authorization header
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Direct Connect Session Manager

Checks direct-connect websocket message filtering and outbound control messages.

## Scenarios

### Claude full DirectConnectSessionManager

#### should connect with optional authorization header

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should connect with optional authorization header
- Verify: should connect with optional authorization header
- Connect a direct websocket
   - Expected: manager.isConnected() is true
   - Expected: manager.authorizationHeader equals `Bearer tok`
   - Expected: manager.callbacks[0] equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should connect with optional authorization header")
step("Verify: should connect with optional authorization header")
# @req: REQ-TOOLS-Dire-001
step("Connect a direct websocket")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", "tok"))
manager.connect()
expect(manager.isConnected()).to_equal(true)
expect(manager.authorizationHeader).to_equal("Bearer tok")
expect(manager.callbacks[0]).to_equal("connected")
```

</details>

#### should parse newline-delimited messages and forward SDK messages

- should parse newline-delimited messages and forward SDK messages
- Verify: should parse newline-delimited messages and forward SDK messages
- Handle multiple websocket lines
   - Expected: manager.messages equals `["assistant:hello", "result:ok"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse newline-delimited messages and forward SDK messages")
step("Verify: should parse newline-delimited messages and forward SDK messages")
# @req: REQ-TOOLS-Dire-001
step("Handle multiple websocket lines")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
manager.connect()
manager.handleMessageBatch("assistant||||hello\n\nresult||||ok\n")
expect(manager.messages).to_equal(["assistant:hello", "result:ok"])
```

</details>

#### should route permission requests and reject unsupported subtypes

- should route permission requests and reject unsupported subtypes
- Verify: should route permission requests and reject unsupported subtypes
- Handle control requests
   - Expected: manager.permissionRequests[0] equals `req-1:Bash`
   - Expected: manager.sent[0] equals `control_response:error:req-2:Unsupported control request subtype: unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route permission requests and reject unsupported subtypes")
step("Verify: should route permission requests and reject unsupported subtypes")
# @req: REQ-TOOLS-Dire-001
step("Handle control requests")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
manager.connect()
manager.handleMessageBatch("control_request|can_use_tool|req-1|Bash|\ncontrol_request|unknown|req-2||\n")
expect(manager.permissionRequests[0]).to_equal("req-1:Bash")
expect(manager.sent[0]).to_equal("control_response:error:req-2:Unsupported control request subtype: unknown")
```

</details>

#### should filter non-SDK stream and control messages

- should filter non-SDK stream and control messages
- Verify: should filter non-SDK stream and control messages
- Handle messages that should not be forwarded
   - Expected: manager.messages.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filter non-SDK stream and control messages")
step("Verify: should filter non-SDK stream and control messages")
# @req: REQ-TOOLS-Dire-001
step("Handle messages that should not be forwarded")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
manager.connect()
manager.handleMessageBatch("control_response||||ack\nkeep_alive||||\ncontrol_cancel_request||||\nstreamlined_text||||x\nsystem|post_turn_summary|||summary\n")
expect(manager.messages.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should send user messages only when connected

- should send user messages only when connected
- Verify: should send user messages only when connected
- Send message before and after connect
   - Expected: manager.sendMessage("hi") is false
   - Expected: manager.sendMessage("hi") is true
   - Expected: manager.sent[0] equals `user:hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should send user messages only when connected")
step("Verify: should send user messages only when connected")
# @req: REQ-TOOLS-Dire-001
step("Send message before and after connect")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
expect(manager.sendMessage("hi")).to_equal(false)
manager.connect()
expect(manager.sendMessage("hi")).to_equal(true)
expect(manager.sent[0]).to_equal("user:hi")
```

</details>

#### should send permission responses and interrupt when connected

- should send permission responses and interrupt when connected
- Verify: should send permission responses and interrupt when connected
- Send control response and interrupt
   - Expected: manager.sent[0] equals `control_response:success:req-1:allow:{"x":1}`
   - Expected: manager.sent[1] equals `control_response:success:req-2:deny:no`
   - Expected: manager.sent[2] equals `control_request:uuid:interrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should send permission responses and interrupt when connected")
step("Verify: should send permission responses and interrupt when connected")
# @req: REQ-TOOLS-Dire-001
step("Send control response and interrupt")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
manager.connect()
manager.respondToPermissionRequest("req-1", directPermissionAllow("{\"x\":1}"))
manager.respondToPermissionRequest("req-2", directPermissionDeny("no"))
manager.sendInterrupt()
expect(manager.sent[0]).to_equal("control_response:success:req-1:allow:{\"x\":1}")
expect(manager.sent[1]).to_equal("control_response:success:req-2:deny:no")
expect(manager.sent[2]).to_equal("control_request:uuid:interrupt")
```

</details>

#### should disconnect and expose source-backed helpers

- should disconnect and expose source-backed helpers
- Verify: should disconnect and expose source-backed helpers
- Disconnect and inspect helpers
   - Expected: manager.isConnected() is false
   - Expected: isStdoutMessage(parseDirectMessage("assistant||||x")) is true
   - Expected: shouldForwardSdkMessage(parseDirectMessage("keep_alive||||")) is false
   - Expected: directConnectManagerSourceLinesModeled() equals `213`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should disconnect and expose source-backed helpers")
step("Verify: should disconnect and expose source-backed helpers")
# @req: REQ-TOOLS-Dire-001
step("Disconnect and inspect helpers")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
manager.connect()
manager.onError()
manager.disconnect()
expect(manager.isConnected()).to_equal(false)
expect(manager.callbacks).to_contain("error:WebSocket connection error")
expect(manager.callbacks).to_contain("disconnected")
expect(isStdoutMessage(parseDirectMessage("assistant||||x"))).to_equal(true)
expect(shouldForwardSdkMessage(parseDirectMessage("keep_alive||||"))).to_equal(false)
expect(directConnectManagerSourceLinesModeled()).to_equal(213)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Dire-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d423b47dae6b01587083ed2a9796c7541b9205a9fce79984f24f8b7f617364bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d423b47dae6b01587083ed2a9796c7541b9205a9fce79984f24f8b7f617364bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d423b47dae6b01587083ed2a9796c7541b9205a9fce79984f24f8b7f617364bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/server/directConnectManager_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/server/directConnectManager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/server/directConnectManager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should connect with optional authorization header' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should connect with optional authorization header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse newline-delimited messages and forward SDK messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse newline-delimited messages and forward SDK messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route permission requests and reject unsupported subtypes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route permission requests and reject unsupported subtypes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should filter non-SDK stream and control messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should send user messages only when connected' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should send permission responses and interrupt when connected' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
