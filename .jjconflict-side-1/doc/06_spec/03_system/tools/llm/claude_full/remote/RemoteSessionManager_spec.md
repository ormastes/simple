# Claude Full Remote Session Manager

> Purpose: should create configs and connect websocket state

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Remote Session Manager

Purpose: should create configs and connect websocket state

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should create configs and connect websocket state
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Remote Session Manager

Checks remote session websocket lifecycle and permission flow.

## Scenarios

### Claude full RemoteSessionManager

#### should create configs and connect websocket state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create configs and connect websocket state
- Verify: should create configs and connect websocket state
- Create manager and connect
   - Expected: manager.isConnected() is true
   - Expected: manager.callbacks[0] equals `connected`
   - Expected: manager.getSessionId() equals `sess-1`
   - Expected: manager.config.hasInitialPrompt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create configs and connect websocket state")
step("Verify: should create configs and connect websocket state")
# @req: REQ-TOOLS-Remo-001
step("Create manager and connect")
val config = createRemoteSessionConfig("sess-1", "token", "org-1", true, false)
val manager = RemoteSessionManager.new(config)
manager.connect()
expect(manager.isConnected()).to_equal(true)
expect(manager.callbacks[0]).to_equal("connected")
expect(manager.getSessionId()).to_equal("sess-1")
expect(manager.config.hasInitialPrompt).to_equal(true)
```

</details>

#### should forward SDK messages and ignore control responses

- should forward SDK messages and ignore control responses
- Verify: should forward SDK messages and ignore control responses
- Handle SDK and control response messages
   - Expected: manager.receivedMessages equals `["assistant:hello"]`
   - Expected: manager.callbacks equals `["control_response"]`
   - Expected: isSDKMessage(remoteMessage("assistant", "")) is true
   - Expected: isSDKMessage(remoteMessage("control_request", "")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should forward SDK messages and ignore control responses")
step("Verify: should forward SDK messages and ignore control responses")
# @req: REQ-TOOLS-Remo-001
step("Handle SDK and control response messages")
val manager = RemoteSessionManager.new(createRemoteSessionConfig("sess", "token", "org", false, false))
manager.handleMessage(remoteMessage("assistant", "hello"))
manager.handleMessage(remoteMessage("control_response", "ack"))
expect(manager.receivedMessages).to_equal(["assistant:hello"])
expect(manager.callbacks).to_equal(["control_response"])
expect(isSDKMessage(remoteMessage("assistant", ""))).to_equal(true)
expect(isSDKMessage(remoteMessage("control_request", ""))).to_equal(false)
```

</details>

#### should store permission requests and send allow responses

- should store permission requests and send allow responses
- Verify: should store permission requests and send allow responses
- Receive can_use_tool then allow it
   - Expected: manager.permissionRequests[0] equals `req-1:Bash`
   - Expected: manager.pendingPermissionRequestIds equals `["req-1"]`
   - Expected: manager.pendingPermissionRequestIds.len() equals `0`
   - Expected: manager.sentControlResponses[0] equals `success:req-1:allow:{"cmd":"ls"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should store permission requests and send allow responses")
step("Verify: should store permission requests and send allow responses")
# @req: REQ-TOOLS-Remo-001
step("Receive can_use_tool then allow it")
val manager = RemoteSessionManager.new(createRemoteSessionConfig("sess", "token", "org", false, false))
manager.handleMessage(permissionRequest("req-1", "tool-1", "Bash"))
expect(manager.permissionRequests[0]).to_equal("req-1:Bash")
expect(manager.pendingPermissionRequestIds).to_equal(["req-1"])
manager.respondToPermissionRequest("req-1", remotePermissionAllow("{\"cmd\":\"ls\"}"))
expect(manager.pendingPermissionRequestIds.len()).to_equal(0)  # oracle: value fixed by the spec contract
expect(manager.sentControlResponses[0]).to_equal("success:req-1:allow:{\"cmd\":\"ls\"}")
```

</details>

#### should send deny responses and reject missing request ids

- should send deny responses and reject missing request ids
- Verify: should send deny responses and reject missing request ids
- Deny one request and try a missing request
   - Expected: manager.sentControlResponses[0] equals `success:req-2:deny:no`
   - Expected: manager.errors[0] equals `No pending permission request with ID: missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should send deny responses and reject missing request ids")
step("Verify: should send deny responses and reject missing request ids")
# @req: REQ-TOOLS-Remo-001
step("Deny one request and try a missing request")
val manager = RemoteSessionManager.new(createRemoteSessionConfig("sess", "token", "org", false, false))
manager.handleMessage(permissionRequest("req-2", "tool-2", "Edit"))
manager.respondToPermissionRequest("req-2", remotePermissionDeny("no"))
manager.respondToPermissionRequest("missing", remotePermissionDeny("no"))
expect(manager.sentControlResponses[0]).to_equal("success:req-2:deny:no")
expect(manager.errors[0]).to_equal("No pending permission request with ID: missing")
```

</details>

#### should cancel pending permission requests with tool use id

- should cancel pending permission requests with tool use id
- Verify: should cancel pending permission requests with tool use id
- Cancel a pending permission request
   - Expected: manager.permissionCancelled[0] equals `req-3:tool-3`
   - Expected: manager.pendingPermissionRequestIds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cancel pending permission requests with tool use id")
step("Verify: should cancel pending permission requests with tool use id")
# @req: REQ-TOOLS-Remo-001
step("Cancel a pending permission request")
val manager = RemoteSessionManager.new(createRemoteSessionConfig("sess", "token", "org", false, false))
manager.handleMessage(permissionRequest("req-3", "tool-3", "Read"))
manager.handleMessage(controlCancel("req-3"))
expect(manager.permissionCancelled[0]).to_equal("req-3:tool-3")
expect(manager.pendingPermissionRequestIds.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should handle unsupported control requests and message send failures

- should handle unsupported control requests and message send failures
- Verify: should handle unsupported control requests and message send failures
- Send unsupported control error and failed remote message
   - Expected: manager.sentControlResponses[0] equals `error:req-4:Unsupported control request subtype: unknown`
   - Expected: manager.sendMessage("hi", "uuid-1", false) is false
   - Expected: manager.errors[0] equals `Failed to send message to session sess`
   - Expected: manager.config.viewerOnly is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle unsupported control requests and message send failures")
step("Verify: should handle unsupported control requests and message send failures")
# @req: REQ-TOOLS-Remo-001
step("Send unsupported control error and failed remote message")
val manager = RemoteSessionManager.new(createRemoteSessionConfig("sess", "token", "org", false, true))
manager.handleMessage(unsupportedControlRequest("req-4", "unknown"))
expect(manager.sentControlResponses[0]).to_equal("error:req-4:Unsupported control request subtype: unknown")
expect(manager.sendMessage("hi", "uuid-1", false)).to_equal(false)
expect(manager.errors[0]).to_equal("Failed to send message to session sess")
expect(manager.config.viewerOnly).to_equal(true)
```

</details>

#### should interrupt, reconnect, disconnect, and expose source coverage

- should interrupt, reconnect, disconnect, and expose source coverage
- Verify: should interrupt, reconnect, disconnect, and expose source coverage
- Drive lifecycle helpers
   - Expected: manager.sentControlRequests[0] equals `interrupt`
   - Expected: manager.callbacks[1] equals `reconnecting`
   - Expected: manager.isConnected() is false
   - Expected: manager.pendingPermissionRequestIds.len() equals `0`
   - Expected: remoteSessionManagerSourceLinesModeled() equals `343`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should interrupt, reconnect, disconnect, and expose source coverage")
step("Verify: should interrupt, reconnect, disconnect, and expose source coverage")
# @req: REQ-TOOLS-Remo-001
step("Drive lifecycle helpers")
val manager = RemoteSessionManager.new(createRemoteSessionConfig("sess", "token", "org", false, false))
manager.connect()
manager.cancelSession()
manager.reconnect()
expect(manager.sentControlRequests[0]).to_equal("interrupt")
expect(manager.callbacks[1]).to_equal("reconnecting")
manager.handleMessage(permissionRequest("req-5", "tool-5", "Write"))
manager.disconnect()
expect(manager.isConnected()).to_equal(false)
expect(manager.pendingPermissionRequestIds.len()).to_equal(0)  # oracle: value fixed by the spec contract
expect(remoteSessionManagerSourceLinesModeled()).to_equal(343)  # oracle: value fixed by the spec contract
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
- `REQ-TOOLS-Remo-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `142666ddc16c4968dcde27f8bd979b65b010b1d69b6d98126443da7f2dc386b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `142666ddc16c4968dcde27f8bd979b65b010b1d69b6d98126443da7f2dc386b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `142666ddc16c4968dcde27f8bd979b65b010b1d69b6d98126443da7f2dc386b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create configs and connect websocket state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create configs and connect websocket state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should forward SDK messages and ignore control responses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should forward SDK messages and ignore control responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should store permission requests and send allow responses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should store permission requests and send allow responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should send deny responses and reject missing request ids' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cancel pending permission requests with tool use id' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle unsupported control requests and message send failures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
