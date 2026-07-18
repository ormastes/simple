# Claude Full Remote Session Manager

> Checks remote session websocket lifecycle and permission flow.

<!-- sdn-diagram:id=RemoteSessionManager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=RemoteSessionManager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

RemoteSessionManager_spec -> std
RemoteSessionManager_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=RemoteSessionManager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Remote Session Manager

Checks remote session websocket lifecycle and permission flow.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/remote/RemoteSessionManager_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks remote session websocket lifecycle and permission flow.

## Scenarios

### Claude full RemoteSessionManager

#### should create configs and connect websocket state

- Create manager and connect
- manager connect
   - Expected: manager.isConnected() is true
   - Expected: manager.callbacks[0] equals `connected`
   - Expected: manager.getSessionId() equals `sess-1`
   - Expected: manager.config.hasInitialPrompt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Handle SDK and control response messages
- manager handleMessage
- manager handleMessage
   - Expected: manager.receivedMessages equals `["assistant:hello"]`
   - Expected: manager.callbacks equals `["control_response"]`
   - Expected: isSDKMessage(remoteMessage("assistant", "")) is true
   - Expected: isSDKMessage(remoteMessage("control_request", "")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Receive can_use_tool then allow it
- manager handleMessage
   - Expected: manager.permissionRequests[0] equals `req-1:Bash`
   - Expected: manager.pendingPermissionRequestIds equals `["req-1"]`
- manager respondToPermissionRequest
   - Expected: manager.pendingPermissionRequestIds.len() equals `0`
   - Expected: manager.sentControlResponses[0] equals `success:req-1:allow:{"cmd":"ls"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Receive can_use_tool then allow it")
val manager = RemoteSessionManager.new(createRemoteSessionConfig("sess", "token", "org", false, false))
manager.handleMessage(permissionRequest("req-1", "tool-1", "Bash"))
expect(manager.permissionRequests[0]).to_equal("req-1:Bash")
expect(manager.pendingPermissionRequestIds).to_equal(["req-1"])
manager.respondToPermissionRequest("req-1", remotePermissionAllow("{\"cmd\":\"ls\"}"))
expect(manager.pendingPermissionRequestIds.len()).to_equal(0)
expect(manager.sentControlResponses[0]).to_equal("success:req-1:allow:{\"cmd\":\"ls\"}")
```

</details>

#### should send deny responses and reject missing request ids

- Deny one request and try a missing request
- manager handleMessage
- manager respondToPermissionRequest
- manager respondToPermissionRequest
   - Expected: manager.sentControlResponses[0] equals `success:req-2:deny:no`
   - Expected: manager.errors[0] equals `No pending permission request with ID: missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Cancel a pending permission request
- manager handleMessage
- manager handleMessage
   - Expected: manager.permissionCancelled[0] equals `req-3:tool-3`
   - Expected: manager.pendingPermissionRequestIds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cancel a pending permission request")
val manager = RemoteSessionManager.new(createRemoteSessionConfig("sess", "token", "org", false, false))
manager.handleMessage(permissionRequest("req-3", "tool-3", "Read"))
manager.handleMessage(controlCancel("req-3"))
expect(manager.permissionCancelled[0]).to_equal("req-3:tool-3")
expect(manager.pendingPermissionRequestIds.len()).to_equal(0)
```

</details>

#### should handle unsupported control requests and message send failures

- Send unsupported control error and failed remote message
- manager handleMessage
   - Expected: manager.sentControlResponses[0] equals `error:req-4:Unsupported control request subtype: unknown`
   - Expected: manager.sendMessage("hi", "uuid-1", false) is false
   - Expected: manager.errors[0] equals `Failed to send message to session sess`
   - Expected: manager.config.viewerOnly is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Drive lifecycle helpers
- manager connect
- manager cancelSession
- manager reconnect
   - Expected: manager.sentControlRequests[0] equals `interrupt`
   - Expected: manager.callbacks[1] equals `reconnecting`
- manager handleMessage
- manager disconnect
   - Expected: manager.isConnected() is false
   - Expected: manager.pendingPermissionRequestIds.len() equals `0`
   - Expected: remoteSessionManagerSourceLinesModeled() equals `343`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(manager.pendingPermissionRequestIds.len()).to_equal(0)
expect(remoteSessionManagerSourceLinesModeled()).to_equal(343)
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
