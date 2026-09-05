# Claude Full Direct Connect Session Manager

> Checks direct-connect websocket message filtering and outbound control messages.

<!-- sdn-diagram:id=directConnectManager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=directConnectManager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

directConnectManager_spec -> std
directConnectManager_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=directConnectManager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Direct Connect Session Manager

Checks direct-connect websocket message filtering and outbound control messages.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/server/directConnectManager_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks direct-connect websocket message filtering and outbound control messages.

## Scenarios

### Claude full DirectConnectSessionManager

#### should connect with optional authorization header

- Connect a direct websocket
- manager connect
   - Expected: manager.isConnected() is true
   - Expected: manager.authorizationHeader equals `Bearer tok`
   - Expected: manager.callbacks[0] equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Connect a direct websocket")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", "tok"))
manager.connect()
expect(manager.isConnected()).to_equal(true)
expect(manager.authorizationHeader).to_equal("Bearer tok")
expect(manager.callbacks[0]).to_equal("connected")
```

</details>

#### should parse newline-delimited messages and forward SDK messages

- Handle multiple websocket lines
- manager connect
- manager handleMessageBatch
   - Expected: manager.messages equals `["assistant:hello", "result:ok"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle multiple websocket lines")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
manager.connect()
manager.handleMessageBatch("assistant||||hello\n\nresult||||ok\n")
expect(manager.messages).to_equal(["assistant:hello", "result:ok"])
```

</details>

#### should route permission requests and reject unsupported subtypes

- Handle control requests
- manager connect
- manager handleMessageBatch
   - Expected: manager.permissionRequests[0] equals `req-1:Bash`
   - Expected: manager.sent[0] equals `control_response:error:req-2:Unsupported control request subtype: unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle control requests")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
manager.connect()
manager.handleMessageBatch("control_request|can_use_tool|req-1|Bash|\ncontrol_request|unknown|req-2||\n")
expect(manager.permissionRequests[0]).to_equal("req-1:Bash")
expect(manager.sent[0]).to_equal("control_response:error:req-2:Unsupported control request subtype: unknown")
```

</details>

#### should filter non-SDK stream and control messages

- Handle messages that should not be forwarded
- manager connect
- manager handleMessageBatch
   - Expected: manager.messages.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle messages that should not be forwarded")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
manager.connect()
manager.handleMessageBatch("control_response||||ack\nkeep_alive||||\ncontrol_cancel_request||||\nstreamlined_text||||x\nsystem|post_turn_summary|||summary\n")
expect(manager.messages.len()).to_equal(0)
```

</details>

#### should send user messages only when connected

- Send message before and after connect
   - Expected: manager.sendMessage("hi") is false
- manager connect
   - Expected: manager.sendMessage("hi") is true
   - Expected: manager.sent[0] equals `user:hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send message before and after connect")
val manager = DirectConnectSessionManager.new(directConnectConfig("https://s", "sess", "ws://s", ""))
expect(manager.sendMessage("hi")).to_equal(false)
manager.connect()
expect(manager.sendMessage("hi")).to_equal(true)
expect(manager.sent[0]).to_equal("user:hi")
```

</details>

#### should send permission responses and interrupt when connected

- Send control response and interrupt
- manager connect
- manager respondToPermissionRequest
- manager respondToPermissionRequest
- manager sendInterrupt
   - Expected: manager.sent[0] equals `control_response:success:req-1:allow:{"x":1}`
   - Expected: manager.sent[1] equals `control_response:success:req-2:deny:no`
   - Expected: manager.sent[2] equals `control_request:uuid:interrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Disconnect and inspect helpers
- manager connect
- manager onError
- manager disconnect
   - Expected: manager.isConnected() is false
   - Expected: isStdoutMessage(parseDirectMessage("assistant||||x")) is true
   - Expected: shouldForwardSdkMessage(parseDirectMessage("keep_alive||||")) is false
   - Expected: directConnectManagerSourceLinesModeled() equals `213`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(directConnectManagerSourceLinesModeled()).to_equal(213)
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
