# Claude Full Sessions WebSocket

> Checks remote session websocket state, messages, sends, and reconnect policy.

<!-- sdn-diagram:id=SessionsWebSocket_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=SessionsWebSocket_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

SessionsWebSocket_spec -> std
SessionsWebSocket_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=SessionsWebSocket_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Sessions WebSocket

Checks remote session websocket state, messages, sends, and reconnect policy.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks remote session websocket state, messages, sends, and reconnect policy.

## Scenarios

### Claude full SessionsWebSocket

#### should connect to the session subscribe URL and open

- Connect and open websocket
- ws connect
   - Expected: ws.state equals `connecting`
   - Expected: ws.sent[0] equals `connect:wss://api.anthropic.com/v1/sessions/ws/sess-1/subscribe?organization_... (full value in folded executable source)`
- ws open
   - Expected: ws.isConnected() is true
   - Expected: ws.pingIntervalActive is true
   - Expected: ws.callbacks[0] equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Connect and open websocket")
val ws = SessionsWebSocket.new("sess-1", "org-1", "tok")
ws.connect("https://api.anthropic.com")
expect(ws.state).to_equal("connecting")
expect(ws.sent[0]).to_equal("connect:wss://api.anthropic.com/v1/sessions/ws/sess-1/subscribe?organization_uuid=org-1:Bearer tok")
ws.open()
expect(ws.isConnected()).to_equal(true)
expect(ws.pingIntervalActive).to_equal(true)
expect(ws.callbacks[0]).to_equal("connected")
```

</details>

#### should parse and forward sessions messages

- Handle typed messages and parse failures
- ws handleMessage
- ws handleMessage
- ws handleParseError
   - Expected: ws.messages equals `["assistant:hello", "control_request:req"]`
   - Expected: ws.errors[0] equals `Failed to parse message: {bad`
   - Expected: isSessionsMessage(parseSessionsMessage("x:y")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle typed messages and parse failures")
val ws = SessionsWebSocket.new("sess", "org", "tok")
ws.handleMessage("assistant:hello")
ws.handleMessage("control_request:req")
ws.handleParseError("{bad")
expect(ws.messages).to_equal(["assistant:hello", "control_request:req"])
expect(ws.errors[0]).to_equal("Failed to parse message: {bad")
expect(isSessionsMessage(parseSessionsMessage("x:y"))).to_equal(true)
```

</details>

#### should stop reconnecting on permanent close code

- Close with unauthorized code
- ws connect
- ws open
- ws handleClose
   - Expected: ws.state equals `closed`
   - Expected: ws.callbacks[1] equals `close`
   - Expected: ws.reconnectTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close with unauthorized code")
val ws = SessionsWebSocket.new("sess", "org", "tok")
ws.connect("https://api")
ws.open()
ws.handleClose(4003)
expect(ws.state).to_equal("closed")
expect(ws.callbacks[1]).to_equal("close")
expect(ws.reconnectTimerActive).to_equal(false)
```

</details>

#### should retry session-not-found closes with increasing delay

- Handle transient 4001 closes
- ws connect
- ws open
- ws handleClose
   - Expected: ws.callbacks[1] equals `reconnecting`
   - Expected: ws.reconnectLabels[0] equals `4001 attempt 1/3:2000`
- ws handleClose
- ws handleClose
- ws handleClose
   - Expected: ws.callbacks[4] equals `close`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle transient 4001 closes")
val ws = SessionsWebSocket.new("sess", "org", "tok")
ws.connect("https://api")
ws.open()
ws.handleClose(4001)
expect(ws.callbacks[1]).to_equal("reconnecting")
expect(ws.reconnectLabels[0]).to_equal("4001 attempt 1/3:2000")
ws.state = "connected"
ws.handleClose(4001)
ws.state = "connected"
ws.handleClose(4001)
ws.state = "connected"
ws.handleClose(4001)
expect(ws.callbacks[4]).to_equal("close")
```

</details>

#### should reconnect transient connected closes up to max attempts

- Handle normal transient close
- ws connect
- ws open
- ws handleClose
   - Expected: ws.reconnectAttempts equals `1`
   - Expected: ws.reconnectLabels[0] equals `attempt 1/5:2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle normal transient close")
val ws = SessionsWebSocket.new("sess", "org", "tok")
ws.connect("https://api")
ws.open()
ws.handleClose(1006)
expect(ws.reconnectAttempts).to_equal(1)
expect(ws.reconnectLabels[0]).to_equal("attempt 1/5:2000")
```

</details>

#### should guard sends by connection state and ping when connected

- Send control messages only while connected
- ws sendControlRequest
   - Expected: ws.errors[0] equals `Cannot send: not connected`
- ws connect
- ws open
- ws sendControlRequest
- ws sendControlResponse
- ws ping
   - Expected: ws.sent[1] equals `control_request:uuid:interrupt`
   - Expected: ws.sent[2] equals `control_response:ok`
   - Expected: ws.sent[3] equals `ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send control messages only while connected")
val ws = SessionsWebSocket.new("sess", "org", "tok")
ws.sendControlRequest("interrupt")
expect(ws.errors[0]).to_equal("Cannot send: not connected")
ws.connect("https://api")
ws.open()
ws.sendControlRequest("interrupt")
ws.sendControlResponse("ok")
ws.ping()
expect(ws.sent[1]).to_equal("control_request:uuid:interrupt")
expect(ws.sent[2]).to_equal("control_response:ok")
expect(ws.sent[3]).to_equal("ping")
```

</details>

#### should close and force reconnect with timer cleanup

- Close then force reconnect
- ws connect
- ws open
- ws close
   - Expected: ws.state equals `closed`
   - Expected: ws.wsActive is false
   - Expected: ws.pingIntervalActive is false
- ws reconnect
   - Expected: ws.reconnectAttempts equals `0`
   - Expected: ws.sessionNotFoundRetries equals `0`
   - Expected: ws.reconnectLabels[0] equals `force:500`
   - Expected: maxReconnectAttempts() equals `5`
   - Expected: pingIntervalMs() equals `30000`
   - Expected: sessionsWebSocketSourceLinesModeled() equals `403`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close then force reconnect")
val ws = SessionsWebSocket.new("sess", "org", "tok")
ws.connect("https://api")
ws.open()
ws.close()
expect(ws.state).to_equal("closed")
expect(ws.wsActive).to_equal(false)
expect(ws.pingIntervalActive).to_equal(false)
ws.reconnectAttempts = 3
ws.sessionNotFoundRetries = 2
ws.reconnect()
expect(ws.reconnectAttempts).to_equal(0)
expect(ws.sessionNotFoundRetries).to_equal(0)
expect(ws.reconnectLabels[0]).to_equal("force:500")
expect(maxReconnectAttempts()).to_equal(5)
expect(pingIntervalMs()).to_equal(30000)
expect(sessionsWebSocketSourceLinesModeled()).to_equal(403)
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
