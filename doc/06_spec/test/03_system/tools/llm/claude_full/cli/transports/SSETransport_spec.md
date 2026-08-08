# Claude Full SSE Transport

> Checks SSE frame parsing, sequence resume state, reconnects, writes, and close.

<!-- sdn-diagram:id=SSETransport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=SSETransport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

SSETransport_spec -> std
SSETransport_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=SSETransport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full SSE Transport

Checks SSE frame parsing, sequence resume state, reconnects, writes, and close.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks SSE frame parsing, sequence resume state, reconnects, writes, and close.

## Scenarios

### Claude full SSETransport

#### should parse complete frames and keep incomplete remainder

- Parse comment, multi-data, and partial SSE input
   - Expected: parsed.frames.len() equals `2`
   - Expected: parsed.frames[0].comment is true
   - Expected: parsed.frames[1].id equals `7`
   - Expected: parsed.frames[1].data equals `7|assistant|hello\nworld`
   - Expected: parsed.remaining equals `id: `


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse comment, multi-data, and partial SSE input")
val parsed = parseSSEFrames(":keepalive\n\nid: 7\nevent: client_event\ndata: 7|assistant|hello\ndata: world\n\nid: ")
expect(parsed.frames.len()).to_equal(2)
expect(parsed.frames[0].comment).to_equal(true)
expect(parsed.frames[1].id).to_equal("7")
expect(parsed.frames[1].data).to_equal("7|assistant|hello\nworld")
expect(parsed.remaining).to_equal("id: ")
```

</details>

#### should connect, read client events, and update sequence high-water mark

- Connect and process one client_event frame
- transport connect
- transport readText
   - Expected: transport.isConnectedStatus() is true
   - Expected: transport.getLastSequenceNum() equals `5`
   - Expected: transport.dataLines[0] equals `payload\n`
   - Expected: transport.eventLog[0].payload_type equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Connect and process one client_event frame")
val transport = SSETransport.new("https://api/session/s1/events/stream", "s1", 3)
transport.connect(200, true)
transport.readText("id: 5\nevent: client_event\ndata: 5|assistant|payload\n\n")
expect(transport.isConnectedStatus()).to_equal(true)
expect(transport.getLastSequenceNum()).to_equal(5)
expect(transport.dataLines[0]).to_equal("payload\n")
expect(transport.eventLog[0].payload_type).to_equal("assistant")
```

</details>

#### should diagnose duplicate, unexpected, and missing-event frames

- Read frames that should not be delivered as payload
- transport connect
- transport readText
   - Expected: transport.getLastSequenceNum() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read frames that should not be delivered as payload")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
transport.connect(200, true)
transport.readText("id: 4\nevent: other\ndata: x\n\nid: 4\ndata: y\n\n")
expect(transport.getLastSequenceNum()).to_equal(4)
expect(transport.diagnostics).to_contain("cli_sse_unexpected_event_type")
expect(transport.diagnostics).to_contain("cli_sse_duplicate_sequence")
expect(transport.diagnostics).to_contain("cli_sse_frame_missing_event_field")
```

</details>

#### should close permanently on permanent connect HTTP status

- Connect with unauthorized response
- transport connect
   - Expected: transport.isClosedStatus() is true
   - Expected: transport.closeCodes[0] equals `401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Connect with unauthorized response")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
transport.connect(401, true)
expect(transport.isClosedStatus()).to_equal(true)
expect(transport.closeCodes[0]).to_equal(401)
```

</details>

#### should schedule reconnects and exhaust the reconnect budget

- Handle transient errors then budget exhaustion
- transport connect
   - Expected: transport.state equals `reconnecting`
   - Expected: transport.reconnectAttempts equals `1`
   - Expected: transport.reconnectTimerActive is true
- transport handleConnectionError
   - Expected: transport.isClosedStatus() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Handle transient errors then budget exhaustion")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
transport.connect(500, true)
expect(transport.state).to_equal("reconnecting")
expect(transport.reconnectAttempts).to_equal(1)
expect(transport.reconnectTimerActive).to_equal(true)
transport.handleConnectionError(sseReconnectGiveUpMs())
expect(transport.isClosedStatus()).to_equal(true)
```

</details>

#### should reset liveness and reconnect on timeout

- Trigger liveness timeout
- transport connect
   - Expected: transport.livenessTimerActive is true
- transport onLivenessTimeout
   - Expected: transport.state equals `reconnecting`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Trigger liveness timeout")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
transport.connect(200, true)
expect(transport.livenessTimerActive).to_equal(true)
transport.onLivenessTimeout()
expect(transport.state).to_equal("reconnecting")
expect(transport.diagnostics).to_contain("cli_sse_liveness_timeout")
```

</details>

#### should classify post writes by auth and status

- Write with missing auth, permanent error, retry, then success
   - Expected: transport.write("assistant", false, [200]) equals `0`
   - Expected: transport.write("assistant", true, [400]) equals `1`
   - Expected: transport.write("assistant", true, [500, 429, 201]) equals `3`
   - Expected: transport.postedMessages[0] equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write with missing auth, permanent error, retry, then success")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
expect(transport.write("assistant", false, [200])).to_equal(0)
expect(transport.write("assistant", true, [400])).to_equal(1)
expect(transport.write("assistant", true, [500, 429, 201])).to_equal(3)
expect(transport.postedMessages[0]).to_equal("assistant")
expect(transport.diagnostics).to_contain("cli_sse_post_no_token")
expect(transport.diagnostics).to_contain("cli_sse_post_client_error")
```

</details>

#### should convert URLs, expose constants, and close timers

- Pin URL and timeout contract
   - Expected: transport.postUrl equals `https://api.example.com/v2/session_ingress/session/s1/events`
- transport connect
- transport close
   - Expected: transport.state equals `closing`
   - Expected: transport.reconnectTimerActive is false
   - Expected: transport.livenessTimerActive is false
   - Expected: reconnectDelayMs(6) equals `30000`
   - Expected: postDelayMs(5) equals `8000`
   - Expected: sseLivenessTimeoutMs() equals `45000`
   - Expected: ssePostMaxRetries() equals `10`
   - Expected: sseTransportSourceLinesModeled() equals `710`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin URL and timeout contract")
val transport = SSETransport.new("https://api.example.com/v2/session_ingress/session/s1/events/stream?ignored=1", "", 0)
expect(transport.postUrl).to_equal("https://api.example.com/v2/session_ingress/session/s1/events")
transport.connect(200, true)
transport.reconnectTimerActive = true
transport.close()
expect(transport.state).to_equal("closing")
expect(transport.reconnectTimerActive).to_equal(false)
expect(transport.livenessTimerActive).to_equal(false)
expect(reconnectDelayMs(6)).to_equal(30000)
expect(postDelayMs(5)).to_equal(8000)
expect(sseLivenessTimeoutMs()).to_equal(45000)
expect(ssePostMaxRetries()).to_equal(10)
expect(sseTransportSourceLinesModeled()).to_equal(710)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
