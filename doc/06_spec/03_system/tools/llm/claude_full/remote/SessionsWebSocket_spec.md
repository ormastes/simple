# Claude Full Sessions WebSocket

> Purpose: should connect to the session subscribe URL and open

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Sessions WebSocket

Purpose: should connect to the session subscribe URL and open

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should connect to the session subscribe URL and open
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Sessions WebSocket

Checks remote session websocket state, messages, sends, and reconnect policy.

## Scenarios

### Claude full SessionsWebSocket

#### should connect to the session subscribe URL and open

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should connect to the session subscribe URL and open
- Verify: should connect to the session subscribe URL and open
- Connect and open websocket
   - Expected: ws.state equals `connecting`
   - Expected: ws.sent[0] equals `connect:wss://api.anthropic.com/v1/sessions/ws/sess-1/subscribe?organization_... (full value in folded executable source)`
   - Expected: ws.isConnected() is true
   - Expected: ws.pingIntervalActive is true
   - Expected: ws.callbacks[0] equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should connect to the session subscribe URL and open")
step("Verify: should connect to the session subscribe URL and open")
# @req: REQ-TOOLS-Sess-001
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

- should parse and forward sessions messages
- Verify: should parse and forward sessions messages
- Handle typed messages and parse failures
   - Expected: ws.messages equals `["assistant:hello", "control_request:req"]`
   - Expected: ws.errors[0] equals `Failed to parse message: {bad`
   - Expected: isSessionsMessage(parseSessionsMessage("x:y")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse and forward sessions messages")
step("Verify: should parse and forward sessions messages")
# @req: REQ-TOOLS-Sess-001
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

- should stop reconnecting on permanent close code
- Verify: should stop reconnecting on permanent close code
- Close with unauthorized code
   - Expected: ws.state equals `closed`
   - Expected: ws.callbacks[1] equals `close`
   - Expected: ws.reconnectTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should stop reconnecting on permanent close code")
step("Verify: should stop reconnecting on permanent close code")
# @req: REQ-TOOLS-Sess-001
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

- should retry session-not-found closes with increasing delay
- Verify: should retry session-not-found closes with increasing delay
- Handle transient 4001 closes
   - Expected: ws.callbacks[1] equals `reconnecting`
   - Expected: ws.reconnectLabels[0] equals `4001 attempt 1/3:2000`
   - Expected: ws.callbacks[4] equals `close`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retry session-not-found closes with increasing delay")
step("Verify: should retry session-not-found closes with increasing delay")
# @req: REQ-TOOLS-Sess-001
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

- should reconnect transient connected closes up to max attempts
- Verify: should reconnect transient connected closes up to max attempts
- Handle normal transient close
   - Expected: ws.reconnectAttempts equals `1`
   - Expected: ws.reconnectLabels[0] equals `attempt 1/5:2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reconnect transient connected closes up to max attempts")
step("Verify: should reconnect transient connected closes up to max attempts")
# @req: REQ-TOOLS-Sess-001
step("Handle normal transient close")
val ws = SessionsWebSocket.new("sess", "org", "tok")
ws.connect("https://api")
ws.open()
ws.handleClose(1006)
expect(ws.reconnectAttempts).to_equal(1)  # oracle: value fixed by the spec contract
expect(ws.reconnectLabels[0]).to_equal("attempt 1/5:2000")
```

</details>

#### should guard sends by connection state and ping when connected

- should guard sends by connection state and ping when connected
- Verify: should guard sends by connection state and ping when connected
- Send control messages only while connected
   - Expected: ws.errors[0] equals `Cannot send: not connected`
   - Expected: ws.sent[1] equals `control_request:uuid:interrupt`
   - Expected: ws.sent[2] equals `control_response:ok`
   - Expected: ws.sent[3] equals `ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should guard sends by connection state and ping when connected")
step("Verify: should guard sends by connection state and ping when connected")
# @req: REQ-TOOLS-Sess-001
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

- should close and force reconnect with timer cleanup
- Verify: should close and force reconnect with timer cleanup
- Close then force reconnect
   - Expected: ws.state equals `closed`
   - Expected: ws.wsActive is false
   - Expected: ws.pingIntervalActive is false
   - Expected: ws.reconnectAttempts equals `0`
   - Expected: ws.sessionNotFoundRetries equals `0`
   - Expected: ws.reconnectLabels[0] equals `force:500`
   - Expected: maxReconnectAttempts() equals `5`
   - Expected: pingIntervalMs() equals `30000`
   - Expected: sessionsWebSocketSourceLinesModeled() equals `403`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should close and force reconnect with timer cleanup")
step("Verify: should close and force reconnect with timer cleanup")
# @req: REQ-TOOLS-Sess-001
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
expect(ws.reconnectAttempts).to_equal(0)  # oracle: value fixed by the spec contract
expect(ws.sessionNotFoundRetries).to_equal(0)  # oracle: value fixed by the spec contract
expect(ws.reconnectLabels[0]).to_equal("force:500")
expect(maxReconnectAttempts()).to_equal(5)  # oracle: value fixed by the spec contract
expect(pingIntervalMs()).to_equal(30000)  # oracle: value fixed by the spec contract
expect(sessionsWebSocketSourceLinesModeled()).to_equal(403)  # oracle: value fixed by the spec contract
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
- `REQ-TOOLS-Sess-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2079f55b6f682b04a5fc93e2b34d86a5821934a817bf32a8dec1d482ffd486b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2079f55b6f682b04a5fc93e2b34d86a5821934a817bf32a8dec1d482ffd486b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2079f55b6f682b04a5fc93e2b34d86a5821934a817bf32a8dec1d482ffd486b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should connect to the session subscribe URL and open' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should connect to the session subscribe URL and open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse and forward sessions messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse and forward sessions messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stop reconnecting on permanent close code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should stop reconnecting on permanent close code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retry session-not-found closes with increasing delay' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reconnect transient connected closes up to max attempts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/remote/SessionsWebSocket_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should guard sends by connection state and ping when connected' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
