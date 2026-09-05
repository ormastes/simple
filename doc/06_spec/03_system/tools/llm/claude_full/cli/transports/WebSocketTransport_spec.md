# Claude Full WebSocket Transport

> Checks connection state, reconnect policy, replay buffering, and keepalive behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full WebSocket Transport

Checks connection state, reconnect policy, replay buffering, and keepalive behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks connection state, reconnect policy, replay buffering, and keepalive behavior.

## Examples

The spec exercises disconnected buffering, server-confirmed replay eviction,
permanent close handling, token refresh on 4003, reconnect budget exhaustion,
sleep detection, and ping/pong health checks.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Scenarios

### Claude full WebSocketTransport

#### connects, opens, and records inbound data

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- connects, opens, and records inbound data
- Open a transport
   - Expected: transport.getStateLabel() equals `reconnecting`
   - Expected: transport.isConnectedStatus() is true
   - Expected: transport.reconnectAttempts equals `0`
   - Expected: transport.pingIntervalActive is true
   - Expected: transport.keepAliveIntervalActive is true
   - Expected: transport.lastActivityTime equals `1200`
   - Expected: transport.dataMessages equals `["hello"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("connects, opens, and records inbound data")
step("Open a transport")
val transport = webSocketTransportNew("wss://api.example/ws/s1", ["Authorization=old"], "s1")
transport.connect(1000)
expect(transport.getStateLabel()).to_equal("reconnecting")
transport.open(1100, "")
expect(transport.isConnectedStatus()).to_equal(true)
expect(transport.reconnectAttempts).to_equal(0)
expect(transport.pingIntervalActive).to_equal(true)
expect(transport.keepAliveIntervalActive).to_equal(true)
transport.receive("hello", 1200)
expect(transport.lastActivityTime).to_equal(1200)
expect(transport.dataMessages).to_equal(["hello"])
```

</details>

#### buffers uuid messages while disconnected and sends after open

- buffers uuid messages while disconnected and sends after open
- Write before connected, then replay
   - Expected: transport.sentLines.len() equals `0`
   - Expected: transport.messageBuffer.len() equals `2`
   - Expected: transport.lastSentId equals `m2`
   - Expected: transport.sentLines.len() equals `2`
   - Expected: transport.messageBuffer.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("buffers uuid messages while disconnected and sends after open")
step("Write before connected, then replay")
val transport = webSocketTransportNew("wss://api.example/ws/s1", [], "s1")
transport.write(webSocketMessage("assistant", "m1"))
transport.write(webSocketMessage("result", "m2"))
expect(transport.sentLines.len()).to_equal(0)
expect(transport.messageBuffer.len()).to_equal(2)
expect(transport.lastSentId).to_equal("m2")
transport.connect(1)
transport.open(2, "")
expect(transport.sentLines.len()).to_equal(2)
expect(transport.messageBuffer.len()).to_equal(2)
```

</details>

#### evicts server-confirmed buffered messages before replay

- evicts server-confirmed buffered messages before replay
- Server confirms through last request id
   - Expected: transport.messageBuffer.len() equals `1`
   - Expected: transport.messageBuffer[0].uuid equals `m3`
   - Expected: transport.sentLines equals `["{"type":"result","uuid":"m3"}\n"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evicts server-confirmed buffered messages before replay")
step("Server confirms through last request id")
val transport = webSocketTransportNew("wss://api.example/ws/s1", [], "s1")
transport.write(webSocketMessage("assistant", "m1"))
transport.write(webSocketMessage("assistant", "m2"))
transport.write(webSocketMessage("result", "m3"))
transport.connect(1)
transport.open(2, "m2")
expect(transport.messageBuffer.len()).to_equal(1)
expect(transport.messageBuffer[0].uuid).to_equal("m3")
expect(transport.sentLines).to_equal(["{\"type\":\"result\",\"uuid\":\"m3\"}\n"])
```

</details>

#### classifies close codes and reconnect settings

- classifies close codes and reconnect settings
- Permanent closes stop, ordinary closes reconnect
   - Expected: permanent.isClosedStatus() is true
   - Expected: permanent.closeCallbackCount equals `1`
   - Expected: reconnecting.getStateLabel() equals `reconnecting`
   - Expected: reconnecting.reconnectAttempts equals `1`
   - Expected: reconnecting.reconnectTimerActive is true
   - Expected: noAuto.isClosedStatus() is true
   - Expected: noAuto.closeCallbackCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies close codes and reconnect settings")
step("Permanent closes stop, ordinary closes reconnect")
val permanent = webSocketTransportNew("wss://api.example/ws/s1", [], "s1")
permanent.open(1, "")
permanent.handleConnectionError(4001, 2, "")
expect(permanent.isClosedStatus()).to_equal(true)
expect(permanent.closeCallbackCount).to_equal(1)
expect(permanent.diagnostics).to_contain("cli_websocket_permanent_close")

val reconnecting = webSocketTransportNew("wss://api.example/ws/s1", [], "s1")
reconnecting.open(10, "")
reconnecting.handleConnectionError(1006, 20, "")
expect(reconnecting.getStateLabel()).to_equal("reconnecting")
expect(reconnecting.reconnectAttempts).to_equal(1)
expect(reconnecting.reconnectTimerActive).to_equal(true)

val noAuto = WebSocketTransport.withOptions("wss://api.example/ws/s1", [], "s1", false, false)
noAuto.open(10, "")
noAuto.handleConnectionError(1006, 20, "")
expect(noAuto.isClosedStatus()).to_equal(true)
expect(noAuto.closeCallbackCount).to_equal(1)
```

</details>

#### refreshes 4003 authorization before reconnecting

- refreshes 4003 authorization before reconnecting
- Unauthorized close can refresh token
   - Expected: transport.getStateLabel() equals `reconnecting`
   - Expected: transport.headers equals `["Authorization=new"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refreshes 4003 authorization before reconnecting")
step("Unauthorized close can refresh token")
val transport = webSocketTransportNew("wss://api.example/ws/s1", ["Authorization=old"], "s1")
transport.open(10, "")
transport.handleConnectionError(4003, 20, "Authorization=new")
expect(transport.getStateLabel()).to_equal("reconnecting")
expect(transport.headers).to_equal(["Authorization=new"])
expect(transport.diagnostics).to_contain("cli_websocket_4003_token_refreshed")
```

</details>

#### handles sleep, exhausted reconnect budget, ping, and close

- handles sleep, exhausted reconnect budget, ping, and close
- Reconnect budget and health checks
   - Expected: transport.reconnectAttempts equals `1`
   - Expected: exhausted.isClosedStatus() is true
   - Expected: pinged.pongReceived is false
   - Expected: pinged.getStateLabel() equals `reconnecting`
   - Expected: pinged.getStateLabel() equals `closing`
   - Expected: pinged.pingIntervalActive is false
   - Expected: pinged.keepAliveIntervalActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles sleep, exhausted reconnect budget, ping, and close")
step("Reconnect budget and health checks")
val transport = webSocketTransportNew("wss://api.example/ws/s1", [], "s1")
transport.open(100, "")
transport.handleConnectionError(1006, 200, "")
transport.handleConnectionError(1006, 200 + sleepDetectionThresholdMs() + 1, "")
expect(transport.reconnectAttempts).to_equal(1)
expect(transport.diagnostics).to_contain("cli_websocket_sleep_detected")

val exhausted = webSocketTransportNew("wss://api.example/ws/s1", [], "s1")
exhausted.open(100, "")
exhausted.reconnectStartTime = 1
exhausted.handleConnectionError(1006, defaultReconnectGiveUpMs() + 2, "")
expect(exhausted.isClosedStatus()).to_equal(true)
expect(exhausted.diagnostics).to_contain("cli_websocket_reconnect_exhausted")

val pinged = webSocketTransportNew("wss://api.example/ws/s1", [], "s1")
pinged.open(10, "")
pinged.tickPing(1000)
expect(pinged.pongReceived).to_equal(false)
pinged.tickPing(1000)
expect(pinged.getStateLabel()).to_equal("reconnecting")
expect(pinged.diagnostics).to_contain("cli_websocket_pong_timeout")
pinged.close()
expect(pinged.getStateLabel()).to_equal("closing")
expect(pinged.pingIntervalActive).to_equal(false)
expect(pinged.keepAliveIntervalActive).to_equal(false)
```

</details>

#### exports source-backed constants and labels

- exports source-backed constants and labels
- Pin constants and modeled source coverage
   - Expected: getControlMessageDetailLabel(control) equals ` subtype=can_use_tool request_id=r1 tool=Bash`
   - Expected: keepAliveFrame() equals `{"type":"keep_alive"}\n`
   - Expected: defaultMaxBufferSize() equals `1000`
   - Expected: defaultBaseReconnectDelayMs() equals `1000`
   - Expected: defaultMaxReconnectDelayMs() equals `30000`
   - Expected: defaultReconnectGiveUpMs() equals `600000`
   - Expected: defaultPingIntervalMs() equals `10000`
   - Expected: defaultKeepaliveIntervalMs() equals `300000`
   - Expected: sleepDetectionThresholdMs() equals `60000`
   - Expected: reconnectDelayMs(1, 25) equals `1250`
   - Expected: reconnectDelayMs(6, -25) equals `22500`
   - Expected: isPermanentCloseCode(1002) is true
   - Expected: isPermanentCloseCode(1006) is false
   - Expected: webSocketTransportSourceLinesModeled() equals `660`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants and labels")
step("Pin constants and modeled source coverage")
val control = WebSocketMessage.controlRequest("c1", "can_use_tool", "r1", "Bash")
expect(getControlMessageDetailLabel(control)).to_equal(" subtype=can_use_tool request_id=r1 tool=Bash")
expect(keepAliveFrame()).to_equal("{\"type\":\"keep_alive\"}\n")
expect(defaultMaxBufferSize()).to_equal(1000)
expect(defaultBaseReconnectDelayMs()).to_equal(1000)
expect(defaultMaxReconnectDelayMs()).to_equal(30000)
expect(defaultReconnectGiveUpMs()).to_equal(600000)
expect(defaultPingIntervalMs()).to_equal(10000)
expect(defaultKeepaliveIntervalMs()).to_equal(300000)
expect(sleepDetectionThresholdMs()).to_equal(60000)
expect(reconnectDelayMs(1, 25)).to_equal(1250)
expect(reconnectDelayMs(6, -25)).to_equal(22500)
expect(isPermanentCloseCode(1002)).to_equal(true)
expect(isPermanentCloseCode(1006)).to_equal(false)
expect(webSocketTransportSourceLinesModeled()).to_equal(660)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5d33e753b888111586e412f4f0d0b349927ea7ab86518aa8ba64235958c90371`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d33e753b888111586e412f4f0d0b349927ea7ab86518aa8ba64235958c90371`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d33e753b888111586e412f4f0d0b349927ea7ab86518aa8ba64235958c90371`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects, opens, and records inbound data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'buffers uuid messages while disconnected and sends after open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/WebSocketTransport_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evicts server-confirmed buffered messages before replay' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
