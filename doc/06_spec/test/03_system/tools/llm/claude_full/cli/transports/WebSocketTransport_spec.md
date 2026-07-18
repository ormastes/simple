# Claude Full WebSocket Transport

> Checks connection state, reconnect policy, replay buffering, and keepalive behavior.

<!-- sdn-diagram:id=WebSocketTransport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=WebSocketTransport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

WebSocketTransport_spec -> std
WebSocketTransport_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=WebSocketTransport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
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

- Open a transport
- transport connect
   - Expected: transport.getStateLabel() equals `reconnecting`
- transport open
   - Expected: transport.isConnectedStatus() is true
   - Expected: transport.reconnectAttempts equals `0`
   - Expected: transport.pingIntervalActive is true
   - Expected: transport.keepAliveIntervalActive is true
- transport receive
   - Expected: transport.lastActivityTime equals `1200`
   - Expected: transport.dataMessages equals `["hello"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Write before connected, then replay
- transport write
- transport write
   - Expected: transport.sentLines.len() equals `0`
   - Expected: transport.messageBuffer.len() equals `2`
   - Expected: transport.lastSentId equals `m2`
- transport connect
- transport open
   - Expected: transport.sentLines.len() equals `2`
   - Expected: transport.messageBuffer.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Server confirms through last request id
- transport write
- transport write
- transport write
- transport connect
- transport open
   - Expected: transport.messageBuffer.len() equals `1`
   - Expected: transport.messageBuffer[0].uuid equals `m3`
   - Expected: transport.sentLines equals `["{"type":"result","uuid":"m3"}\n"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Permanent closes stop, ordinary closes reconnect
- permanent open
- permanent handleConnectionError
   - Expected: permanent.isClosedStatus() is true
   - Expected: permanent.closeCallbackCount equals `1`
- reconnecting open
- reconnecting handleConnectionError
   - Expected: reconnecting.getStateLabel() equals `reconnecting`
   - Expected: reconnecting.reconnectAttempts equals `1`
   - Expected: reconnecting.reconnectTimerActive is true
- noAuto open
- noAuto handleConnectionError
   - Expected: noAuto.isClosedStatus() is true
   - Expected: noAuto.closeCallbackCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Unauthorized close can refresh token
- transport open
- transport handleConnectionError
   - Expected: transport.getStateLabel() equals `reconnecting`
   - Expected: transport.headers equals `["Authorization=new"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Reconnect budget and health checks
- transport open
- transport handleConnectionError
- transport handleConnectionError
   - Expected: transport.reconnectAttempts equals `1`
- exhausted open
- exhausted handleConnectionError
   - Expected: exhausted.isClosedStatus() is true
- pinged open
- pinged tickPing
   - Expected: pinged.pongReceived is false
- pinged tickPing
   - Expected: pinged.getStateLabel() equals `reconnecting`
- pinged close
   - Expected: pinged.getStateLabel() equals `closing`
   - Expected: pinged.pingIntervalActive is false
   - Expected: pinged.keepAliveIntervalActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
