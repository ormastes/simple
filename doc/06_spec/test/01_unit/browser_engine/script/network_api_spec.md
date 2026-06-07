# Network Api Specification

> <details>

<!-- sdn-diagram:id=network_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=network_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

network_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=network_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Network Api Specification

## Scenarios

### Browser script network API

### Fetch

#### keeps no-dispatch fetch as a safe zero-status response

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("https://example.test/data", "GET")
val resp = fetch_send(req)
expect(resp.status).to_equal(0)
expect(resp.ok).to_equal(false)
expect(resp.body).to_equal("")
```

</details>

#### converts script fetch requests to net fetch requests

1. var req = fetch create request
2. req = fetch set header
   - Expected: net_req.method equals `POST`
   - Expected: net_req.url.scheme equals `https`
   - Expected: net_req.url.host equals `example.test`
   - Expected: net_req.url.path equals `/data`
   - Expected: net_req.url.query equals `q=1`
   - Expected: net_req.headers equals `accept: text/plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var req = fetch_create_request("https://example.test/data?q=1", "POST")
req = fetch_set_header(req, "accept", "text/plain")
val net_req = script_fetch_to_net_request(req)
expect(net_req.method).to_equal("POST")
expect(net_req.url.scheme).to_equal("https")
expect(net_req.url.host).to_equal("example.test")
expect(net_req.url.path).to_equal("/data")
expect(net_req.url.query).to_equal("q=1")
expect(net_req.headers).to_equal("accept: text/plain")
```

</details>

#### parses explicit ports and fragments in script fetch URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("http://example.test:8080/data/path?q=1#frag", "GET")
val net_req = script_fetch_to_net_request(req)
expect(net_req.url.scheme).to_equal("http")
expect(net_req.url.host).to_equal("example.test")
expect(net_req.url.port).to_equal(8080)
expect(net_req.url.path).to_equal("/data/path")
expect(net_req.url.query).to_equal("q=1")
expect(net_req.url.fragment).to_equal("frag")
```

</details>

#### sends script fetch through injected host dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("http://example.test/api", "GET")
val dispatch = ScriptStaticFetchDispatch.create(200, "content-type: text/plain\nx-cache: hit", "hello")
val resp = fetch_send_with_dispatch(req, dispatch)
expect(resp.status).to_equal(200)
expect(resp.ok).to_equal(true)
expect(resp.headers[0]).to_equal("content-type")
expect(resp.headers[1]).to_equal("text/plain")
expect(resp.headers[2]).to_equal("x-cache")
expect(resp.headers[3]).to_equal("hit")
expect(resp.body).to_equal("hello")
```

</details>

#### falls back when optional dispatch is not installed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("http://example.test/api", "GET")
val resp = fetch_send_with_optional_dispatch(req, nil)
expect(resp.status).to_equal(0)
expect(resp.ok).to_equal(false)
```

</details>

#### sends through optional dispatch when installed

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("http://example.test/api", "GET")
val dispatch = ScriptStaticFetchDispatch.create(204, "x-mode: injected", "")
val resp = fetch_send_with_optional_dispatch(req, Some(dispatch))
expect(resp.status).to_equal(204)
expect(resp.ok).to_equal(true)
expect(resp.headers[0]).to_equal("x-mode")
expect(resp.headers[1]).to_equal("injected")
```

</details>

### WebSocket

#### rejects non-WebSocket URL schemes as closed connections

1. var ws = websocket connect
2. ws = websocket send
   - Expected: ws.state equals `closed`
   - Expected: ws.ready_state equals `WEBSOCKET_CLOSED`
   - Expected: ws.buffered_amount equals `0`
   - Expected: ws.messages.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("https://example.test/socket")
ws = websocket_send(ws, "ignored")
expect(ws.state).to_equal("closed")
expect(ws.ready_state).to_equal(WEBSOCKET_CLOSED)
expect(ws.buffered_amount).to_equal(0)
expect(ws.messages.len()).to_equal(0)
```

</details>

#### rejects WebSocket URLs with fragments as closed connections

1. var ws = websocket connect
2. ws = websocket send
   - Expected: ws.state equals `closed`
   - Expected: ws.ready_state equals `WEBSOCKET_CLOSED`
   - Expected: ws.buffered_amount equals `0`
   - Expected: ws.messages.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("wss://example.test/socket#frag")
ws = websocket_send(ws, "ignored")
expect(ws.state).to_equal("closed")
expect(ws.ready_state).to_equal(WEBSOCKET_CLOSED)
expect(ws.buffered_amount).to_equal(0)
expect(ws.messages.len()).to_equal(0)
```

</details>

#### stores sent messages on open in-memory connections

1. var ws = websocket connect
2. ws = websocket send
3. ws = websocket send
   - Expected: ws.state equals `open`
   - Expected: ws.ready_state equals `WEBSOCKET_OPEN`
   - Expected: ws.buffered_amount equals `10`
   - Expected: ws.protocol equals ``
   - Expected: ws.extensions equals ``
   - Expected: ws.received_messages.len() equals `0`
   - Expected: ws.close_code equals `WEBSOCKET_CLOSE_NO_STATUS`
   - Expected: ws.close_was_clean is false
   - Expected: ws.messages.len() equals `2`
   - Expected: ws.messages[0] equals `hello`
   - Expected: ws.messages[1] equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("ws://example.test/socket")
ws = websocket_send(ws, "hello")
ws = websocket_send(ws, "world")
expect(ws.state).to_equal("open")
expect(ws.ready_state).to_equal(WEBSOCKET_OPEN)
expect(ws.buffered_amount).to_equal(10)
expect(ws.protocol).to_equal("")
expect(ws.extensions).to_equal("")
expect(ws.received_messages.len()).to_equal(0)
expect(ws.close_code).to_equal(WEBSOCKET_CLOSE_NO_STATUS)
expect(ws.close_was_clean).to_equal(false)
expect(ws.messages.len()).to_equal(2)
expect(ws.messages[0]).to_equal("hello")
expect(ws.messages[1]).to_equal("world")
```

</details>

#### ignores sends after close

1. var ws = websocket connect
2. ws = websocket send
3. ws = websocket close
4. ws = websocket send
   - Expected: ws.state equals `closed`
   - Expected: ws.ready_state equals `WEBSOCKET_CLOSED`
   - Expected: ws.buffered_amount equals `6`
   - Expected: ws.protocol equals ``
   - Expected: ws.extensions equals ``
   - Expected: ws.close_code equals `WEBSOCKET_CLOSE_NORMAL`
   - Expected: ws.close_reason equals ``
   - Expected: ws.close_was_clean is true
   - Expected: ws.messages.len() equals `1`
   - Expected: ws.messages[0] equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("ws://example.test/socket")
ws = websocket_send(ws, "before")
ws = websocket_close(ws)
ws = websocket_send(ws, "after")
expect(ws.state).to_equal("closed")
expect(ws.ready_state).to_equal(WEBSOCKET_CLOSED)
expect(ws.buffered_amount).to_equal(6)
expect(ws.protocol).to_equal("")
expect(ws.extensions).to_equal("")
expect(ws.close_code).to_equal(WEBSOCKET_CLOSE_NORMAL)
expect(ws.close_reason).to_equal("")
expect(ws.close_was_clean).to_equal(true)
expect(ws.messages.len()).to_equal(1)
expect(ws.messages[0]).to_equal("before")
```

</details>

#### selects the first valid requested subprotocol

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = websocket_connect_with_protocols("wss://example.test/socket", [" invalid", "chat.v2", "ignored"])
expect(ws.state).to_equal("open")
expect(ws.ready_state).to_equal(WEBSOCKET_OPEN)
expect(ws.protocol).to_equal("chat.v2")
```

</details>

#### keeps protocol empty for invalid URLs even when protocols are requested

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = websocket_connect_with_protocols("https://example.test/socket", ["chat.v2"])
expect(ws.state).to_equal("closed")
expect(ws.ready_state).to_equal(WEBSOCKET_CLOSED)
expect(ws.protocol).to_equal("")
```

</details>

#### records close code and reason for valid close requests

1. var ws = websocket connect
2. ws = websocket close with code
   - Expected: ws.ready_state equals `WEBSOCKET_CLOSED`
   - Expected: ws.close_code equals `3001`
   - Expected: ws.close_reason equals `app shutdown`
   - Expected: ws.close_was_clean is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("wss://example.test/socket")
ws = websocket_close_with_code(ws, 3001, "app shutdown")
expect(ws.ready_state).to_equal(WEBSOCKET_CLOSED)
expect(ws.close_code).to_equal(3001)
expect(ws.close_reason).to_equal("app shutdown")
expect(ws.close_was_clean).to_equal(true)
```

</details>

#### marks invalid close codes as no-status unsafe closes

1. var ws = websocket connect
2. ws = websocket close with code
   - Expected: ws.ready_state equals `WEBSOCKET_CLOSED`
   - Expected: ws.close_code equals `WEBSOCKET_CLOSE_NO_STATUS`
   - Expected: ws.close_reason equals ``
   - Expected: ws.close_was_clean is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("wss://example.test/socket")
ws = websocket_close_with_code(ws, 1006, "not allowed")
expect(ws.ready_state).to_equal(WEBSOCKET_CLOSED)
expect(ws.close_code).to_equal(WEBSOCKET_CLOSE_NO_STATUS)
expect(ws.close_reason).to_equal("")
expect(ws.close_was_clean).to_equal(false)
```

</details>

#### queues and drains received messages without network I/O

1. var ws = websocket connect
2. ws = websocket queue received
3. ws = websocket queue received
   - Expected: websocket_receive_count(ws) equals `2`
   - Expected: first.has_message is true
   - Expected: first.message equals `one`
   - Expected: websocket_receive_count(first.connection) equals `1`
   - Expected: second.has_message is true
   - Expected: second.message equals `two`
   - Expected: empty.has_message is false
   - Expected: empty.message equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("wss://example.test/socket")
ws = websocket_queue_received(ws, "one")
ws = websocket_queue_received(ws, "two")
expect(websocket_receive_count(ws)).to_equal(2)
val first = websocket_receive_next(ws)
expect(first.has_message).to_equal(true)
expect(first.message).to_equal("one")
expect(websocket_receive_count(first.connection)).to_equal(1)
val second = websocket_receive_next(first.connection)
expect(second.has_message).to_equal(true)
expect(second.message).to_equal("two")
val empty = websocket_receive_next(second.connection)
expect(empty.has_message).to_equal(false)
expect(empty.message).to_equal("")
```

</details>

#### guards send behavior with readyState rather than the text state label

1. var ws = websocket connect
2. ws = websocket send
3. ws = websocket queue received
   - Expected: ws.messages.len() equals `0`
   - Expected: ws.received_messages.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("wss://example.test/socket")
ws.state = "open"
ws.ready_state = WEBSOCKET_CLOSED
ws = websocket_send(ws, "ignored")
ws = websocket_queue_received(ws, "ignored")
expect(ws.messages.len()).to_equal(0)
expect(ws.received_messages.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/script/network_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser script network API
- Fetch
- WebSocket

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
