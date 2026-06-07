# Network API Spec

> Unit tests for the Simple browser engine Network API.

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
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Network API Spec

Unit tests for the Simple browser engine Network API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/network_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the Simple browser engine Network API.

## Scenarios

### Network API - Fetch Request

#### creates a GET request

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("https://example.com", "GET")
expect(req.url).to_equal("https://example.com")
```

</details>

#### request has correct method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("https://example.com", "POST")
expect(req.method).to_equal("POST")
```

</details>

#### adds headers to request

1. var req = fetch create request
2. req = fetch set header
   - Expected: req.headers.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var req = fetch_create_request("https://example.com", "GET")
req = fetch_set_header(req, "Content-Type", "application/json")
expect(req.headers.len()).to_equal(2)
```

</details>

### Network API - Fetch Response

#### fetch without host dispatch returns an opaque network error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("https://example.com", "GET")
val resp = fetch_send(req)
expect(resp.status).to_equal(0)
```

</details>

#### opaque network error response is not ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("https://example.com", "GET")
val resp = fetch_send(req)
expect(resp.ok).to_equal(false)
```

</details>

#### fetch through dispatch returns status headers and body

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = fetch_create_request("https://example.com/api", "GET")
val dispatch = ScriptStaticFetchDispatch.create(201, "Content-Type: application/json\nX-Trace: abc", "{\"ok\":true}")
val resp = fetch_send_with_dispatch(req, dispatch)
expect(resp.status).to_equal(201)
expect(resp.ok).to_equal(true)
expect(resp.headers.len()).to_equal(4)
expect(resp.headers[0]).to_equal("Content-Type")
expect(resp.headers[1]).to_equal("application/json")
expect(resp.headers[2]).to_equal("X-Trace")
expect(resp.headers[3]).to_equal("abc")
expect(resp.body).to_equal("{\"ok\":true}")
```

</details>

### Network API - WebSocket

#### creates a websocket connection

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = websocket_connect("wss://example.com/ws")
expect(ws.url).to_equal("wss://example.com/ws")
```

</details>

#### websocket starts in open state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = websocket_connect("wss://example.com/ws")
expect(ws.state).to_equal("open")
expect(ws.ready_state).to_equal(WEBSOCKET_OPEN)
expect(ws.buffered_amount).to_equal(0)
expect(ws.protocol).to_equal("")
expect(ws.extensions).to_equal("")
```

</details>

#### rejects fragment URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ws = websocket_connect("wss://example.com/ws#frag")
expect(ws.state).to_equal("closed")
expect(ws.ready_state).to_equal(WEBSOCKET_CLOSED)
expect(ws.protocol).to_equal("")
expect(ws.extensions).to_equal("")
expect(ws.buffered_amount).to_equal(0)
```

</details>

#### closes a websocket

1. var ws = websocket connect
2. ws = websocket close
   - Expected: ws.state equals `closed`
   - Expected: ws.ready_state equals `WEBSOCKET_CLOSED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ws = websocket_connect("wss://example.com/ws")
ws = websocket_close(ws)
expect(ws.state).to_equal("closed")
expect(ws.ready_state).to_equal(WEBSOCKET_CLOSED)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
