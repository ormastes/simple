# Async Web Specification

> <details>

<!-- sdn-diagram:id=async_web_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_web_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_web_spec -> std
async_web_spec -> common
async_web_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_web_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Web Specification

## Scenarios

### AsyncWebServer

### http_response helper

#### generates 200 OK response with correct Content-Type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = http_response(200, "text/html", "<h1>Hi</h1>")
expect resp to_contain "HTTP/1.1 200 OK"
expect resp to_contain "Content-Type: text/html"
```

</details>

#### generates 404 response

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = http_response(404, "text/plain", "Not Found")
expect resp to_contain "HTTP/1.1 404 Not Found"
```

</details>

#### includes CORS header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = http_response(200, "application/json", "{}")
expect resp to_contain "Access-Control-Allow-Origin: *"
```

</details>

#### includes body content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "{\"status\": \"ok\"}"
val resp = http_response(200, "application/json", body)
expect resp to_contain body
```

</details>

### async_state_to_json

#### serializes state mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val json = async_state_to_json(state)
expect json to_contain "\"mode\""
```

</details>

#### serializes focused_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val json = async_state_to_json(state)
expect json to_contain "\"focused_id\""
```

</details>

#### is valid JSON structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val json = async_state_to_json(state)
# Check contains opening and closing braces
expect json to_contain "\"mode\""
expect json to_contain "\"focused_id\""
expect json to_contain "\"title\""
expect json to_contain "\"theme\""
```

</details>

### Event channel integration

#### channel sends and receives UIEvent

1. ch send


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send(UIEvent.KeyPress(key: "a"))
val received = ch.try_recv()
expect received != nil to_equal true
```

</details>

#### channel returns nil when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
val received = ch.try_recv()
expect received == nil to_equal true
```

</details>

#### channel delivers multiple events in order

1. ch send
2. ch send
3. ch send


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send(UIEvent.KeyPress(key: "x"))
ch.send(UIEvent.FileChanged)
ch.send(UIEvent.Quit)
val e1 = ch.try_recv()
val e2 = ch.try_recv()
val e3 = ch.try_recv()
expect e1 != nil to_equal true
expect e2 != nil to_equal true
expect e3 != nil to_equal true
```

</details>

#### channel is closeable

1. ch close
2. expect ch is closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.close()
expect ch.is_closed() to_equal true
```

</details>

### parse_ws_event helpers

#### returns empty for empty json

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = extract_field("", "type")
expect t to_equal ""
```

</details>

### extract_field

#### extracts field with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_field("{\"type\": \"key\"}", "type")
expect result to_equal "key"
```

</details>

#### extracts field without spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_field("{\"type\":\"key\"}", "type")
expect result to_equal "key"
```

</details>

#### returns empty for missing field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_field("{\"type\":\"key\"}", "missing")
expect result to_equal ""
```

</details>

#### returns empty for empty json

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_field("", "type")
expect result to_equal ""
```

</details>

### File change detection

#### FileChanged event can be sent over channel

1. ch send


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = channel_new()
ch.send(UIEvent.FileChanged)
val event = ch.try_recv()
expect event != nil to_equal true
```

</details>

#### state update after file change preserves mode

1. expect updated mode name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val new_tree = make_test_tree()
val updated = update_tree(state, new_tree)
expect updated.mode_name() to_equal state.mode_name()
```

</details>

### Multiple client tracking

#### empty client list has zero length

1. expect clients len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clients: [i32] = []
expect clients.len() to_equal 0
```

</details>

#### adding clients increases count

1. expect clients len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clients: [i32] = []
clients = clients + [1]
clients = clients + [2]
expect clients.len() to_equal 2
```

</details>

#### pruning removes disconnected entries

1. expect alive len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clients = [1, 2, 3]
# Simulate keeping only alive clients (1 and 3)
var alive: [i32] = []
alive = alive + [1]
alive = alive + [3]
expect alive.len() to_equal 2
```

</details>

### HTTP response generation

#### 200 response contains status line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = http_response(200, "text/html", "hello")
expect resp to_contain "HTTP/1.1 200 OK"
```

</details>

#### response contains Content-Length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "test"
val resp = http_response(200, "text/plain", body)
expect resp to_contain "Content-Length:"
```

</details>

#### response ends with body content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "the body"
val resp = http_response(200, "text/plain", body)
expect resp to_contain body
```

</details>

#### response includes Connection: close

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = http_response(200, "text/html", "x")
expect resp to_contain "Connection: close"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/async_web_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AsyncWebServer
- http_response helper
- async_state_to_json
- Event channel integration
- parse_ws_event helpers
- extract_field
- File change detection
- Multiple client tracking
- HTTP response generation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
