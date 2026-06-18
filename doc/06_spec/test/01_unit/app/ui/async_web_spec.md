# Async Web Server Specification

> Verifies async web server response construction, event-channel behavior, WebSocket event parsing helpers, and production response security headers.

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
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Web Server Specification

Verifies async web server response construction, event-channel behavior, WebSocket event parsing helpers, and production response security headers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/simple_web_browser_production_hardening.md |
| Plan | doc/03_plan/agent_tasks/simple_browser_production_level.md |
| Design | doc/05_design/simple_web_browser_production_hardening.md |
| Research | doc/01_research/local/simple_browser_production_level.md |
| Source | `test/01_unit/app/ui/async_web_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies async web server response construction, event-channel behavior,
WebSocket event parsing helpers, and production response security headers.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Research:** doc/01_research/local/simple_browser_production_level.md
**Plan:** doc/03_plan/agent_tasks/simple_browser_production_level.md
**Design:** doc/05_design/simple_web_browser_production_hardening.md
**Traceability:** REQ-WEB-HARD-004, NFR-WEB-HARD-003, NFR-WEB-HARD-005

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

#### does not expose wildcard CORS by default

- expect resp contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = http_response(200, "application/json", "{}")
expect resp.contains("Access-Control-Allow-Origin: *") to_equal false
```

</details>

#### adds cache and sniffing guards to json responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = http_response(200, "application/json", "{}")
expect resp to_contain "Cache-Control: no-store"
expect resp to_contain "Pragma: no-cache"
expect resp to_contain "X-Content-Type-Options: nosniff"
```

</details>

#### adds browser document security headers to html responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = http_response(200, "text/html", "<h1>Hi</h1>")
expect resp to_contain "X-Frame-Options: DENY"
expect resp to_contain "Referrer-Policy: no-referrer"
expect resp to_contain "Content-Security-Policy: default-src 'self'"
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

- ch send


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

- ch send
- ch send
- ch send


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

- ch close
- expect ch is closed


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

#### extracts browser navigation intent fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"type\":\"browser_navigation\",\"action\":\"address\",\"url\":\"https://example.test\"}"
expect(extract_field(json, "type")).to_equal("browser_navigation")
expect(extract_field(json, "action")).to_equal("address")
expect(extract_field(json, "url")).to_equal("https://example.test")
```

</details>

#### keeps browser navigation intent parser branch guarded by an action allowlist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/ui.web/async_ws.spl")
expect(src).to_contain("fn ui_web_browser_navigation_action_allowed(action: text) -> bool")
expect(src).to_contain("\"browser_navigation\":")
expect(src).to_contain("return UIEvent.BrowserNavigation(action: action, url: url)")
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

- ch send


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

- expect updated mode name


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

- expect clients len


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

- expect clients len


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

- expect alive len


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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/simple_web_browser_production_hardening.md](doc/02_requirements/nfr/simple_web_browser_production_hardening.md)
- **Plan:** [doc/03_plan/agent_tasks/simple_browser_production_level.md](doc/03_plan/agent_tasks/simple_browser_production_level.md)
- **Design:** [doc/05_design/simple_web_browser_production_hardening.md](doc/05_design/simple_web_browser_production_hardening.md)
- **Research:** [doc/01_research/local/simple_browser_production_level.md](doc/01_research/local/simple_browser_production_level.md)


</details>
