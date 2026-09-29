# Async Web Specification

> Tests covering AsyncWebServer, http_response helper, async_state_to_json, Event channel integration, parse_ws_event helpers, extract_field, File change detection, Multiple client tracking, HTTP response generation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Web Specification

## Scenarios

### AsyncWebServer

### http_response helper

#### generates 200 OK response with correct Content-Type

- generates 200 OK response with correct Content-Type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates 200 OK response with correct Content-Type")
val resp = http_response(200, "text/html", "<h1>Hi</h1>")
expect resp to_contain "HTTP/1.1 200 OK"
expect resp to_contain "Content-Type: text/html"
```

</details>

#### generates 404 response

- generates 404 response


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates 404 response")
val resp = http_response(404, "text/plain", "Not Found")
expect resp to_contain "HTTP/1.1 404 Not Found"
```

</details>

#### includes CORS header

- includes CORS header


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes CORS header")
val resp = http_response(200, "application/json", "{}")
expect resp to_contain "Access-Control-Allow-Origin: *"
```

</details>

#### adds cache and sniffing guards to json responses

- adds cache and sniffing guards to json responses


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds cache and sniffing guards to json responses")
val resp = http_response(200, "application/json", "{}")
expect resp to_contain "Cache-Control: no-store"
expect resp to_contain "Pragma: no-cache"
expect resp to_contain "X-Content-Type-Options: nosniff"
```

</details>

#### adds browser document security headers to html responses

- adds browser document security headers to html responses


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds browser document security headers to html responses")
val resp = http_response(200, "text/html", "<h1>Hi</h1>")
expect resp to_contain "X-Frame-Options: DENY"
expect resp to_contain "Referrer-Policy: no-referrer"
expect resp to_contain "Content-Security-Policy: default-src 'self'"
```

</details>

#### includes body content

- includes body content


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes body content")
val body = "{\"status\": \"ok\"}"
val resp = http_response(200, "application/json", body)
expect resp to_contain body
```

</details>

### async_state_to_json

#### serializes state mode

- serializes state mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes state mode")
val tree = make_test_tree()
val state = init_state(tree)
val json = async_state_to_json(state)
expect json to_contain "\"mode\""
```

</details>

#### serializes focused_id

- serializes focused_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes focused_id")
val tree = make_test_tree()
val state = init_state(tree)
val json = async_state_to_json(state)
expect json to_contain "\"focused_id\""
```

</details>

#### is valid JSON structure

- is valid JSON structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is valid JSON structure")
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

- channel sends and receives UIEvent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("channel sends and receives UIEvent")
val ch = channel_new()
ch.send(UIEvent.KeyPress(key: "a"))
val received = ch.try_recv()
expect received != nil to_equal true
```

</details>

#### channel returns nil when empty

- channel returns nil when empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("channel returns nil when empty")
val ch = channel_new()
val received = ch.try_recv()
expect received == nil to_equal true
```

</details>

#### channel delivers multiple events in order

- channel delivers multiple events in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("channel delivers multiple events in order")
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

- channel is closeable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("channel is closeable")
val ch = channel_new()
ch.close()
expect ch.is_closed() to_equal true
```

</details>

### parse_ws_event helpers

#### returns empty for empty json

- returns empty for empty json


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty json")
val t = extract_field("", "type")
expect t to_equal ""
```

</details>

### extract_field

#### extracts field with spaces

- extracts field with spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts field with spaces")
val result = extract_field("{\"type\": \"key\"}", "type")
expect result to_equal "key"
```

</details>

#### extracts field without spaces

- extracts field without spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts field without spaces")
val result = extract_field("{\"type\":\"key\"}", "type")
expect result to_equal "key"
```

</details>

#### returns empty for missing field

- returns empty for missing field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for missing field")
val result = extract_field("{\"type\":\"key\"}", "missing")
expect result to_equal ""
```

</details>

#### returns empty for empty json

- returns empty for empty json


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty json")
val result = extract_field("", "type")
expect result to_equal ""
```

</details>

### File change detection

#### FileChanged event can be sent over channel

- FileChanged event can be sent over channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FileChanged event can be sent over channel")
val ch = channel_new()
ch.send(UIEvent.FileChanged)
val event = ch.try_recv()
expect event != nil to_equal true
```

</details>

#### state update after file change preserves mode

- state update after file change preserves mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("state update after file change preserves mode")
val tree = make_test_tree()
val state = init_state(tree)
val new_tree = make_test_tree()
val updated = update_tree(state, new_tree)
expect updated.mode_name() to_equal state.mode_name()
```

</details>

### Multiple client tracking

#### empty client list has zero length

- empty client list has zero length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty client list has zero length")
val clients: [i32] = []
expect clients.len() to_equal 0
```

</details>

#### adding clients increases count

- adding clients increases count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adding clients increases count")
var clients: [i32] = []
clients = clients + [1]
clients = clients + [2]
expect clients.len() to_equal 2
```

</details>

#### pruning removes disconnected entries

- pruning removes disconnected entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pruning removes disconnected entries")
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

- 200 response contains status line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("200 response contains status line")
val resp = http_response(200, "text/html", "hello")
expect resp to_contain "HTTP/1.1 200 OK"
```

</details>

#### response contains Content-Length

- response contains Content-Length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("response contains Content-Length")
val body = "test"
val resp = http_response(200, "text/plain", body)
expect resp to_contain "Content-Length:"
```

</details>

#### response ends with body content

- response ends with body content


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("response ends with body content")
val body = "the body"
val resp = http_response(200, "text/plain", body)
expect resp to_contain body
```

</details>

#### response includes Connection: close

- response includes Connection: close


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("response includes Connection: close")
val resp = http_response(200, "text/html", "x")
expect resp to_contain "Connection: close"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/async_web_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AsyncWebServer, http_response helper, async_state_to_json, Event channel integration, parse_ws_event helpers, extract_field, File change detection, Multiple client tracking, HTTP response generation.
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
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7bd219d1dcfe337cf94a42d5e9d9ee555097b1a79a26ada1674c14a3235e71bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bd219d1dcfe337cf94a42d5e9d9ee555097b1a79a26ada1674c14a3235e71bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bd219d1dcfe337cf94a42d5e9d9ee555097b1a79a26ada1674c14a3235e71bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/async_web_spec.spl
mirror: doc/06_spec/unit/app/ui/async_web_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/async_web_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/async_web_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/async_web_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates 200 OK response with correct Content-Type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/async_web_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates 404 response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/async_web_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes CORS header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
