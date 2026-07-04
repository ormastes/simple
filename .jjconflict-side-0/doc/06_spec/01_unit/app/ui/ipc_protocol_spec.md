# Ipc Protocol Specification

> <details>

<!-- sdn-diagram:id=ipc_protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_protocol_spec -> app
ipc_protocol_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Protocol Specification

## Scenarios

### IPC Protocol

### parse_ipc_message

#### parses keypress events

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"keypress\",\"key\":\"j\"}")
expect(event != nil).to_equal(true)
```

</details>

#### parses action events

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"action\",\"name\":\"save\"}")
expect(event != nil).to_equal(true)
```

</details>

#### parses window scoped keypress events as Simple actions

1. UIEvent Action
   - Expected: name equals `win:terminal:keypress:Enter`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"keypress\",\"windowId\":\"terminal\",\"key\":\"Enter\"}")
match event:
    UIEvent.Action(name) =>
        expect(name).to_equal("win:terminal:keypress:Enter")
    _ =>
        expect(false).to_equal(true)
```

</details>

#### parses window scoped action events as Simple actions

1. UIEvent Action
   - Expected: name equals `win:terminal:action:close`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"action\",\"windowId\":\"terminal\",\"name\":\"close\"}")
match event:
    UIEvent.Action(name) =>
        expect(name).to_equal("win:terminal:action:close")
    _ =>
        expect(false).to_equal(true)
```

</details>

#### parses Tauri input envelopes as Simple input changes

1. UIEvent InputChange
   - Expected: target_id equals `name`
   - Expected: value equals `Ada`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"input\",\"target\":\"tauri\",\"surface_id\":\"main\",\"event_type\":\"input\",\"target_id\":\"name\",\"value\":\"Ada\"}")
match event:
    UIEvent.InputChange(target_id, value) =>
        expect(target_id).to_equal("name")
        expect(value).to_equal("Ada")
    _ =>
        expect(false).to_equal(true)
```

</details>

#### parses resize events

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"resize\",\"width\":\"800\",\"height\":\"600\"}")
expect(event != nil).to_equal(true)
```

</details>

#### parses quit events

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"quit\"}")
expect(event != nil).to_equal(true)
```

</details>

#### returns nil for unknown messages

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"unknown\"}")
expect(event == nil).to_equal(true)
```

</details>

#### parses fetch results with headers

1. UIEvent FetchResult
   - Expected: request_id equals `fetch-3`
   - Expected: url equals `https://example.com/data`
   - Expected: status equals `200`
   - Expected: body equals `alpha`
   - Expected: error equals ``
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = parse_ipc_message("{\"type\":\"fetch_result\",\"requestId\":\"fetch-3\",\"url\":\"https://example.com/data\",\"status\":\"200\",\"headers\":\"Content-Type: text/plain\\nSet-Cookie: sid=abc\",\"body\":\"alpha\",\"error\":\"\"}")
match event:
    UIEvent.FetchResult(request_id, url, status, headers, body, error) =>
        expect(request_id).to_equal("fetch-3")
        expect(url).to_equal("https://example.com/data")
        expect(status).to_equal(200)
        expect(headers).to_contain("Set-Cookie: sid=abc")
        expect(body).to_equal("alpha")
        expect(error).to_equal("")
    _ =>
        expect(false).to_equal(true)
```

</details>

### build_ipc_render

#### builds a render message

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_ipc_render("<div>hello</div>")
expect(msg).to_contain("render")
expect(msg).to_contain("hello")
```

</details>

### build_ipc_dialog

#### builds a dialog message

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_ipc_dialog("info", "Title", "Body text")
expect(msg).to_contain("dialog")
expect(msg).to_contain("Title")
expect(msg).to_contain("Body text")
```

</details>

### build_ipc_notification

#### builds a notification message

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_ipc_notification("Alert", "Something happened")
expect(msg).to_contain("notification")
expect(msg).to_contain("Alert")
```

</details>

### window lifecycle messages

#### escapes open window fields with html/css content

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_ipc_open_window("win\"1", "A < B", "<style>.x{}</style><img class=\"simple-picture\">", 1, 2, 300, 200)

expect(msg).to_contain("\"type\":\"openWindow\"")
expect(msg).to_contain("\"windowId\":\"win\\\"1\"")
expect(msg).to_contain("\"title\":\"A < B\"")
expect(msg).to_contain("\\\"simple-picture\\\"")
expect(msg).to_contain("\"x\":1")
```

</details>

#### escapes render and close window ids

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val render = build_ipc_render_window("win\"2", "<b>body</b>")
val close = build_ipc_close_window("win\"2")

expect(render).to_contain("\"windowId\":\"win\\\"2\"")
expect(render).to_contain("<b>body</b>")
expect(close).to_contain("\"windowId\":\"win\\\"2\"")
```

</details>

### build_ipc_request_http

#### builds a GET fetch request without body fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_ipc_request_fetch("https://example.com", "req-1")
expect(msg).to_contain("\"type\":\"request_fetch\"")
expect(msg).to_contain("\"url\":\"https://example.com\"")
expect(msg).to_contain("\"requestId\":\"req-1\"")
expect(msg).to_contain("\"method\":\"GET\"")
```

</details>

#### builds a POST fetch request with body and content type

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_ipc_request_http("https://example.com/submit", "req-2", "POST", "Cookie: sid=abc", "q=cat", "application/x-www-form-urlencoded")
expect(msg).to_contain("\"method\":\"POST\"")
expect(msg).to_contain("\"headers\":\"Cookie: sid=abc\"")
expect(msg).to_contain("\"body\":\"q=cat\"")
expect(msg).to_contain("\"contentType\":\"application/x-www-form-urlencoded\"")
```

</details>

### extract_json_field

#### extracts string fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(extract_json_field("{\"key\":\"value\"}", "key")).to_equal("value")
expect(extract_json_field("{\"a\":\"1\",\"b\":\"2\"}", "b")).to_equal("2")
```

</details>

#### returns empty for missing fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(extract_json_field("{\"key\":\"value\"}", "missing")).to_equal("")
```

</details>

### escape_ipc_json

#### escapes special characters

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_ipc_json("hello\nworld")
expect(escaped).to_contain("\\n")
```

</details>

#### escapes quotes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_ipc_json("say \"hi\"")
expect(escaped).to_contain("\\\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ipc_protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IPC Protocol
- parse_ipc_message
- build_ipc_render
- build_ipc_dialog
- build_ipc_notification
- window lifecycle messages
- build_ipc_request_http
- extract_json_field
- escape_ipc_json

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
