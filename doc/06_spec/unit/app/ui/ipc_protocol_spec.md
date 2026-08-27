# Ipc Protocol Specification

> Tests covering IPC Protocol, parse_ipc_message, build_ipc_render, build_ipc_dialog, build_ipc_notification, window lifecycle messages, build_ipc_request_http, extract_json_field, escape_ipc_json.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Protocol Specification

## Scenarios

### IPC Protocol

### parse_ipc_message

#### parses keypress events

- parses keypress events
   - Expected: event != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses keypress events")
val event = parse_ipc_message("{\"type\":\"keypress\",\"key\":\"j\"}")
expect(event != nil).to_equal(true)
```

</details>

#### parses action events

- parses action events
   - Expected: event != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses action events")
val event = parse_ipc_message("{\"type\":\"action\",\"name\":\"save\"}")
expect(event != nil).to_equal(true)
```

</details>

#### parses resize events

- parses resize events
   - Expected: event != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses resize events")
val event = parse_ipc_message("{\"type\":\"resize\",\"width\":\"800\",\"height\":\"600\"}")
expect(event != nil).to_equal(true)
```

</details>

#### parses quit events

- parses quit events
   - Expected: event != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses quit events")
val event = parse_ipc_message("{\"type\":\"quit\"}")
expect(event != nil).to_equal(true)
```

</details>

#### returns nil for unknown messages

- returns nil for unknown messages
   - Expected: event equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for unknown messages")
val event = parse_ipc_message("{\"type\":\"unknown\"}")
expect(event).to_equal(nil)
```

</details>

#### parses fetch results with headers

- parses fetch results with headers
   - Expected: request_id equals `fetch-3`
   - Expected: url equals `https://example.com/data`
   - Expected: status equals `200`
   - Expected: body equals `alpha`
   - Expected: error equals ``
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fetch results with headers")
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

- builds a render message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a render message")
val msg = build_ipc_render("<div>hello</div>")
expect(msg).to_contain("render")
expect(msg).to_contain("hello")
```

</details>

### build_ipc_dialog

#### builds a dialog message

- builds a dialog message


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a dialog message")
val msg = build_ipc_dialog("info", "Title", "Body text")
expect(msg).to_contain("dialog")
expect(msg).to_contain("Title")
expect(msg).to_contain("Body text")
```

</details>

### build_ipc_notification

#### builds a notification message

- builds a notification message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a notification message")
val msg = build_ipc_notification("Alert", "Something happened")
expect(msg).to_contain("notification")
expect(msg).to_contain("Alert")
```

</details>

### window lifecycle messages

#### escapes open window fields with html/css content

- escapes open window fields with html/css content


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes open window fields with html/css content")
val msg = build_ipc_open_window("win\"1", "A < B", "<style>.x{}</style><img class=\"simple-picture\">", 1, 2, 300, 200)

expect(msg).to_contain("\"type\":\"openWindow\"")
expect(msg).to_contain("\"windowId\":\"win\\\"1\"")
expect(msg).to_contain("\"title\":\"A < B\"")
expect(msg).to_contain("\\\"simple-picture\\\"")
expect(msg).to_contain("\"x\":1")
```

</details>

#### escapes render and close window ids

- escapes render and close window ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes render and close window ids")
val render = build_ipc_render_window("win\"2", "<b>body</b>")
val close = build_ipc_close_window("win\"2")

expect(render).to_contain("\"windowId\":\"win\\\"2\"")
expect(render).to_contain("<b>body</b>")
expect(close).to_contain("\"windowId\":\"win\\\"2\"")
```

</details>

### build_ipc_request_http

#### builds a GET fetch request without body fields

- builds a GET fetch request without body fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a GET fetch request without body fields")
val msg = build_ipc_request_fetch("https://example.com", "req-1")
expect(msg).to_contain("\"type\":\"request_fetch\"")
expect(msg).to_contain("\"url\":\"https://example.com\"")
expect(msg).to_contain("\"requestId\":\"req-1\"")
expect(msg).to_contain("\"method\":\"GET\"")
```

</details>

#### builds a POST fetch request with body and content type

- builds a POST fetch request with body and content type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a POST fetch request with body and content type")
val msg = build_ipc_request_http("https://example.com/submit", "req-2", "POST", "Cookie: sid=abc", "q=cat", "application/x-www-form-urlencoded")
expect(msg).to_contain("\"method\":\"POST\"")
expect(msg).to_contain("\"headers\":\"Cookie: sid=abc\"")
expect(msg).to_contain("\"body\":\"q=cat\"")
expect(msg).to_contain("\"contentType\":\"application/x-www-form-urlencoded\"")
```

</details>

### extract_json_field

#### extracts string fields

- extracts string fields
   - Expected: extract_json_field("{\"key\":\"value\"}", "key") equals `value`
   - Expected: extract_json_field("{\"a\":\"1\",\"b\":\"2\"}", "b") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts string fields")
expect(extract_json_field("{\"key\":\"value\"}", "key")).to_equal("value")
expect(extract_json_field("{\"a\":\"1\",\"b\":\"2\"}", "b")).to_equal("2")
```

</details>

#### returns empty for missing fields

- returns empty for missing fields
   - Expected: extract_json_field("{\"key\":\"value\"}", "missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for missing fields")
expect(extract_json_field("{\"key\":\"value\"}", "missing")).to_equal("")
```

</details>

### escape_ipc_json

#### escapes special characters

- escapes special characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes special characters")
val escaped = escape_ipc_json("hello\nworld")
expect(escaped).to_contain("\\n")
```

</details>

#### escapes quotes

- escapes quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes quotes")
val escaped = escape_ipc_json("say \"hi\"")
expect(escaped).to_contain("\\\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/ipc_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering IPC Protocol, parse_ipc_message, build_ipc_render, build_ipc_dialog, build_ipc_notification, window lifecycle messages, build_ipc_request_http, extract_json_field, escape_ipc_json.
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
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `94aefff90b86ead354a6d32dd0c6db65c5977d89681db0381795c6fcec08554d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94aefff90b86ead354a6d32dd0c6db65c5977d89681db0381795c6fcec08554d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94aefff90b86ead354a6d32dd0c6db65c5977d89681db0381795c6fcec08554d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/ui/ipc_protocol_spec.spl
mirror: doc/06_spec/unit/app/ui/ipc_protocol_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/ipc_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/ipc_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/ipc_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/ipc_protocol_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses keypress events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ipc_protocol_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses action events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ipc_protocol_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses resize events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
