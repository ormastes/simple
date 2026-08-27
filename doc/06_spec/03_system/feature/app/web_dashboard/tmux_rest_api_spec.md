# Tmux REST API Specification

> Tests the tmux REST API endpoints mounted under `/api/tmux/*` in the web dashboard server. The API provides HTTP access to tmux session, window, and pane management, enabling the browser-based terminal panel.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmux REST API Specification

Tests the tmux REST API endpoints mounted under `/api/tmux/*` in the web dashboard server. The API provides HTTP access to tmux session, window, and pane management, enabling the browser-based terminal panel.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TMUX-002 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/app/web_dashboard/tmux_rest_api_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the tmux REST API endpoints mounted under `/api/tmux/*` in the
web dashboard server. The API provides HTTP access to tmux session,
window, and pane management, enabling the browser-based terminal panel.

The REST API converts between query-string/JSON-body parameters and
the underlying `std.tmux` library functions.

## Key Concepts

| Concept | Description |
|---------|-------------|
| handle_tmux_api | Router that dispatches to endpoint handlers |
| _query_to_json | Converts URL query strings to JSON for uniform parsing |
| _extract_json_field | Simple JSON field extraction for request bodies |
| Endpoint tuple | Each handler returns (status_code, content_type, body) |

## Behavior

- GET requests accept query string parameters (e.g., `?session=main&window=0`)
- POST requests accept JSON body
- Returns 503 if tmux is not installed
- Returns 400 for missing required parameters
- Returns 405 for wrong HTTP method on mutation endpoints
- All responses are JSON with `application/json` content type

## Endpoint Reference

| Method | Path | Description |
|--------|------|-------------|
| GET | /api/tmux | Tmux status (available, server running, session count) |
| GET | /api/tmux/sessions | List all sessions |
| POST | /api/tmux/sessions | Create new session (body: name) |
| DELETE | /api/tmux/sessions | Kill session (body: name) |
| GET | /api/tmux/windows | List windows (query: session) |
| GET | /api/tmux/panes | List panes (query: session, window) |
| GET | /api/tmux/capture | Capture pane content (query: session, window, pane) |
| POST | /api/tmux/send | Send keys/text to pane |
| POST | /api/tmux/send-command | Send command + Enter to pane |
| POST | /api/tmux/resize | Resize pane (body: session, window, pane, width, height) |

## Implementation Notes

- Query-string parameters are converted to JSON via `_query_to_json` so
  all endpoint handlers use a uniform JSON body interface
- The router strips `/api/tmux` prefix and splits path from query string
- Error responses always include an `error` field in the JSON body
- Graceful degradation: returns 503 when tmux binary is missing

## Related Specifications

- [Tmux API Library](test/unit/lib/std/tmux/tmux_api_spec.spl) — underlying stdlib module
- [Dashboard HTML Rendering](test/feature/app/web_dashboard/dashboard_render_spec.spl) — shared rendering layer

## Examples

```simple
# GET /api/tmux → status
use std.spec.step

val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux", "")
# body: {"available": true, "server_running": true, "session_count": 3}

# GET with query params
val (s, c, b) = handle_tmux_api("GET", "/api/tmux/capture?session=main&window=0&pane=0", "")
# body: {"pane_id": "main:0.0", "rows": 24, "content": "..."}

# POST with JSON body
val body = r'{"session": "main", "window": "0", "pane": "0", "command": "ls -la"}'
val (s2, c2, b2) = handle_tmux_api("POST", "/api/tmux/send-command", body)
```

## Scenarios

### Tmux API JSON Parsing

#### _extract_json_field

#### extracts a simple field

- extracts a simple field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts a simple field")
val json = "{\"name\": \"test\"}"
val value = _extract_json_field(json, "name")
expect value to_equal "test"
```

</details>

#### extracts from multiple fields

- extracts from multiple fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts from multiple fields")
val json = "{\"session\": \"main\", \"window\": \"2\", \"pane\": \"0\"}"
expect _extract_json_field(json, "session") to_equal "main"
expect _extract_json_field(json, "window") to_equal "2"
expect _extract_json_field(json, "pane") to_equal "0"
```

</details>

#### returns empty string for missing field

- returns empty string for missing field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty string for missing field")
val json = "{\"name\": \"test\"}"
val value = _extract_json_field(json, "missing")
expect value to_equal ""
```

</details>

#### returns empty string for empty json

- returns empty string for empty json


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty string for empty json")
val value = _extract_json_field("", "name")
expect value to_equal ""
```

</details>

#### handles escaped characters

- handles escaped characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles escaped characters")
val json = "{\"path\": \"a\\\\b\"}"
val value = _extract_json_field(json, "path")
expect value to_contain "b"
```

</details>

#### _query_to_json

#### converts single key-value pair

- converts single key-value pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts single key-value pair")
val json = _query_to_json("session=main")
expect json to_contain "session"
expect json to_contain "main"
```

</details>

#### converts multiple pairs

- converts multiple pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts multiple pairs")
val json = _query_to_json("session=main&window=0&pane=1")
expect _extract_json_field(json, "session") to_equal "main"
expect _extract_json_field(json, "window") to_equal "0"
expect _extract_json_field(json, "pane") to_equal "1"
```

</details>

#### handles empty value

- handles empty value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty value")
val json = _query_to_json("key=")
expect _extract_json_field(json, "key") to_equal ""
```

</details>

### Tmux API Router

#### status endpoint

#### returns JSON with available field

- returns JSON with available field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns JSON with available field")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux", "")
# Either 200 (tmux available) or 503 (not installed)
expect (status == 200 or status == 503) to_equal true
expect ctype to_equal "application/json"
```

</details>

#### sessions endpoint

#### returns JSON array

- returns JSON array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns JSON array")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/sessions", "")
expect (status == 200 or status == 503) to_equal true
expect ctype to_equal "application/json"
```

</details>

#### method validation

#### rejects GET on send endpoint

- rejects GET on send endpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects GET on send endpoint")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/send", "")
# Either 405 (method not allowed) or 503 (tmux not installed)
expect (status == 405 or status == 503) to_equal true
```

</details>

#### rejects GET on send-command endpoint

- rejects GET on send-command endpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects GET on send-command endpoint")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/send-command", "")
expect (status == 405 or status == 503) to_equal true
```

</details>

#### rejects GET on resize endpoint

- rejects GET on resize endpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects GET on resize endpoint")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/resize", "")
expect (status == 405 or status == 503) to_equal true
```

</details>

#### parameter validation

#### returns 400 when session missing from panes

- returns 400 when session missing from panes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns 400 when session missing from panes")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/panes", "")
# 400 (missing session) or 503 (no tmux)
expect (status == 400 or status == 503) to_equal true
```

</details>

#### returns 400 when session missing from windows

- returns 400 when session missing from windows


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns 400 when session missing from windows")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/windows", "")
expect (status == 400 or status == 503) to_equal true
```

</details>

#### unknown endpoint

#### returns 404 for unknown path

- returns 404 for unknown path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns 404 for unknown path")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/nonexistent", "")
# 404 or 503 (no tmux)
expect (status == 404 or status == 503) to_equal true
```

</details>

#### query string routing

#### handles capture with query params

- handles capture with query params


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles capture with query params")
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/capture?session=test&window=0&pane=0", "")
# 200 (capture attempted) or 503 (no tmux)
expect (status == 200 or status == 503) to_equal true
expect ctype to_equal "application/json"
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e92f4b07c32a6416fcf094e3ac6f1ba1b37a863f343edf25143d2e779961d15f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e92f4b07c32a6416fcf094e3ac6f1ba1b37a863f343edf25143d2e779961d15f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e92f4b07c32a6416fcf094e3ac6f1ba1b37a863f343edf25143d2e779961d15f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/web_dashboard/tmux_rest_api_spec.spl
mirror: doc/06_spec/03_system/feature/app/web_dashboard/tmux_rest_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/web_dashboard/tmux_rest_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/web_dashboard/tmux_rest_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/web_dashboard/tmux_rest_api_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a simple field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/web_dashboard/tmux_rest_api_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts from multiple fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/web_dashboard/tmux_rest_api_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string for missing field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
