# Tmux REST API Specification

> Tests the tmux REST API endpoints mounted under `/api/tmux/*` in the web dashboard server. The API provides HTTP access to tmux session, window, and pane management, enabling the browser-based terminal panel.

<!-- sdn-diagram:id=tmux_rest_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmux_rest_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmux_rest_api_spec -> std
tmux_rest_api_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmux_rest_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\": \"test\"}"
val value = _extract_json_field(json, "name")
expect value to_equal "test"
```

</details>

#### extracts from multiple fields

1. expect  extract json field
2. expect  extract json field
3. expect  extract json field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"session\": \"main\", \"window\": \"2\", \"pane\": \"0\"}"
expect _extract_json_field(json, "session") to_equal "main"
expect _extract_json_field(json, "window") to_equal "2"
expect _extract_json_field(json, "pane") to_equal "0"
```

</details>

#### returns empty string for missing field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\": \"test\"}"
val value = _extract_json_field(json, "missing")
expect value to_equal ""
```

</details>

#### returns empty string for empty json

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = _extract_json_field("", "name")
expect value to_equal ""
```

</details>

#### handles escaped characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"path\": \"a\\\\b\"}"
val value = _extract_json_field(json, "path")
expect value to_contain "b"
```

</details>

#### _query_to_json

#### converts single key-value pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _query_to_json("session=main")
expect json to_contain "session"
expect json to_contain "main"
```

</details>

#### converts multiple pairs

1. expect  extract json field
2. expect  extract json field
3. expect  extract json field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _query_to_json("session=main&window=0&pane=1")
expect _extract_json_field(json, "session") to_equal "main"
expect _extract_json_field(json, "window") to_equal "0"
expect _extract_json_field(json, "pane") to_equal "1"
```

</details>

#### handles empty value

1. expect  extract json field


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _query_to_json("key=")
expect _extract_json_field(json, "key") to_equal ""
```

</details>

### Tmux API Router

#### status endpoint

#### returns JSON with available field

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux", "")
# Either 200 (tmux available) or 503 (not installed)
expect (status == 200 or status == 503) to_equal true
expect ctype to_equal "application/json"
```

</details>

#### sessions endpoint

#### returns JSON array

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/sessions", "")
expect (status == 200 or status == 503) to_equal true
expect ctype to_equal "application/json"
```

</details>

#### method validation

#### rejects GET on send endpoint

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/send", "")
# Either 405 (method not allowed) or 503 (tmux not installed)
expect (status == 405 or status == 503) to_equal true
```

</details>

#### rejects GET on send-command endpoint

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/send-command", "")
expect (status == 405 or status == 503) to_equal true
```

</details>

#### rejects GET on resize endpoint

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/resize", "")
expect (status == 405 or status == 503) to_equal true
```

</details>

#### parameter validation

#### returns 400 when session missing from panes

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/panes", "")
# 400 (missing session) or 503 (no tmux)
expect (status == 400 or status == 503) to_equal true
```

</details>

#### returns 400 when session missing from windows

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/windows", "")
expect (status == 400 or status == 503) to_equal true
```

</details>

#### unknown endpoint

#### returns 404 for unknown path

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux/nonexistent", "")
# 404 or 503 (no tmux)
expect (status == 404 or status == 503) to_equal true
```

</details>

#### query string routing

#### handles capture with query params

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
