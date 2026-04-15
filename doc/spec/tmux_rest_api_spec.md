# Tmux REST API Specification

*Source: `test/app/web_dashboard/tmux_rest_api_spec.spl`*
*Last Updated: 2026-03-29*

**Feature IDs:** #TMUX-002
**Category:** Tooling
**Difficulty:** 3/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

---

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

- [Tmux API Library](test/lib/std/unit/tmux/tmux_api_spec.spl) — underlying stdlib module
- [Dashboard HTML Rendering](test/app/web_dashboard/dashboard_render_spec.spl) — shared rendering layer

## Examples

```simple
val (status, ctype, body) = handle_tmux_api("GET", "/api/tmux", "")

val (s, c, b) = handle_tmux_api("GET", "/api/tmux/capture?session=main&window=0&pane=0", "")

val body = r'{"session": "main", "window": "0", "pane": "0", "command": "ls -la"}'
val (s2, c2, b2) = handle_tmux_api("POST", "/api/tmux/send-command", body)
```

## Request Body Parsing

    The `_extract_json_field` helper extracts string values from
    simple JSON objects. Used to parse both JSON bodies and
    query-string-converted JSON.

### Scenario: Extracting fields from JSON strings

        Handles basic JSON objects with string values.

### Scenario: Converting URL query strings to JSON

        Enables GET requests to use query parameters while
        endpoint handlers work uniformly with JSON bodies.

## Endpoint Routing and HTTP Method Handling

    The `handle_tmux_api` function routes requests based on path
    and HTTP method, returning (status, content_type, body) tuples.

### Scenario: GET /api/tmux

        Returns tmux availability and session count. Always succeeds
        if tmux is installed (returns 503 otherwise).

### Scenario: GET /api/tmux/sessions

        Lists all active tmux sessions as a JSON array.

### Scenario: Wrong HTTP method on mutation endpoints

        POST-only endpoints reject GET requests with 405.

### Scenario: Missing required parameters

        Endpoints that require session/command return 400 when
        required fields are absent.

### Scenario: Non-existent API path

        Returns 404 for paths not matching any known endpoint.

### Scenario: GET with query parameters

        Query parameters are converted to JSON and passed to
        endpoint handlers uniformly.

## Test Summary

| Metric | Count |
|--------|-------|
| Scenarios | 17 |
| Slow Scenarios | 0 |
| Skipped Scenarios | 0 |

## Scenarios

- extracts a simple field
- extracts from multiple fields
- returns empty string for missing field
- returns empty string for empty json
- handles escaped characters
- converts single key-value pair
- converts multiple pairs
- handles empty value
- returns JSON with available field
- returns JSON array
- rejects GET on send endpoint
- rejects GET on send-command endpoint
- rejects GET on resize endpoint
- returns 400 when session missing from panes
- returns 400 when session missing from windows
- returns 404 for unknown path
- handles capture with query params
