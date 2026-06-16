# Simple Web Browser Production Hardening Specification

> <details>

<!-- sdn-diagram:id=simple_web_browser_production_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_browser_production_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_browser_production_hardening_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_browser_production_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Browser Production Hardening Specification

## Scenarios

### Simple web browser production hardening live endpoints

<details>
<summary>Advanced: fails closed on unauthenticated browser HTTP and WebSocket routes</summary>

#### fails closed on unauthenticated browser HTTP and WebSocket routes _(slow)_

- hardening stop web server
   - Expected: missing_origin equals `HTTP/1.1 403 Forbidden|present`
   - Expected: oversized_login equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: api_state equals `HTTP/1.1 403 Forbidden|present`
   - Expected: websocket equals `HTTP/1.1 403 Forbidden|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port()
val pid = hardening_start_web_server(port)

val missing_origin = raw_http_summary(port, login_missing_origin_request(port), "forbidden_origin")
val oversized_login = raw_http_summary(port, login_oversized_request(port), "request_body_too_large")
val api_state = raw_http_summary(port, api_state_unauthorized_request(port), "\"error\": \"forbidden\"")
val websocket = raw_http_summary(port, websocket_unauthorized_request(port), "\"error\": \"forbidden\"")

hardening_stop_web_server(pid)

expect(missing_origin).to_equal("HTTP/1.1 403 Forbidden|present")
expect(oversized_login).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(api_state).to_equal("HTTP/1.1 403 Forbidden|present")
expect(websocket).to_equal("HTTP/1.1 403 Forbidden|present")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple web browser production hardening live endpoints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
