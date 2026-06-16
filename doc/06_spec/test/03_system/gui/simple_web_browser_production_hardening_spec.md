# Simple Web Browser Production Hardening Specification

> <details>

<!-- sdn-diagram:id=simple_web_browser_production_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_browser_production_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_browser_production_hardening_spec -> std
simple_web_browser_production_hardening_spec -> app
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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Browser Production Hardening Specification

## Scenarios

### Simple web browser production hardening live endpoints

<details>
<summary>Advanced: fails closed on unauthenticated browser HTTP and WebSocket routes</summary>

#### fails closed on unauthenticated browser HTTP and WebSocket routes _(slow)_

- Start a production-configured Simple Web server with a real token secret
- Send unauthenticated requests to login, API, and WebSocket routes
- hardening stop web server
- Verify every unauthenticated route fails closed with a concrete status and marker
   - Expected: missing_origin equals `HTTP/1.1 403 Forbidden|present`
   - Expected: oversized_login equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: api_state equals `HTTP/1.1 403 Forbidden|present`
   - Expected: api_widgets equals `HTTP/1.1 403 Forbidden|present`
   - Expected: websocket equals `HTTP/1.1 403 Forbidden|present`
   - Expected: websocket_query equals `HTTP/1.1 403 Forbidden|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port(0)
step("Start a production-configured Simple Web server with a real token secret")
val pid = hardening_start_web_server(port)

step("Send unauthenticated requests to login, API, and WebSocket routes")
val missing_origin = raw_http_summary(port, login_missing_origin_request(port), "forbidden_origin")
val oversized_login = raw_http_summary(port, login_oversized_request(port), "request_body_too_large")
val api_state = raw_http_summary(port, api_state_unauthorized_request(port), "\"error\": \"forbidden\"")
val api_widgets = raw_http_summary(port, api_widgets_unauthorized_request(port), "\"error\": \"forbidden\"")
val websocket = raw_http_summary(port, websocket_unauthorized_request(port), "\"error\": \"forbidden\"")
val websocket_query = raw_http_summary(port, websocket_query_token_request(port), "\"error\": \"forbidden\"")

hardening_stop_web_server(pid)

step("Verify every unauthenticated route fails closed with a concrete status and marker")
expect(missing_origin).to_equal("HTTP/1.1 403 Forbidden|present")
expect(oversized_login).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(api_state).to_equal("HTTP/1.1 403 Forbidden|present")
expect(api_widgets).to_equal("HTTP/1.1 403 Forbidden|present")
expect(websocket).to_equal("HTTP/1.1 403 Forbidden|present")
expect(websocket_query).to_equal("HTTP/1.1 403 Forbidden|present")
```

</details>


</details>

<details>
<summary>Advanced: mints an origin-bound token and redeems it for a websocket upgrade</summary>

#### mints an origin-bound token and redeems it for a websocket upgrade _(slow)_

- Start a fresh production-configured Simple Web server
- Request a login token from an allowed loopback origin
- Redeem the minted bearer token through the WebSocket subprotocol list
- hardening stop web server
- Verify login succeeds and the WebSocket upgrade echoes only the safe simple-ui protocol
   - Expected: http_status_line(login_response) equals `HTTP/1.1 200 OK`
   - Expected: websocket equals `HTTP/1.1 101 Switching Protocols|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port(100)
step("Start a fresh production-configured Simple Web server")
val pid = hardening_start_web_server(port)

step("Request a login token from an allowed loopback origin")
val login_response = raw_http_request(port, login_allowed_request(port))
val token = http_json_string_field(login_response, "token")

step("Redeem the minted bearer token through the WebSocket subprotocol list")
val websocket_response = raw_http_request(port, websocket_authorized_request(port, token))
val websocket = "{http_status_line(websocket_response)}|{http_marker(websocket_response, "Sec-WebSocket-Protocol: simple-ui")}"

hardening_stop_web_server(pid)

step("Verify login succeeds and the WebSocket upgrade echoes only the safe simple-ui protocol")
expect(http_status_line(login_response)).to_equal("HTTP/1.1 200 OK")
expect(token.len()).to_be_greater_than(20)
expect(websocket).to_equal("HTTP/1.1 101 Switching Protocols|present")
```

</details>


</details>

<details>
<summary>Advanced: rate limits allowed origin login bursts</summary>

#### rate limits allowed origin login bursts _(slow)_

- Start a fresh production-configured Simple Web server
- Spend the allowed login burst budget from an allowed loopback origin
- last allowed = raw http summary
- Send one more login request in the same fixed window
- hardening stop web server
- Verify the burst budget allows the configured count and rejects the next request
   - Expected: last_allowed equals `HTTP/1.1 200 OK|present`
   - Expected: limited equals `HTTP/1.1 429 Too Many Requests|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port(200)
step("Start a fresh production-configured Simple Web server")
val pid = hardening_start_web_server(port)

step("Spend the allowed login burst budget from an allowed loopback origin")
var attempts = 0
var last_allowed = ""
while attempts < UI_WEB_LOGIN_RATE_MAX_ATTEMPTS:
    last_allowed = raw_http_summary(port, login_allowed_request(port), "\"token\"")
    attempts = attempts + 1

step("Send one more login request in the same fixed window")
val limited = raw_http_summary(port, login_allowed_request(port), "login_rate_limited")

hardening_stop_web_server(pid)

step("Verify the burst budget allows the configured count and rejects the next request")
expect(last_allowed).to_equal("HTTP/1.1 200 OK|present")
expect(limited).to_equal("HTTP/1.1 429 Too Many Requests|present")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` |
| Updated | 2026-06-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple web browser production hardening live endpoints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
