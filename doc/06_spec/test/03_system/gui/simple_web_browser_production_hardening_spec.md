# Simple Web Browser Production Hardening Live Endpoint Specification

> Verifies selected Feature C and NFR C browser production hardening behavior for the live Simple Web HTTP/WebSocket boundary.

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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Browser Production Hardening Live Endpoint Specification

Verifies selected Feature C and NFR C browser production hardening behavior for the live Simple Web HTTP/WebSocket boundary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/nfr/simple_web_browser_production_hardening.md |
| Source | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected Feature C and NFR C browser production hardening behavior for
the live Simple Web HTTP/WebSocket boundary.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Traceability:** REQ-WEB-HARD-003, REQ-WEB-HARD-006, REQ-WEB-HARD-007, REQ-WEB-HARD-008, REQ-WEB-HARD-009, REQ-WEB-HARD-010, REQ-WEB-HARD-011, REQ-WEB-HARD-012, NFR-WEB-HARD-003, NFR-WEB-HARD-004, NFR-WEB-HARD-005, NFR-WEB-HARD-006, NFR-WEB-HARD-007, NFR-WEB-HARD-008, NFR-WEB-HARD-010, NFR-WEB-HARD-011

## Scenarios

### Simple web browser production hardening live endpoints

<details>
<summary>Advanced: fails closed on unauthenticated browser HTTP and WebSocket routes</summary>

#### fails closed on unauthenticated browser HTTP and WebSocket routes _(slow)_

- Start a production-configured Simple Web server with a real token secret
- Send unauthenticated requests to login, API, and WebSocket routes
- hardening stop web server
- Verify every unauthenticated route fails closed and the root document has browser security headers
   - Expected: missing_origin equals `HTTP/1.1 403 Forbidden|present`
   - Expected: oversized_head equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_request_line equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_header_line equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_login equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: malformed_login equals `HTTP/1.1 400 Bad Request|present`
   - Expected: api_state equals `HTTP/1.1 403 Forbidden|present`
   - Expected: api_widgets equals `HTTP/1.1 403 Forbidden|present`
   - Expected: resume equals `HTTP/1.1 403 Forbidden|present`
   - Expected: websocket equals `HTTP/1.1 403 Forbidden|present`
   - Expected: legacy_websocket equals `HTTP/1.1 404 Not Found|present`
   - Expected: websocket_query equals `HTTP/1.1 403 Forbidden|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port(0)
step("Start a production-configured Simple Web server with a real token secret")
val pid = hardening_start_web_server(port)

step("Send unauthenticated requests to login, API, and WebSocket routes")
val missing_origin = raw_http_summary(port, login_missing_origin_request(port), "forbidden_origin")
val oversized_head = raw_http_summary(port, oversized_head_request(port), "request_head_too_large")
val oversized_request_line = raw_http_summary(port, oversized_request_line_request(port), "request_head_too_large")
val oversized_header_line = raw_http_summary(port, oversized_header_line_request(port), "request_head_too_large")
val oversized_login = raw_http_summary(port, login_oversized_request(port), "request_body_too_large")
val malformed_login = raw_http_summary(port, login_malformed_framing_request(port), "invalid_request_framing")
val api_state = raw_http_summary(port, api_state_unauthorized_request(port), "\"error\": \"forbidden\"")
val api_widgets = raw_http_summary(port, api_widgets_unauthorized_request(port), "\"error\": \"forbidden\"")
val resume = raw_http_summary(port, resume_unauthorized_request(port), "\"error\": \"forbidden\"")
val websocket = raw_http_summary(port, websocket_unauthorized_request(port), "\"error\": \"forbidden\"")
val legacy_websocket = raw_http_summary(port, legacy_websocket_unauthorized_request(port), "\"error\": \"not_found\"")
val websocket_query = raw_http_summary(port, websocket_query_token_request(port), "\"error\": \"forbidden\"")
val root_page = raw_http_request(port, root_page_request(port))

hardening_stop_web_server(pid)

step("Verify every unauthenticated route fails closed and the root document has browser security headers")
expect(missing_origin).to_equal("HTTP/1.1 403 Forbidden|present")
expect(oversized_head).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_request_line).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_header_line).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_login).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(malformed_login).to_equal("HTTP/1.1 400 Bad Request|present")
expect(api_state).to_equal("HTTP/1.1 403 Forbidden|present")
expect(api_widgets).to_equal("HTTP/1.1 403 Forbidden|present")
expect(resume).to_equal("HTTP/1.1 403 Forbidden|present")
expect(websocket).to_equal("HTTP/1.1 403 Forbidden|present")
expect(legacy_websocket).to_equal("HTTP/1.1 404 Not Found|present")
expect(websocket_query).to_equal("HTTP/1.1 403 Forbidden|present")
expect(root_page).to_contain("X-Frame-Options: DENY")
expect(root_page).to_contain("Referrer-Policy: no-referrer")
expect(root_page).to_contain("Content-Security-Policy: default-src 'self'")
```

</details>


</details>

<details>
<summary>Advanced: mints an origin-bound token and redeems it for a websocket upgrade</summary>

#### mints an origin-bound token and redeems it for a websocket upgrade _(slow)_

- Start a fresh production-configured Simple Web server
- Request a login token from an allowed loopback origin
- Redeem the minted bearer token through resume and WebSocket routes
- hardening stop web server
- Verify login succeeds, canonical GET upgrades are accepted, legacy routes are hidden, and POST upgrades are rejected
   - Expected: http_status_line(login_response) equals `HTTP/1.1 200 OK`
   - Expected: malformed_resume equals `HTTP/1.1 400 Bad Request|present`
   - Expected: valid_resume equals `HTTP/1.1 200 OK|present`
   - Expected: oversized_resume equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: websocket equals `HTTP/1.1 101 Switching Protocols|present`
   - Expected: legacy_websocket equals `HTTP/1.1 404 Not Found|present`
   - Expected: lowercase_websocket equals `HTTP/1.1 101 Switching Protocols|present`
   - Expected: websocket_post equals `HTTP/1.1 405 Method Not Allowed|present`
   - Expected: legacy_websocket_post equals `HTTP/1.1 404 Not Found|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port(100)
step("Start a fresh production-configured Simple Web server")
val pid = hardening_start_web_server(port)

step("Request a login token from an allowed loopback origin")
val login_response = raw_http_request(port, login_allowed_request(port))
val token = http_json_string_field(login_response, "token")

step("Redeem the minted bearer token through resume and WebSocket routes")
val malformed_resume_body = "{\"session_id\":\"session-1\",\"snapshot_revision\":\"bad\",\"last_sequence\":0}"
val malformed_resume_response = raw_http_request(port, resume_authorized_request(port, token, malformed_resume_body))
val malformed_resume = "{http_status_line(malformed_resume_response)}|{http_marker(malformed_resume_response, "invalid_resume_body")}"
val valid_resume_body = "{\"session_id\":\"session-1\",\"snapshot_revision\":42,\"last_sequence\":7}"
val valid_resume_response = raw_http_request(port, resume_authorized_request(port, token, valid_resume_body))
val valid_resume = "{http_status_line(valid_resume_response)}|{http_marker(valid_resume_response, "\"session_id\": \"session-1\"")}"
val oversized_resume = raw_http_summary(port, resume_authorized_oversized_request(port, token), "request_body_too_large")
val websocket_response = raw_http_request(port, websocket_authorized_request(port, token))
val websocket = "{http_status_line(websocket_response)}|{http_marker(websocket_response, "Sec-WebSocket-Protocol: simple-ui")}"
val legacy_websocket_response = raw_http_request(port, legacy_websocket_authorized_request(port, token))
val legacy_websocket = "{http_status_line(legacy_websocket_response)}|{http_marker(legacy_websocket_response, "not_found")}"
val lowercase_websocket_response = raw_http_request(port, websocket_lowercase_authorized_request(port, token))
val lowercase_websocket = "{http_status_line(lowercase_websocket_response)}|{http_marker(lowercase_websocket_response, "Sec-WebSocket-Protocol: simple-ui")}"
val websocket_post_response = raw_http_request(port, websocket_post_authorized_request(port, token))
val websocket_post = "{http_status_line(websocket_post_response)}|{http_marker(websocket_post_response, "method_not_allowed")}"
val legacy_websocket_post_response = raw_http_request(port, legacy_websocket_post_authorized_request(port, token))
val legacy_websocket_post = "{http_status_line(legacy_websocket_post_response)}|{http_marker(legacy_websocket_post_response, "not_found")}"

hardening_stop_web_server(pid)

step("Verify login succeeds, canonical GET upgrades are accepted, legacy routes are hidden, and POST upgrades are rejected")
expect(http_status_line(login_response)).to_equal("HTTP/1.1 200 OK")
expect(login_response).to_contain("Cache-Control: no-store")
expect(login_response).to_contain("Pragma: no-cache")
expect(login_response).to_contain("X-Content-Type-Options: nosniff")
expect(login_response).to_contain("X-Request-Id: browser-hardening-login")
expect(token.len()).to_be_greater_than(20)
expect(malformed_resume).to_equal("HTTP/1.1 400 Bad Request|present")
expect(valid_resume).to_equal("HTTP/1.1 200 OK|present")
expect(valid_resume_response).to_contain("Cache-Control: no-store")
expect(valid_resume_response).to_contain("Pragma: no-cache")
expect(valid_resume_response).to_contain("X-Content-Type-Options: nosniff")
expect(oversized_resume).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(websocket).to_equal("HTTP/1.1 101 Switching Protocols|present")
expect(legacy_websocket).to_equal("HTTP/1.1 404 Not Found|present")
expect(lowercase_websocket).to_equal("HTTP/1.1 101 Switching Protocols|present")
expect(websocket_post).to_equal("HTTP/1.1 405 Method Not Allowed|present")
expect(legacy_websocket_post).to_equal("HTTP/1.1 404 Not Found|present")
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

<details>
<summary>Advanced: measures warm browser auth path latency</summary>

#### measures warm browser auth path latency _(slow)_

- Start and warm a production-configured Simple Web server
- Measure a warmed login plus authenticated WebSocket upgrade
- hardening stop web server
- Verify the warmed browser auth path succeeds inside the local latency budget
   - Expected: http_status_line(warmup_response) equals `HTTP/1.1 200 OK`
   - Expected: http_status_line(login_response) equals `HTTP/1.1 200 OK`
   - Expected: websocket equals `HTTP/1.1 101 Switching Protocols|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port(250)
step("Start and warm a production-configured Simple Web server")
val pid = hardening_start_web_server(port)
val warmup_response = raw_http_request(port, login_allowed_request(port))

step("Measure a warmed login plus authenticated WebSocket upgrade")
val start_ms = rt_time_ms()
val login_response = raw_http_request(port, login_allowed_request(port))
val token = http_json_string_field(login_response, "token")
val websocket_response = raw_http_request(port, websocket_authorized_request(port, token))
val elapsed_ms = rt_time_ms() - start_ms
val websocket = "{http_status_line(websocket_response)}|{http_marker(websocket_response, "Sec-WebSocket-Protocol: simple-ui")}"

hardening_stop_web_server(pid)

step("Verify the warmed browser auth path succeeds inside the local latency budget")
expect(http_status_line(warmup_response)).to_equal("HTTP/1.1 200 OK")
expect(http_status_line(login_response)).to_equal("HTTP/1.1 200 OK")
expect(token.len()).to_be_greater_than(20)
expect(websocket).to_equal("HTTP/1.1 101 Switching Protocols|present")
expect(elapsed_ms).to_be_less_than(10000u64)
```

</details>


</details>

<details>
<summary>Advanced: rejects query bearer websocket compatibility even when deprecated env is set</summary>

#### rejects query bearer websocket compatibility even when deprecated env is set _(slow)_

- Start a production-configured Simple Web server with query-token compatibility enabled
- Mint a token and try to redeem it through the query bearer path
- hardening stop web server
- Verify the deprecated compatibility environment variable is non-authorizing
   - Expected: http_status_line(login_response) equals `HTTP/1.1 200 OK`
   - Expected: websocket equals `HTTP/1.1 403 Forbidden|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port(300)
step("Start a production-configured Simple Web server with query-token compatibility enabled")
val pid = hardening_start_web_server_with_query_tokens(port)

step("Mint a token and try to redeem it through the query bearer path")
val login_response = raw_http_request(port, login_allowed_request(port))
val token = http_json_string_field(login_response, "token")
val websocket_response = raw_http_request(port, websocket_query_token_authorized_request(port, token))
val websocket = "{http_status_line(websocket_response)}|{http_marker(websocket_response, "forbidden")}"

hardening_stop_web_server(pid)

step("Verify the deprecated compatibility environment variable is non-authorizing")
expect(http_status_line(login_response)).to_equal("HTTP/1.1 200 OK")
expect(token.len()).to_be_greater_than(20)
expect(websocket).to_equal("HTTP/1.1 403 Forbidden|present")
```

</details>


</details>

<details>
<summary>Advanced: rate limits shared wm login bursts</summary>

#### rate limits shared wm login bursts _(slow)_

- Start a shared-WM Simple Web server with a real token secret
- Reject an oversized shared-WM request head before route dispatch
- Spend the shared-WM login burst budget from an allowed loopback origin
- last allowed = raw http summary
- Send one more shared-WM login request in the same fixed window
- hardening stop web server
- Verify the shared-WM request-head cap and burst budget
   - Expected: oversized_head equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_request_line equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_header_line equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_login_body equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: last_allowed equals `HTTP/1.1 200 OK|present`
   - Expected: limited equals `HTTP/1.1 429 Too Many Requests|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = hardening_free_port(400)
step("Start a shared-WM Simple Web server with a real token secret")
val pid = hardening_start_shared_wm_server(port)

step("Reject an oversized shared-WM request head before route dispatch")
val oversized_head = raw_http_summary(port, oversized_head_request(port), "request_head_too_large")
val oversized_request_line = raw_http_summary(port, oversized_request_line_request(port), "request_head_too_large")
val oversized_header_line = raw_http_summary(port, oversized_header_line_request(port), "request_head_too_large")
val oversized_login_body = raw_http_summary(port, login_oversized_request(port), "request_body_too_large")

step("Spend the shared-WM login burst budget from an allowed loopback origin")
var attempts = 0
var last_allowed = ""
while attempts < UI_WEB_LOGIN_RATE_MAX_ATTEMPTS:
    last_allowed = raw_http_summary(port, login_allowed_request(port), "\"token\"")
    attempts = attempts + 1

step("Send one more shared-WM login request in the same fixed window")
val limited = raw_http_summary(port, login_allowed_request(port), "login_rate_limited")

hardening_stop_web_server(pid)

step("Verify the shared-WM request-head cap and burst budget")
expect(oversized_head).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_request_line).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_header_line).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_login_body).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(last_allowed).to_equal("HTTP/1.1 200 OK|present")
expect(limited).to_equal("HTTP/1.1 429 Too Many Requests|present")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/simple_web_browser_production_hardening.md](doc/02_requirements/nfr/simple_web_browser_production_hardening.md)


</details>
