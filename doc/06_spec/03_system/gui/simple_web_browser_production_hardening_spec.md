# Simple Web Browser Production Hardening Live Endpoint Specification

> Verifies selected Feature C and NFR C browser production hardening behavior for the live Simple Web HTTP/WebSocket boundary.

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
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/05_design/ui/web/simple_web_browser_production_hardening.md |
| Research | doc/01_research/domain/simple_web_browser_production_hardening.md |
| Source | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected Feature C and NFR C browser production hardening behavior for
the live Simple Web HTTP/WebSocket boundary.

**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Design:** doc/05_design/ui/web/simple_web_browser_production_hardening.md
**Architecture:** doc/04_architecture/ui/simple_web_browser_production_hardening.md
**Research:** doc/01_research/local/simple_web_browser_production_hardening.md
**Research:** doc/01_research/domain/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Traceability:** REQ-WEB-HARD-003, REQ-WEB-HARD-006, REQ-WEB-HARD-007, REQ-WEB-HARD-008, REQ-WEB-HARD-009, REQ-WEB-HARD-010, REQ-WEB-HARD-011, REQ-WEB-HARD-012, NFR-WEB-HARD-003, NFR-WEB-HARD-004, NFR-WEB-HARD-005, NFR-WEB-HARD-006, NFR-WEB-HARD-007, NFR-WEB-HARD-008, NFR-WEB-HARD-010, NFR-WEB-HARD-011

## Syntax

Run the focused executable production hardening spec from the repository root:

```sh
bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360
```

Regenerate the manual evidence after changing this file:

```sh
SIMPLE_LIB=src bin/simple spipe-docgen test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output doc/06_spec --no-index
```

The spec launches a local Simple Web server with `SIMPLE_UI_WEB_TOKEN_SECRET`
set to a deterministic test secret. Each scenario chooses a pid-offset port,
waits for the local listener, exercises raw HTTP requests through `TcpStream`,
and stops the child process before assertions are reported.

Shared-WM coverage is enabled through `SIMPLE_UI_WEB_SHARED_WM=1` and
`SIMPLE_UI_WEB_PORT=<port>`. Deprecated query-token compatibility is exercised
through `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1`, but production behavior must still
reject query bearer tokens.

## Examples

Unauthenticated browser entrypoints must fail closed:

```text
GET /api/state              -> 403 forbidden
GET /api/widgets            -> 403 forbidden
GET /ui/resume              -> 403 forbidden
GET /ui/ws                  -> 403 forbidden
GET /ws                     -> 404 not_found
GET /ui/ws?token=<bearer>   -> 403 forbidden
```

Authorized browser entrypoints must accept only the production path:

```text
POST /ui/login              -> 200 token
POST /ui/resume             -> 200 session resume response
GET /ui/ws + bearer subprot -> 101 Switching Protocols
POST /ui/ws + bearer        -> 405 method_not_allowed
POST /ws + bearer           -> 404 not_found
```

Document and script responses must include browser hardening headers:

```text
/                  -> X-Frame-Options, Referrer-Policy, Content-Security-Policy
/wm/native_window  -> X-Frame-Options, Referrer-Policy, Content-Security-Policy
/wm.js             -> Cache-Control, Pragma, X-Content-Type-Options
/retained_renderer.js -> Cache-Control, Pragma, X-Content-Type-Options
```

Request-boundary guards must fail before route-specific work:

```text
oversized request head      -> 413 request_head_too_large
oversized request line      -> 413 request_head_too_large
oversized header line       -> 413 request_head_too_large
oversized unauth body       -> 413 request_body_too_large
malformed body framing      -> 400 invalid_request_framing
```

Hidden browser fallback routes must use the same hardened JSON response path as
named routes:

```text
GET /hidden-browser-production-gap -> 404 {"error": "not_found"}
```

## Production Evidence Scope

This spec is the live endpoint gate for browser-facing production behavior. It
does not mock HTTP parsing, bearer-token issuance, WebSocket upgrades, route
dispatch, or static script delivery. The scenarios exercise the normal web
server and the shared-WM web server through TCP so regressions in hidden server
paths are visible to the generated manual.

The unauthenticated scenario proves that shown browser entrypoints do not expose
state without a valid origin-bound token. It also proves hidden compatibility
surfaces, including legacy `/ws` and query bearer tokens, remain non-authorizing
in production mode.

The positive auth scenario proves the intended login, resume, and WebSocket
upgrade path still works after the fail-closed guards are applied. It also
checks that malformed resume bodies and oversized resume bodies are rejected
with typed errors instead of partial state recovery.

The login burst scenarios prove the normal and shared-WM login routes enforce
the configured fixed-window budget. The shared-WM scenario also checks route
parity for `/wm.js` and `/retained_renderer.js`, including no-store, no-cache,
and nosniff script headers. Both normal and shared-WM scenarios also exercise
`/hidden-browser-production-gap` to prove unknown browser routes inherit
no-store, no-cache, and nosniff headers from the centralized JSON fallback.

The latency scenario is intentionally broad enough to include token minting and
WebSocket authorization. Its purpose is a local regression guard for accidental
slow startup-path work in the warmed browser auth path, not a replacement for
the external native rendering performance gates.

The external native rendering gates remain in
`doc/03_plan/agent_tasks/simple_web_browser_external_native_readback_proof.md`.
Those gates require hosts with macOS Metal, AMD ROCm/HIP, Windows DirectX, and
real browser WebGPU readback support. This local spec complements that follow-up
by proving the live browser server boundary is production-hardened on this host.

## Scenarios

### Simple web browser production hardening live endpoints

<details>
<summary>Advanced: fails closed on unauthenticated browser HTTP and WebSocket routes</summary>

#### fails closed on unauthenticated browser HTTP and WebSocket routes _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-HARD-003
# @req REQ-WEB-HARD-006
# @req REQ-WEB-HARD-007
# @req REQ-WEB-HARD-008
# @req REQ-WEB-HARD-009
# @req REQ-WEB-HARD-010
# @req REQ-WEB-HARD-011
# @req REQ-WEB-HARD-012
```

</details>


</details>

<details>
<summary>Advanced: mints an origin-bound token and redeems it for a websocket upgrade</summary>

#### mints an origin-bound token and redeems it for a websocket upgrade _(slow)_

- mints an origin-bound token and redeems it for a websocket upgrade
- Start a fresh production-configured Simple Web server
- Extract the server bootstrap grant and reject an attacker-chosen grant from another allowed localhost port
- Redeem the minted bearer token through resume and WebSocket routes
- Verify login succeeds, canonical GET upgrades are accepted, legacy routes are hidden, and POST upgrades are rejected
   - Expected: http_status_line(login_response) equals `HTTP/1.1 200 OK`
   - Expected: login_grant.len() equals `64`
   - Expected: http_status_line(attacker_response) equals `HTTP/1.1 403 Forbidden`
   - Expected: http_status_line(missing_grant_response) equals `HTTP/1.1 403 Forbidden`
   - Expected: issued_token_grant_id.len() equals `64`
   - Expected: http_status_line(replay_response) equals `HTTP/1.1 403 Forbidden`
   - Expected: http_status_line(api_state_response) equals `HTTP/1.1 200 OK`
   - Expected: http_status_line(api_widgets_response) equals `HTTP/1.1 200 OK`
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

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mints an origin-bound token and redeems it for a websocket upgrade")
"""The positive production path must mint a token for the request origin and accept that token during WebSocket upgrade."""
val port = hardening_free_port(100)
step("Start a fresh production-configured Simple Web server")
val pid = hardening_start_web_server(port)

step("Extract the server bootstrap grant and reject an attacker-chosen grant from another allowed localhost port")
val root_response = raw_http_request(port, root_page_request(port))
val login_grant = http_meta_content(root_response, "simple-ui-login-grant")
val attacker_response = raw_http_request(port, login_attacker_request(port))
val missing_grant_response = raw_http_request(port, login_missing_grant_request(port))
val login_response = raw_http_request(port, login_allowed_request(port, login_grant))
val token = http_json_string_field(login_response, "token")
val issued_token_grant_id = token_grant_id(token)
val replay_response = raw_http_request(port, login_allowed_request(port, issued_token_grant_id))

step("Redeem the minted bearer token through resume and WebSocket routes")
val malformed_resume_body = "{\"session_id\":\"session-1\",\"snapshot_revision\":\"bad\",\"last_sequence\":0}"
val malformed_resume_response = raw_http_request(port, resume_authorized_request(port, token, malformed_resume_body))
val malformed_resume = "{http_status_line(malformed_resume_response)}|{http_marker(malformed_resume_response, "invalid_resume_body")}"
val api_state_response = raw_http_request(port, api_state_authorized_request(port, token))
val api_widgets_response = raw_http_request(port, api_widgets_authorized_request(port, token))
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
expect(login_grant.len()).to_equal(64)
expect(http_status_line(attacker_response)).to_equal("HTTP/1.1 403 Forbidden")
expect(attacker_response.contains("\"token\"")).to_be(false)
expect(http_status_line(missing_grant_response)).to_equal("HTTP/1.1 403 Forbidden")
expect(missing_grant_response.contains("\"token\"")).to_be(false)
expect(issued_token_grant_id.len()).to_equal(64)
expect(issued_token_grant_id == login_grant).to_be(false)
expect(token.contains(login_grant)).to_be(false)
expect(http_status_line(replay_response)).to_equal("HTTP/1.1 403 Forbidden")
expect(replay_response.contains("\"token\"")).to_be(false)
expect(login_response).to_contain("Cache-Control: no-store")
expect(login_response).to_contain("Pragma: no-cache")
expect(login_response).to_contain("X-Content-Type-Options: nosniff")
expect(login_response).to_contain("X-Request-Id: browser-hardening-login")
expect(token.len()).to_be_greater_than(20)
expect(http_status_line(api_state_response)).to_equal("HTTP/1.1 200 OK")
expect(api_state_response).to_contain("Cache-Control: no-store")
expect(api_state_response).to_contain("Pragma: no-cache")
expect(api_state_response).to_contain("X-Content-Type-Options: nosniff")
expect(http_status_line(api_widgets_response)).to_equal("HTTP/1.1 200 OK")
expect(api_widgets_response).to_contain("Cache-Control: no-store")
expect(api_widgets_response).to_contain("Pragma: no-cache")
expect(api_widgets_response).to_contain("X-Content-Type-Options: nosniff")
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

- rate limits allowed origin login bursts
- Start a fresh production-configured Simple Web server
- Spend the allowed login burst budget from an allowed loopback origin
- Send one more login request in the same fixed window
- Verify the burst budget allows the configured count and rejects the next request
   - Expected: last_allowed equals `HTTP/1.1 200 OK|present`
   - Expected: limited equals `HTTP/1.1 429 Too Many Requests|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rate limits allowed origin login bursts")
"""The production login endpoint must bound repeated token mint requests even when the Origin is allowed."""
val port = hardening_free_port(200)
step("Start a fresh production-configured Simple Web server")
val pid = hardening_start_web_server(port)
val login_grant = http_meta_content(raw_http_request(port, root_page_request(port)), "simple-ui-login-grant")

step("Spend the allowed login burst budget from an allowed loopback origin")
var attempts = 0
var last_allowed = ""
while attempts < UI_WEB_LOGIN_RATE_MAX_ATTEMPTS:
    last_allowed = raw_http_summary(port, login_allowed_request(port, login_grant), "\"token\"")
    attempts = attempts + 1

step("Send one more login request in the same fixed window")
val limited = raw_http_summary(port, login_allowed_request(port, login_grant), "login_rate_limited")

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

- measures warm browser auth path latency
- Start and warm a production-configured Simple Web server
- Measure a warmed login plus authenticated WebSocket upgrade
- Verify the warmed browser auth path succeeds inside the local latency budget
   - Expected: http_status_line(warmup_response) equals `HTTP/1.1 200 OK`
   - Expected: http_status_line(login_response) equals `HTTP/1.1 200 OK`
   - Expected: websocket equals `HTTP/1.1 101 Switching Protocols|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("measures warm browser auth path latency")
"""A warmed production server must complete token minting and authenticated WebSocket upgrade within a bounded local latency budget."""
val port = hardening_free_port(250)
step("Start and warm a production-configured Simple Web server")
val pid = hardening_start_web_server(port)
val login_grant = http_meta_content(raw_http_request(port, root_page_request(port)), "simple-ui-login-grant")
val warmup_response = raw_http_request(port, login_allowed_request(port, login_grant))

step("Measure a warmed login plus authenticated WebSocket upgrade")
val start_ms = current_time_ms()
val login_response = raw_http_request(port, login_allowed_request(port, login_grant))
val token = http_json_string_field(login_response, "token")
val websocket_response = raw_http_request(port, websocket_authorized_request(port, token))
val elapsed_ms = current_time_ms() - start_ms
val websocket = "{http_status_line(websocket_response)}|{http_marker(websocket_response, "Sec-WebSocket-Protocol: simple-ui")}"

hardening_stop_web_server(pid)

step("Verify the warmed browser auth path succeeds inside the local latency budget")
expect(http_status_line(warmup_response)).to_equal("HTTP/1.1 200 OK")
expect(http_status_line(login_response)).to_equal("HTTP/1.1 200 OK")
expect(token.len()).to_be_greater_than(20)
expect(websocket).to_equal("HTTP/1.1 101 Switching Protocols|present")
expect(elapsed_ms).to_be_less_than(10000)
```

</details>


</details>

<details>
<summary>Advanced: rejects query bearer websocket compatibility even when deprecated env is set</summary>

#### rejects query bearer websocket compatibility even when deprecated env is set _(slow)_

- rejects query bearer websocket compatibility even when deprecated env is set
- Start a production-configured Simple Web server with query-token compatibility enabled
- Mint a token and try to redeem it through the query bearer path
- Verify the deprecated compatibility environment variable is non-authorizing
   - Expected: http_status_line(login_response) equals `HTTP/1.1 200 OK`
   - Expected: websocket equals `HTTP/1.1 403 Forbidden|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects query bearer websocket compatibility even when deprecated env is set")
"""Production auth must reject query bearer tokens even when the old compatibility environment variable is present."""
val port = hardening_free_port(300)
step("Start a production-configured Simple Web server with query-token compatibility enabled")
val pid = hardening_start_web_server_with_query_tokens(port)
val login_grant = http_meta_content(raw_http_request(port, root_page_request(port)), "simple-ui-login-grant")

step("Mint a token and try to redeem it through the query bearer path")
val login_response = raw_http_request(port, login_allowed_request(port, login_grant))
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

- rate limits shared wm login bursts
- Start a shared-WM Simple Web server with a real token secret
- Reject an oversized shared-WM request head before route dispatch
- Fetch shared-WM browser script responses
- Spend the shared-WM login burst budget from an allowed loopback origin
- Send one more shared-WM login request in the same fixed window
- Verify the shared-WM request-head cap and burst budget
   - Expected: oversized_head equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_request_line equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_header_line equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: oversized_login_body equals `HTTP/1.1 413 Payload Too Large|present`
   - Expected: login_grant.len() equals `64`
   - Expected: http_status_line(attacker_response) equals `HTTP/1.1 403 Forbidden`
   - Expected: http_status_line(missing_grant_response) equals `HTTP/1.1 403 Forbidden`
   - Expected: shared_token_grant_id.len() equals `64`
   - Expected: http_status_line(replay_response) equals `HTTP/1.1 403 Forbidden`
   - Expected: last_allowed equals `HTTP/1.1 200 OK|present`
   - Expected: limited equals `HTTP/1.1 429 Too Many Requests|present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 84 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rate limits shared wm login bursts")
"""The shared WM web server has a separate login path and must enforce the same burst limit as normal run_web."""
val port = hardening_free_port(400)
step("Start a shared-WM Simple Web server with a real token secret")
val pid = hardening_start_shared_wm_server(port)

step("Reject an oversized shared-WM request head before route dispatch")
val oversized_head = raw_http_summary(port, oversized_head_request(port), "request_head_too_large")
val oversized_request_line = raw_http_summary(port, oversized_request_line_request(port), "request_head_too_large")
val oversized_header_line = raw_http_summary(port, oversized_header_line_request(port), "request_head_too_large")
val oversized_login_body = raw_http_summary(port, login_oversized_request(port), "request_body_too_large")

step("Fetch shared-WM browser script responses")
val shared_wm_script = raw_http_request(port, wm_script_request(port))
val shared_native_window = raw_http_request(port, native_window_request(port))
val shared_retained_renderer_script = raw_http_request(port, retained_renderer_script_request(port))
val shared_unknown_route = raw_http_request(port, unknown_route_request(port))
val login_grant = http_meta_content(raw_http_request(port, root_page_request(port)), "simple-ui-login-grant")
val attacker_response = raw_http_request(port, login_attacker_request(port))
val missing_grant_response = raw_http_request(port, login_missing_grant_request(port))
val initial_login_response = raw_http_request(port, login_allowed_request(port, login_grant))
val shared_token = http_json_string_field(initial_login_response, "token")
val shared_token_grant_id = token_grant_id(shared_token)
val replay_response = raw_http_request(port, login_allowed_request(port, shared_token_grant_id))

step("Spend the shared-WM login burst budget from an allowed loopback origin")
# Attacker, missing, valid, and token-claim replay requests consume four attempts.
var attempts = 4
var last_allowed = "{http_status_line(initial_login_response)}|{http_marker(initial_login_response, "\"token\"")}"
while attempts < UI_WEB_LOGIN_RATE_MAX_ATTEMPTS:
    last_allowed = raw_http_summary(port, login_allowed_request(port, login_grant), "\"token\"")
    attempts = attempts + 1

step("Send one more shared-WM login request in the same fixed window")
val limited = raw_http_summary(port, login_allowed_request(port, login_grant), "login_rate_limited")

hardening_stop_web_server(pid)

step("Verify the shared-WM request-head cap and burst budget")
expect(oversized_head).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_request_line).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_header_line).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(oversized_login_body).to_equal("HTTP/1.1 413 Payload Too Large|present")
expect(shared_wm_script).to_contain("Cache-Control: no-store")
expect(shared_wm_script).to_contain("Pragma: no-cache")
expect(shared_wm_script).to_contain("X-Content-Type-Options: nosniff")
expect(shared_native_window).to_contain("HTTP/1.1 200 OK")
expect(shared_native_window).to_contain("Cache-Control: no-store")
expect(shared_native_window).to_contain("Pragma: no-cache")
expect(shared_native_window).to_contain("Expires: 0")
expect(shared_native_window).to_contain("X-Frame-Options: DENY")
expect(shared_native_window).to_contain("X-DNS-Prefetch-Control: off")
expect(shared_native_window).to_contain("X-Permitted-Cross-Domain-Policies: none")
expect(shared_native_window).to_contain("Referrer-Policy: no-referrer")
expect(shared_native_window).to_contain("Permissions-Policy: camera=(), microphone=(), geolocation=(), payment=()")
expect(shared_native_window).to_contain("usb=(), serial=(), bluetooth=()")
expect(shared_native_window).to_contain("clipboard-read=(), clipboard-write=()")
expect(shared_native_window).to_contain("display-capture=(), screen-wake-lock=(), xr-spatial-tracking=()")
expect(shared_native_window).to_contain("Content-Security-Policy: default-src 'self'")
expect(shared_native_window).to_contain("Origin-Agent-Cluster: ?1")
expect(shared_native_window).to_contain("Cross-Origin-Embedder-Policy: require-corp")
expect(shared_native_window).to_contain("object-src 'none'")
expect(shared_retained_renderer_script).to_contain("HTTP/1.1 200 OK")
expect(shared_retained_renderer_script).to_contain("Cache-Control: no-store")
expect(shared_retained_renderer_script).to_contain("Pragma: no-cache")
expect(shared_retained_renderer_script).to_contain("X-Content-Type-Options: nosniff")
expect(shared_unknown_route).to_contain("HTTP/1.1 404 Not Found")
expect(shared_unknown_route).to_contain("\"error\": \"not_found\"")
expect(shared_unknown_route).to_contain("Cache-Control: no-store")
expect(shared_unknown_route).to_contain("Pragma: no-cache")
expect(shared_unknown_route).to_contain("X-Content-Type-Options: nosniff")
expect(login_grant.len()).to_equal(64)
expect(http_status_line(attacker_response)).to_equal("HTTP/1.1 403 Forbidden")
expect(attacker_response.contains("\"token\"")).to_be(false)
expect(http_status_line(missing_grant_response)).to_equal("HTTP/1.1 403 Forbidden")
expect(missing_grant_response.contains("\"token\"")).to_be(false)
expect(shared_token_grant_id.len()).to_equal(64)
expect(shared_token_grant_id == login_grant).to_be(false)
expect(shared_token.contains(login_grant)).to_be(false)
expect(http_status_line(replay_response)).to_equal("HTTP/1.1 403 Forbidden")
expect(replay_response.contains("\"token\"")).to_be(false)
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

- **Requirements:** `doc/02_requirements/nfr/simple_web_browser_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
- **Design:** `doc/05_design/ui/web/simple_web_browser_production_hardening.md`
- **Research:** `doc/01_research/domain/simple_web_browser_production_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-HARD-003`
- `REQ-WEB-HARD-006`
- `REQ-WEB-HARD-007`
- `REQ-WEB-HARD-008`
- `REQ-WEB-HARD-009`
- `REQ-WEB-HARD-010`
- `REQ-WEB-HARD-011`
- `REQ-WEB-HARD-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1a37dbbe05359f6223418fd465dbd9a35c9c46ea248e14e2690441544a49b22b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a37dbbe05359f6223418fd465dbd9a35c9c46ea248e14e2690441544a49b22b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a37dbbe05359f6223418fd465dbd9a35c9c46ea248e14e2690441544a49b22b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/gui/simple_web_browser_production_hardening_spec.spl
mirror: doc/06_spec/03_system/gui/simple_web_browser_production_hardening_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/simple_web_browser_production_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/simple_web_browser_production_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/simple_web_browser_production_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/simple_web_browser_production_hardening_spec.spl:451:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'fails closed on unauthenticated browser HTTP and WebSocket routes' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/gui/simple_web_browser_production_hardening_spec.spl:552:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mints an origin-bound token and redeems it for a websocket upgrade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/simple_web_browser_production_hardening_spec.spl:630:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rate limits allowed origin login bursts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/simple_web_browser_production_hardening_spec.spl:655:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures warm browser auth path latency' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
