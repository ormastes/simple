# Simple Web Browser Production Auth Hardening Specification

> Verifies selected Feature C and NFR C production authentication, origin, request-boundary, generated-client, and login burst behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Browser Production Auth Hardening Specification

Verifies selected Feature C and NFR C production authentication, origin, request-boundary, generated-client, and login burst behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/simple_web_browser_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/05_design/ui/web/simple_web_browser_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_production_hardening.md |
| Source | `test/01_unit/app/ui/web_auth_hardening_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected Feature C and NFR C production authentication, origin,
request-boundary, generated-client, and login burst behavior.

**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Design:** doc/05_design/ui/web/simple_web_browser_production_hardening.md
**Research:** doc/01_research/local/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Traceability:** REQ-WEB-HARD-001, REQ-WEB-HARD-002, REQ-WEB-HARD-003, REQ-WEB-HARD-004, REQ-WEB-HARD-005, REQ-WEB-HARD-008, REQ-WEB-HARD-011, NFR-WEB-HARD-001, NFR-WEB-HARD-002, NFR-WEB-HARD-003, NFR-WEB-HARD-004, NFR-WEB-HARD-005, NFR-WEB-HARD-010, NFR-WEB-HARD-011

## Syntax

Run this focused unit specification from the repository root:

```sh
bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter
```

Regenerate its manual after changing the executable specification:

```sh
bin/simple spipe-docgen test/01_unit/app/ui/web_auth_hardening_spec.spl --output doc/06_spec
```

## Security Model

Production startup requires a token-signing secret.

The insecure development fallback requires explicit opt-in.

TLS never accepts the insecure fallback.

Each server process owns a random 256-bit login grant.

Each server process also owns a distinct random token grant claim.

The login grant is rendered only as lowercase hex.

The root document publishes it through a same-origin meta element.

Generated browser JavaScript reads that meta element.

Generated WM JavaScript reads that meta element.

Static `wm.js` reads that meta element.

No client sends the former `legacy`, `wm`, or `dev` literals.

Login grant equality uses a constant-time comparison.

A missing login grant is forbidden.

An attacker-chosen login grant is forbidden.

The distinct token grant claim is forbidden as login proof.

Only the exact login grant is accepted.

The serialized token contains the token grant claim.

The serialized token does not contain the login grant.

The token remains bound to its accepted origin.

## Exact Oracles

```text
missing login grant                  -> forbidden
attacker-chosen login grant          -> forbidden
serialized token grant replay        -> forbidden
exact per-process login grant        -> ok
unsafe login-grant HTML input        -> no meta insertion
safe 64-character lowercase hex      -> exact meta insertion
```

The tests use exact status strings where policy has multiple outcomes.

The tests inspect response-producing client text directly.

The tests do not hide HTTP or token behavior behind boolean wrappers.

The tests reject static login grant literals in generated clients.

The tests require the positive `loginGrant()` request body expression.

## Origin And Bearer Rules

Missing login origins fail closed.

Disallowed login origins fail closed.

Default loopback policy accepts valid loopback origins with numeric ports.

Explicit allowlists remain exact.

Sensitive API state routes require a bearer.

Resume routes require a bearer.

WebSocket routes require a bearer.

Wrong-origin tokens fail verification.

Expired tokens fail verification.

Malformed tokens fail verification.

Query bearer decoding remains single-pass.

Bearer-like request identifiers are never reflected.

## Request Boundary Rules

Unauthenticated JSON bodies are bounded.

Oversized content lengths fail before allocation.

Duplicate content lengths are rejected.

Malformed content lengths are rejected.

Unsupported transfer encodings are rejected.

Request heads are bounded.

Request lines are bounded.

Individual header lines are bounded.

Inbound WebSocket frames are bounded.

Login attempts remain fixed-window rate limited.

## Response Rules

JSON responses are no-store.

JSON responses disable MIME sniffing.

HTML responses deny framing.

HTML responses disable referrer disclosure.

HTML responses use restrictive permissions policy.

HTML responses use a restrictive content security policy.

## Scope

This unit specification covers pure policy and generated-client contracts.

The live TCP behavior is covered by
`test/03_system/gui/simple_web_browser_production_hardening_spec.spl`.

Normal and shared-WM root extraction, mismatch rejection, token-claim replay
rejection, valid redemption, and rate limiting are live system-test concerns.

Renderer parity and host GPU evidence remain separate release gates.

No bootstrap, package, release, or deployment behavior is exercised here.

## Scenarios

### ui.web production auth hardening

#### requires explicit opt-in before using an insecure dev token secret

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_allow_insecure_dev_secret_flag("")).to_be(false)
expect(_allow_insecure_dev_secret_flag("0")).to_be(false)
expect(_allow_insecure_dev_secret_flag("1")).to_be(true)
expect(_allow_insecure_dev_secret_flag("true")).to_be(true)
```

</details>

#### keeps missing secrets fatal in TLS and production non-TLS modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_missing_secret_fatal(true, false)).to_be(true)
expect(_missing_secret_fatal(true, true)).to_be(true)
expect(_missing_secret_fatal(false, false)).to_be(true)
expect(_missing_secret_fatal(false, true)).to_be(false)
```

</details>

#### fails closed when login origin headers are missing or disallowed

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://localhost"])
val missing = guard.check("Host: localhost\n")
val disallowed = guard.check("Origin: https://evil.example\n")
val allowed = guard.check("Origin: https://localhost\n")
expect(missing.is_err()).to_be(true)
expect(disallowed.is_err()).to_be(true)
expect(allowed.is_ok()).to_be(true)
```

</details>

<details>
<summary>Advanced: allows loopback browser origins with ports only under the default policy</summary>

#### allows loopback browser origins with ports only under the default policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_guard = OriginGuard(allowed: ["https://localhost", "http://localhost"])
expect(_is_loopback_origin("http://localhost:8080")).to_be(true)
expect(_is_loopback_origin("https://127.0.0.1:8443")).to_be(true)
expect(_is_loopback_origin("http://[::1]:8080")).to_be(true)
expect(_is_loopback_origin("http://localhost:bad")).to_be(false)
expect(_is_loopback_origin("https://evil.example:8443")).to_be(false)
expect(default_guard.check("Origin: http://localhost:8080\n").is_ok()).to_be(true)
val strict_guard = OriginGuard(allowed: ["https://localhost"])
expect(strict_guard.check("Origin: http://localhost:8080\n").is_err()).to_be(true)
```

</details>


</details>

#### parses explicit origin allowlists as trimmed exact entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard.from_env_value(" https://app.example , http://localhost:8080, ")
expect(guard.check("Origin: https://app.example\n").is_ok()).to_be(true)
expect(guard.check("Origin: http://localhost:8080\n").is_ok()).to_be(true)
expect(guard.check("Origin: http://localhost:9090\n").is_err()).to_be(true)
```

</details>

#### requires origin-bound bearer tokens for sensitive api routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://localhost"])
val secret = "unit-test-secret"
val now = 1000u64
expect(ui_web_authorization_status("Origin: https://localhost\n", "/api/state", guard, secret, now)).to_equal("missing_bearer")
expect(ui_web_authorization_status("Origin: https://localhost\n", "/api/widgets", guard, secret, now)).to_equal("missing_bearer")
expect(ui_web_authorization_status("Origin: https://localhost\n", "/api/clients", guard, secret, now)).to_equal("missing_bearer")
expect(ui_web_authorization_status("Origin: https://evil.example\nAuthorization: Bearer malformed\n", "/api/state", guard, secret, now)).to_equal("forbidden_origin")
expect(ui_web_authorization_status("Origin: https://localhost\nAuthorization: Bearer malformed\n", "/api/state", guard, secret, now)).to_equal("invalid_bearer")
expect(ui_web_request_authorized("Origin: https://localhost\nAuthorization: Bearer malformed\n", "/api/state", guard, secret, now)).to_be(false)
```

</details>

#### requires origin-bound bearer tokens for websocket and resume routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://localhost"])
val secret = "unit-test-secret"
val token = SessionToken.issue("resume-grant", "https://localhost", 3600000u64, secret).serialize()
val headers = "Origin: https://localhost\nAuthorization: Bearer {token}\n"
val ws_headers = "Origin: https://localhost\nSec-WebSocket-Protocol: simple-ui, bearer.{token}\n"

expect(ui_web_authorization_status("Origin: https://localhost\n", "/ui/resume", guard, secret, 1000u64)).to_equal("missing_bearer")
expect(ui_web_authorization_status("Origin: https://evil.example\nAuthorization: Bearer {token}\n", "/ui/resume", guard, secret, 1000u64)).to_equal("forbidden_origin")
expect(ui_web_authorization_status("Origin: https://localhost\nAuthorization: Bearer malformed\n", "/ui/resume", guard, secret, 1000u64)).to_equal("invalid_bearer")
expect(ui_web_authorization_status(headers, "/ui/resume", guard, secret, 1000u64)).to_equal("ok")
expect(ui_web_authorization_status(ws_headers, "/ui/ws", guard, secret, 1000u64)).to_equal("ok")
```

</details>

#### rejects malformed, expired, and wrong-origin serialized tokens before authorization succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expired = SessionToken(token_id: "tok", grant_id: "grant", origin: "https://localhost", expires_at_ms: 100u64, signature: "sig").serialize()
val wrong_origin = SessionToken(token_id: "tok", grant_id: "grant", origin: "https://localhost", expires_at_ms: 5000u64, signature: "sig").serialize()

expect(SessionToken.parse("not-a-complete-token").is_err()).to_be(true)
expect(verify(expired, "https://localhost", "unit-test-secret", 101u64).is_err()).to_be(true)
expect(verify(wrong_origin, "https://other.example", "unit-test-secret", 1000u64).is_err()).to_be(true)
```

</details>

#### generates token-authenticated websocket clients for browser and wm paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy_js = generate_js(8080)
expect(legacy_js).to_contain("fetch('/ui/login'")
expect(legacy_js).to_contain("meta[name=\"simple-ui-login-grant\"]")
expect(legacy_js).to_contain("capability_grant: loginGrant()")
expect(legacy_js.contains("capability_grant: 'legacy'")).to_be(false)
expect(legacy_js).to_contain("new WebSocket(browserWsUrl(), ['simple-ui', 'bearer.' + encodeURIComponent(authToken)])")
expect(legacy_js).to_contain("return wsProto + '://' + wsHost + '/ui/ws'")
expect(legacy_js.contains("legacyWsUrl")).to_be(false)
expect(legacy_js.contains("/ws?token=")).to_be(false)
expect(legacy_js.contains("'/ws'")).to_be(false)
val wm_js = generate_wm_js(8080)
expect(wm_js).to_contain("fetch('/ui/login'")
expect(wm_js).to_contain("meta[name=\"simple-ui-login-grant\"]")
expect(wm_js).to_contain("capability_grant: loginGrant()")
expect(wm_js.contains("capability_grant: 'wm'")).to_be(false)
expect(wm_js).to_contain("new WebSocket(wsProto + '://' + wsHost + '/ui/ws', ['simple-ui', 'bearer.' + encodeURIComponent(authToken)])")
expect(wm_js.contains("/ui/ws?token=")).to_be(false)
val static_wm_js = rt_file_read_text("src/app/ui.web/wm.js")
expect(static_wm_js).to_contain("meta[name=\"simple-ui-login-grant\"]")
expect(static_wm_js).to_contain("capability_grant: loginGrant")
expect(static_wm_js.contains("capability_grant: 'dev'")).to_be(false)
expect(static_wm_js).to_contain("new WebSocket(url, ['simple-ui', 'bearer.' + encodeURIComponent(this.token)])")
expect(static_wm_js.contains("/ui/ws?token=")).to_be(false)
```

</details>

#### publishes and accepts only the exact server-owned bootstrap grant

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
val attacker_grant = "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789"
val token_grant_id = "1111111111111111111111111111111111111111111111111111111111111111"
val page = ui_web_with_login_grant("<html><head>\n<title>Simple</title></head></html>", grant)
val serialized = SessionToken.issue(token_grant_id, "http://localhost:8080", 3600000u64, "secret").serialize()
expect(page).to_contain("<meta name=\"simple-ui-login-grant\" content=\"{grant}\">")
expect(ui_web_with_login_grant("<html><head></head></html>", "not-hex")).to_equal("<html><head></head></html>")
expect(ui_web_login_grant_status("", grant)).to_equal("forbidden")
expect(ui_web_login_grant_status(attacker_grant, grant)).to_equal("forbidden")
expect(ui_web_login_grant_status(token_grant_id, grant)).to_equal("forbidden")
expect(ui_web_login_grant_status(grant, grant)).to_equal("ok")
expect(serialized.contains(grant)).to_be(false)
expect(serialized).to_contain(token_grant_id)
```

</details>

#### decodes browser-encoded query bearer tokens once before verification

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_query_percent_decode("abc%252Edef%253Aghi")).to_equal("abc%2Edef%3Aghi")
expect(ui_web_query_percent_decode("a%2Eb%2Fc%20d%2Be")).to_equal("a.b/c d+e")
```

</details>

#### sanitizes request ids without echoing bearer-like values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_sanitize_request_id("browser-req_01.2")).to_equal("browser-req_01.2")
expect(ui_web_sanitize_request_id("Bearer secret-token")).to_equal("")
expect(ui_web_request_id("X-Request-Id: browser-req-7\nAuthorization: Bearer secret-token\n", "fallback")).to_equal("browser-req-7")
expect(ui_web_request_id("X-Request-Id: Bearer secret-token\n", "fallback")).to_equal("fallback")
```

</details>

#### adds cache and sniffing guards to json responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ui_web_json_security_headers("application/json")
expect(headers).to_contain("Cache-Control: no-store")
expect(headers).to_contain("Pragma: no-cache")
expect(headers).to_contain("X-Content-Type-Options: nosniff")
expect(ui_web_json_security_headers("text/html")).to_equal("")
```

</details>

#### adds browser document security headers to html responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ui_web_html_security_headers("text/html")
expect(headers).to_contain("X-Content-Type-Options: nosniff")
expect(headers).to_contain("X-Frame-Options: DENY")
expect(headers).to_contain("Referrer-Policy: no-referrer")
expect(headers).to_contain("Permissions-Policy: camera=(), microphone=(), geolocation=(), payment=()")
expect(headers).to_contain("Content-Security-Policy: default-src 'self'")
expect(headers).to_contain("frame-ancestors 'none'")
expect(ui_web_html_security_headers("application/json")).to_equal("")
```

</details>

#### uses bounded shared json field extraction for auth path bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val login_body = "{\"capability_grant\":\"grant\\\"one\",\"snapshot_revision\":42,\"last_sequence\":7}"
expect(ui_web_auth_json_field(login_body, "capability_grant")).to_equal("grant\"one")
expect(ui_web_auth_json_field(login_body, "snapshot_revision")).to_equal("42")
expect(ui_web_auth_json_field(login_body, "last_sequence")).to_equal("7")
expect(ui_web_auth_json_field(login_body, "missing")).to_equal("")
val oversized = "x".repeat(UI_WEB_MAX_AUTH_JSON_BYTES + 1)
expect(ui_web_auth_json_field(oversized, "capability_grant")).to_equal("")
```

</details>

#### rejects malformed resume bodies after authorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = "{\"session_id\":\"session-1\",\"snapshot_revision\":42,\"last_sequence\":7}"
val missing_session = "{\"snapshot_revision\":42,\"last_sequence\":7}"
val invalid_revision = "{\"session_id\":\"session-1\",\"snapshot_revision\":\"4x\",\"last_sequence\":7}"
val invalid_sequence = "{\"session_id\":\"session-1\",\"snapshot_revision\":42,\"last_sequence\":\"7x\"}"
val oversized = "x".repeat(UI_WEB_MAX_AUTH_JSON_BYTES + 1)
expect(ui_web_resume_body_status(valid)).to_equal("ok")
expect(ui_web_resume_body_status(oversized)).to_equal("body_too_large")
expect(ui_web_resume_body_status(missing_session)).to_equal("missing_session_id")
expect(ui_web_resume_body_status(invalid_revision)).to_equal("invalid_snapshot_revision")
expect(ui_web_resume_body_status(invalid_sequence)).to_equal("invalid_last_sequence")
```

</details>

#### fails oversized unauthenticated login bodies from content length alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Host: 127.0.0.1\nOrigin: http://localhost:8080\nContent-Length: 8193\n"
expect(ui_web_content_length(headers)).to_equal(8193)
expect(ui_web_body_exceeds_unauth_limit(headers)).to_be(true)
expect(ui_web_request_body_status(headers)).to_equal("request_body_too_large")
```

</details>

#### rejects malformed or ambiguous request body framing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_request_body_status("Content-Length: 42\n")).to_equal("ok")
expect(ui_web_request_body_status("Content-Length: -1\n")).to_equal("invalid_request_framing")
expect(ui_web_request_body_status("Content-Length: nope\n")).to_equal("invalid_request_framing")
expect(ui_web_request_body_status("Content-Length: 4\nContent-Length: 4\n")).to_equal("invalid_request_framing")
expect(ui_web_request_body_status("Transfer-Encoding: chunked\n")).to_equal("invalid_request_framing")
expect(ui_web_request_body_framing_valid("Content-Length: 42\n")).to_be(true)
expect(ui_web_request_body_framing_valid("Transfer-Encoding: chunked\n")).to_be(false)
```

</details>

#### bounds request heads before shared wm route dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_request_head_allowed(UI_WEB_MAX_REQUEST_HEAD_BYTES)).to_be(true)
expect(ui_web_request_head_allowed(UI_WEB_MAX_REQUEST_HEAD_BYTES + 1)).to_be(false)
expect(ui_web_request_line_allowed(UI_WEB_MAX_REQUEST_LINE_BYTES)).to_be(true)
expect(ui_web_request_line_allowed(UI_WEB_MAX_REQUEST_LINE_BYTES + 1)).to_be(false)
expect(ui_web_header_line_allowed(UI_WEB_MAX_HEADER_LINE_BYTES)).to_be(true)
expect(ui_web_header_line_allowed(UI_WEB_MAX_HEADER_LINE_BYTES + 1)).to_be(false)
expect(ui_web_request_head_status("GET / HTTP/1.1", "Host: localhost\n")).to_equal("ok")
val oversized_request_path = "x".repeat(UI_WEB_MAX_REQUEST_LINE_BYTES + 1)
val oversized_header_value = "x".repeat(UI_WEB_MAX_HEADER_LINE_BYTES + 1)
val oversized_head_value = "x".repeat(UI_WEB_MAX_REQUEST_HEAD_BYTES + 1)
expect(ui_web_request_head_status("GET /{oversized_request_path} HTTP/1.1", "Host: localhost\n")).to_equal("request_head_too_large")
expect(ui_web_request_head_status("GET / HTTP/1.1", "X-Pad: {oversized_header_value}\n")).to_equal("request_head_too_large")
expect(ui_web_request_head_status("GET / HTTP/1.1", "X-Pad: {oversized_head_value}\n")).to_equal("request_head_too_large")
```

</details>

#### bounds login attempts with a fixed burst window

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = ui_web_login_rate_decision(0u64, 0, 1000u64)
expect(first.0).to_be(true)
expect(first.1).to_equal(1000u64)
expect(first.2).to_equal(1)

val last_allowed = ui_web_login_rate_decision(1000u64, UI_WEB_LOGIN_RATE_MAX_ATTEMPTS - 1, 2000u64)
expect(last_allowed.0).to_be(true)
expect(last_allowed.2).to_equal(UI_WEB_LOGIN_RATE_MAX_ATTEMPTS)

val limited = ui_web_login_rate_decision(1000u64, UI_WEB_LOGIN_RATE_MAX_ATTEMPTS, 3000u64)
expect(limited.0).to_be(false)
expect(limited.1).to_equal(1000u64)
expect(limited.2).to_equal(UI_WEB_LOGIN_RATE_MAX_ATTEMPTS)

val reset = ui_web_login_rate_decision(1000u64, UI_WEB_LOGIN_RATE_MAX_ATTEMPTS, 1000u64 + UI_WEB_LOGIN_RATE_WINDOW_MS)
expect(reset.0).to_be(true)
expect(reset.2).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/nfr/simple_web_browser_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
- **Design:** `doc/05_design/ui/web/simple_web_browser_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_production_hardening.md`


</details>
