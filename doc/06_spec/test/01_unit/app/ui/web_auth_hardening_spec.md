# Simple Web Browser Production Auth Hardening Specification

> Verifies selected Feature C and NFR C production authentication, origin, request-boundary, generated-client, and login burst behavior.

<!-- sdn-diagram:id=web_auth_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_auth_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_auth_hardening_spec -> std
web_auth_hardening_spec -> app
web_auth_hardening_spec -> common
web_auth_hardening_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_auth_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

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
| Plan | doc/03_plan/agent_tasks/simple_browser_production_level.md |
| Design | doc/05_design/simple_web_browser_production_hardening.md |
| Research | doc/01_research/local/simple_browser_production_level.md |
| Source | `test/01_unit/app/ui/web_auth_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected Feature C and NFR C production authentication, origin,
request-boundary, generated-client, and login burst behavior.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Research:** doc/01_research/local/simple_browser_production_level.md
**Plan:** doc/03_plan/agent_tasks/simple_browser_production_level.md
**Design:** doc/05_design/simple_web_browser_production_hardening.md
**Traceability:** REQ-WEB-HARD-001, REQ-WEB-HARD-002, REQ-WEB-HARD-003, REQ-WEB-HARD-004, REQ-WEB-HARD-005, REQ-WEB-HARD-008, REQ-WEB-HARD-011, NFR-WEB-HARD-001, NFR-WEB-HARD-002, NFR-WEB-HARD-003, NFR-WEB-HARD-004, NFR-WEB-HARD-005, NFR-WEB-HARD-010, NFR-WEB-HARD-011

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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://localhost"])
val missing = guard.check("Host: localhost\n")
val duplicate = guard.check("Host: localhost\nOrigin: https://localhost\nOrigin: https://evil.example\n")
val disallowed = guard.check("Origin: https://evil.example\n")
val allowed = guard.check("Origin: https://localhost\n")
expect(missing.is_err()).to_be(true)
expect(duplicate.is_err()).to_be(true)
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

#### requires explicit opt-in before using local default origins

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_allow_local_default_origins_flag("")).to_be(false)
expect(_allow_local_default_origins_flag("0")).to_be(false)
expect(_allow_local_default_origins_flag("false")).to_be(false)
expect(_allow_local_default_origins_flag("1")).to_be(true)
val production_guard = OriginGuard.from_env_value_with_policy("", false)
val local_dev_guard = OriginGuard.from_env_value_with_policy("", true)
expect(production_guard.check("Origin: http://localhost:8080\n").is_err()).to_be(true)
expect(local_dev_guard.check("Origin: http://localhost:8080\n").is_ok()).to_be(true)
```

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
expect(ui_web_authorization_status("Host: localhost\nOrigin: https://localhost\n", "/api/state", guard, secret, now)).to_equal("missing_bearer")
expect(ui_web_authorization_status("Host: localhost\nOrigin: https://localhost\n", "/api/widgets", guard, secret, now)).to_equal("missing_bearer")
expect(ui_web_authorization_status("Host: localhost\nOrigin: https://localhost\n", "/api/clients", guard, secret, now)).to_equal("missing_bearer")
expect(ui_web_authorization_status("Host: localhost\nOrigin: https://evil.example\nAuthorization: Bearer malformed\n", "/api/state", guard, secret, now)).to_equal("forbidden_origin")
expect(ui_web_authorization_status("Host: localhost\nOrigin: https://localhost\nAuthorization: Bearer malformed\n", "/api/state", guard, secret, now)).to_equal("invalid_bearer")
expect(ui_web_request_authorized("Host: localhost\nOrigin: https://localhost\nAuthorization: Bearer malformed\n", "/api/state", guard, secret, now)).to_be(false)
```

</details>

#### requires exactly one valid host header before sensitive authorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://localhost"])
val secret = "unit-test-secret"
val now = 1000u64
expect(ui_web_host_value_allowed("localhost")).to_be(true)
expect(ui_web_host_value_allowed("127.0.0.1:8080")).to_be(true)
expect(ui_web_host_value_allowed("[::1]:8080")).to_be(true)
expect(ui_web_host_value_allowed("http://localhost")).to_be(false)
expect(ui_web_host_value_allowed("localhost/path")).to_be(false)
expect(ui_web_host_value_allowed("user@localhost")).to_be(false)
expect(ui_web_host_header_status("Host: localhost\n")).to_equal("ok")
expect(ui_web_host_header_status("Origin: https://localhost\n")).to_equal("missing_host")
expect(ui_web_host_header_status("Host: localhost\nHost: other\n")).to_equal("duplicate_host")
expect(ui_web_host_header_status("Host: http://localhost\n")).to_equal("invalid_host")
expect(ui_web_host_header_allowed("Host: localhost\n")).to_be(true)
expect(ui_web_authorization_status("Origin: https://localhost\nAuthorization: Bearer malformed\n", "/api/state", guard, secret, now)).to_equal("bad_host")
```

</details>

#### requires host and origin authorities to match before token use

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://localhost", "https://127.0.0.1:8443"])
val secret = "unit-test-secret"
val now = 1000u64
expect(ui_web_host_header_value("Host: LOCALHOST\n")).to_equal("localhost")
expect(ui_web_origin_authority("https://127.0.0.1:8443")).to_equal("127.0.0.1:8443")
expect(ui_web_origin_authority("https://localhost/path")).to_equal("")
expect(ui_web_host_origin_authority_status("Host: localhost\n", "https://localhost")).to_equal("ok")
expect(ui_web_host_origin_authority_status("Host: 127.0.0.1:8443\n", "https://127.0.0.1:8443")).to_equal("ok")
expect(ui_web_host_origin_authority_status("Host: 127.0.0.1:8443\n", "https://localhost")).to_equal("origin_host_mismatch")
expect(ui_web_host_origin_authority_allowed("Host: localhost\n", "https://localhost")).to_be(true)
expect(ui_web_authorization_status("Host: 127.0.0.1:8443\nOrigin: https://localhost\nAuthorization: Bearer malformed\n", "/api/state", guard, secret, now)).to_equal("origin_host_mismatch")
```

</details>

#### requires origin-bound bearer tokens for websocket and resume routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://localhost"])
val secret = "unit-test-secret"
val token = SessionToken.issue("legacy", "https://localhost", 3600000u64, secret).serialize()
val unauthorized_token = SessionToken.issue("admin", "https://localhost", 3600000u64, secret).serialize()
val headers = "Host: localhost\nOrigin: https://localhost\nAuthorization: Bearer {token}\n"
val ws_headers = "Host: localhost\nOrigin: https://localhost\nSec-WebSocket-Protocol: simple-ui, bearer.{token}\n"
val unauthorized_headers = "Host: localhost\nOrigin: https://localhost\nAuthorization: Bearer {unauthorized_token}\n"

expect(ui_web_authorization_status("Host: localhost\nOrigin: https://localhost\n", "/ui/resume", guard, secret, 1000u64)).to_equal("missing_bearer")
expect(ui_web_authorization_status("Host: localhost\nOrigin: https://evil.example\nAuthorization: Bearer {token}\n", "/ui/resume", guard, secret, 1000u64)).to_equal("forbidden_origin")
expect(ui_web_authorization_status("Host: localhost\nOrigin: https://localhost\nAuthorization: Bearer malformed\n", "/ui/resume", guard, secret, 1000u64)).to_equal("invalid_bearer")
expect(ui_web_authorization_status(unauthorized_headers, "/ui/resume", guard, secret, 1000u64)).to_equal("unauthorized_grant")
expect(ui_web_authorization_status(headers, "/ui/resume", guard, secret, 1000u64)).to_equal("ok")
expect(ui_web_authorization_status(ws_headers, "/ui/ws", guard, secret, 1000u64)).to_equal("ok")
```

</details>

#### caps issued token ttl at the production maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bounded_token_ttl_ms(1000u64)).to_equal(1000u64)
expect(_bounded_token_ttl_ms(TOKEN_TTL_MAX_MS + 1u64)).to_equal(TOKEN_TTL_MAX_MS)
val before = rt_time_ms()
val token = SessionToken.issue("legacy", "https://localhost", TOKEN_TTL_MAX_MS + 3600000u64, "unit-test-secret")
val max_expected = before + TOKEN_TTL_MAX_MS + 1000u64
expect(token.expires_at_ms > before).to_be(true)
expect(token.expires_at_ms <= max_expected).to_be(true)
```

</details>

#### rejects malformed, expired, and wrong-origin serialized tokens before authorization succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token_id = "a".repeat(64)
val signature = "b".repeat(64)
val expired = SessionToken(token_id: token_id, grant_id: "grant", origin: "https://localhost", expires_at_ms: 100u64, signature: signature).serialize()
val wrong_origin = SessionToken(token_id: token_id, grant_id: "grant", origin: "https://localhost", expires_at_ms: 5000u64, signature: signature).serialize()
val unsafe_grant = SessionToken(token_id: token_id, grant_id: "grant:admin", origin: "https://localhost", expires_at_ms: 5000u64, signature: signature).serialize()
val short_token_id = SessionToken(token_id: "tok", grant_id: "grant", origin: "https://localhost", expires_at_ms: 5000u64, signature: signature).serialize()
val bad_signature = SessionToken(token_id: token_id, grant_id: "grant", origin: "https://localhost", expires_at_ms: 5000u64, signature: "not-hex").serialize()

expect(SessionToken.parse("not-a-complete-token").is_err()).to_be(true)
expect(SessionToken.parse(short_token_id).is_err()).to_be(true)
expect(SessionToken.parse(bad_signature).is_err()).to_be(true)
expect(SessionToken.parse(unsafe_grant).is_err()).to_be(true)
expect(verify(expired, "https://localhost", "unit-test-secret", 101u64).is_err()).to_be(true)
expect(verify(wrong_origin, "https://other.example", "unit-test-secret", 1000u64).is_err()).to_be(true)
```

</details>

#### generates token-authenticated websocket clients for browser and wm paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy_js = generate_js(8080)
expect(legacy_js).to_contain("fetch('/ui/login'")
expect(legacy_js).to_contain("new WebSocket(browserWsUrl(), ['simple-ui', 'bearer.' + encodeURIComponent(authToken)])")
expect(legacy_js).to_contain("return wsProto + '://' + wsHost + '/ui/ws'")
expect(legacy_js.contains("legacyWsUrl")).to_be(false)
expect(legacy_js.contains("/ws?token=")).to_be(false)
expect(legacy_js.contains("'/ws'")).to_be(false)
val wm_js = generate_wm_js(8080)
expect(wm_js).to_contain("fetch('/ui/login'")
expect(wm_js).to_contain("new WebSocket(wsProto + '://' + wsHost + '/ui/ws', ['simple-ui', 'bearer.' + encodeURIComponent(authToken)])")
expect(wm_js.contains("/ui/ws?token=")).to_be(false)
val static_wm_js = rt_file_read_text("src/app/ui.web/wm.js")
expect(static_wm_js).to_contain("new WebSocket(url, ['simple-ui', 'bearer.' + encodeURIComponent(this.token)])")
expect(static_wm_js.contains("/ui/ws?token=")).to_be(false)
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

#### redacts sensitive auth material before diagnostic logging

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Host: localhost\nAuthorization: Bearer secret-token\nCookie: session=secret\nSec-WebSocket-Protocol: simple-ui, bearer.secret-token\nX-Request-Id: browser-1\n"
val safe_headers = ui_web_redact_sensitive_headers(headers)
expect(ui_web_redact_sensitive_header_line("Authorization: Bearer secret-token")).to_equal("Authorization: <redacted>")
expect(safe_headers).to_contain("Host: localhost")
expect(safe_headers).to_contain("Authorization: <redacted>")
expect(safe_headers).to_contain("Cookie: <redacted>")
expect(safe_headers).to_contain("Sec-WebSocket-Protocol: simple-ui, bearer.<redacted>")
expect(safe_headers.contains("secret-token")).to_be(false)
val safe_path = ui_web_redact_sensitive_path("/ui/ws?token=secret-token&mode=debug&access_token=other-secret")
expect(safe_path).to_equal("/ui/ws?token=<redacted>&mode=debug&access_token=<redacted>")
```

</details>

#### adds cache and sniffing guards to json responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ui_web_json_security_headers("application/json")
expect(headers).to_contain("Cache-Control: no-store")
expect(headers).to_contain("Pragma: no-cache")
expect(headers).to_contain("X-Content-Type-Options: nosniff")
expect(headers).to_contain("Cross-Origin-Resource-Policy: same-origin")
expect(ui_web_json_security_headers("text/html")).to_equal("")
```

</details>

#### adds cache and sniffing guards to browser script responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ui_web_script_security_headers("application/javascript")
expect(headers).to_contain("Cache-Control: no-store")
expect(headers).to_contain("Pragma: no-cache")
expect(headers).to_contain("X-Content-Type-Options: nosniff")
expect(headers).to_contain("Cross-Origin-Resource-Policy: same-origin")
expect(ui_web_script_security_headers("text/html")).to_equal("")
```

</details>

#### adds browser document security headers to html responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ui_web_html_security_headers("text/html")
expect(headers).to_contain("Cache-Control: no-store")
expect(headers).to_contain("Pragma: no-cache")
expect(headers).to_contain("Expires: 0")
expect(headers).to_contain("X-Content-Type-Options: nosniff")
expect(headers).to_contain("X-Frame-Options: DENY")
expect(headers).to_contain("X-DNS-Prefetch-Control: off")
expect(headers).to_contain("X-Permitted-Cross-Domain-Policies: none")
expect(headers).to_contain("Cross-Origin-Opener-Policy: same-origin")
expect(headers).to_contain("Cross-Origin-Embedder-Policy: require-corp")
expect(headers).to_contain("Cross-Origin-Resource-Policy: same-origin")
expect(headers).to_contain("Origin-Agent-Cluster: ?1")
expect(headers).to_contain("Referrer-Policy: no-referrer")
expect(headers).to_contain("Permissions-Policy: camera=(), microphone=(), geolocation=(), payment=()")
expect(headers).to_contain("usb=(), serial=(), bluetooth=()")
expect(headers).to_contain("clipboard-read=(), clipboard-write=()")
expect(headers).to_contain("display-capture=(), screen-wake-lock=(), xr-spatial-tracking=()")
expect(headers).to_contain("accelerometer=(), gyroscope=(), magnetometer=(), midi=()")
expect(headers).to_contain("autoplay=(), encrypted-media=(), fullscreen=()")
expect(headers).to_contain("Content-Security-Policy: default-src 'self'")
expect(headers).to_contain("object-src 'none'")
expect(headers).to_contain("frame-ancestors 'none'")
expect(ui_web_html_security_headers("application/json")).to_equal("")
```

</details>

#### adds strict transport security to tls responses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ui_web_tls_transport_security_headers()
expect(headers).to_contain("Strict-Transport-Security: max-age=31536000")
expect(headers).to_contain("includeSubDomains")
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

#### bounds capability grant ids before login token minting

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_capability_grant_id_status("legacy")).to_equal("ok")
expect(ui_web_capability_grant_id_status("wm_default-01")).to_equal("ok")
expect(ui_web_capability_grant_id_allowed("dev")).to_be(true)
expect(ui_web_capability_grant_id_status("")).to_equal("missing_capability_grant")
expect(ui_web_capability_grant_id_status("grant.with.dot")).to_equal("invalid_capability_grant")
expect(ui_web_capability_grant_id_status("grant:admin")).to_equal("invalid_capability_grant")
expect(ui_web_capability_grant_id_status("x".repeat(UI_WEB_MAX_CAPABILITY_GRANT_ID_BYTES + 1))).to_equal("capability_grant_too_large")
```

</details>

#### authorizes login grants from a server owned allowlist

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_capability_grant_id_authorized_from_value("legacy", "")).to_be(true)
expect(ui_web_capability_grant_id_authorized_from_value("wm", "")).to_be(true)
expect(ui_web_capability_grant_id_authorized_from_value("dev", "")).to_be(true)
expect(ui_web_capability_grant_id_authorized_from_value("wm-default", "")).to_be(true)
expect(ui_web_capability_grant_id_authorized_from_value("admin", "")).to_be(false)
expect(ui_web_capability_grant_id_authorized_from_value("ops", "legacy, ops")).to_be(true)
expect(ui_web_capability_grant_id_authorized_from_value("dev", "legacy, ops")).to_be(false)
expect(ui_web_capability_grant_id_authorized_from_value("grant:admin", "grant:admin")).to_be(false)
```

</details>

#### rejects malformed resume bodies after authorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = "{\"session_id\":\"session-1\",\"snapshot_revision\":42,\"last_sequence\":7}"
val missing_session = "{\"snapshot_revision\":42,\"last_sequence\":7}"
val invalid_session = "{\"session_id\":\"session/../1\",\"snapshot_revision\":42,\"last_sequence\":7}"
val too_long_session_id = "s".repeat(UI_WEB_MAX_SESSION_ID_BYTES + 1)
val oversized_session = "{\"session_id\":\"{too_long_session_id}\",\"snapshot_revision\":42,\"last_sequence\":7}"
val invalid_revision = "{\"session_id\":\"session-1\",\"snapshot_revision\":\"4x\",\"last_sequence\":7}"
val invalid_sequence = "{\"session_id\":\"session-1\",\"snapshot_revision\":42,\"last_sequence\":\"7x\"}"
val oversized = "x".repeat(UI_WEB_MAX_AUTH_JSON_BYTES + 1)
expect(ui_web_resume_body_status(valid)).to_equal("ok")
expect(ui_web_resume_body_status(oversized)).to_equal("body_too_large")
expect(ui_web_resume_body_status(missing_session)).to_equal("missing_session_id")
expect(ui_web_resume_body_status(invalid_session)).to_equal("invalid_session_id")
expect(ui_web_resume_body_status(oversized_session)).to_equal("session_id_too_large")
expect(ui_web_resume_body_status(invalid_revision)).to_equal("invalid_snapshot_revision")
expect(ui_web_resume_body_status(invalid_sequence)).to_equal("invalid_last_sequence")
```

</details>

#### bounds resume session identifiers before replay handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_session_id_status("session-1")).to_equal("ok")
expect(ui_web_session_id_status("abc_DEF-012")).to_equal("ok")
expect(ui_web_session_id_allowed("abc_DEF-012")).to_be(true)
expect(ui_web_session_id_status("")).to_equal("missing_session_id")
expect(ui_web_session_id_status("session/1")).to_equal("invalid_session_id")
expect(ui_web_session_id_status("Bearer token")).to_equal("invalid_session_id")
expect(ui_web_session_id_status("s".repeat(UI_WEB_MAX_SESSION_ID_BYTES + 1))).to_equal("session_id_too_large")
```

</details>

#### returns a snapshot wire frame when a resume request has a stale revision

- var session = UISession new
- session set active backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = build_tree_with_title(label("resume_label", "Resume Ready"), "Resume App", "dark")
var session = UISession.new(tree)
session.set_active_backend("web")
val body = "{\"session_id\":\"session-1\",\"snapshot_revision\":999,\"last_sequence\":0}"
val response = ui_web_resume_response_body(body, session, "grant")
expect(response).to_contain("\"t\": \"snapshot\"")
expect(response).to_contain("\"s\": \"session-1\"")
expect(response).to_contain("\"snapshot_json\"")
expect(response.contains("\"snapshot_revision\": 999")).to_be(false)
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

#### requires json content type for auth body routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_json_content_type_status("Content-Type: application/json\n")).to_equal("ok")
expect(ui_web_json_content_type_status("Content-Type: application/json; charset=utf-8\n")).to_equal("ok")
expect(ui_web_json_content_type_status("Host: localhost\n")).to_equal("missing_content_type")
expect(ui_web_json_content_type_status("Content-Type: text/plain\n")).to_equal("unsupported_content_type")
expect(ui_web_json_content_type_status("Content-Type: application/json\nContent-Type: application/json\n")).to_equal("duplicate_content_type")
expect(ui_web_json_content_type_allowed("Content-Type: application/json\n")).to_be(true)
```

</details>

#### rejects explicit cross-site fetch metadata for auth body routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_fetch_site_status("Host: localhost\n")).to_equal("ok")
expect(ui_web_fetch_site_status("Sec-Fetch-Site: same-origin\n")).to_equal("ok")
expect(ui_web_fetch_site_status("Sec-Fetch-Site: same-site\n")).to_equal("ok")
expect(ui_web_fetch_site_status("Sec-Fetch-Site: cross-site\n")).to_equal("cross_site_request")
expect(ui_web_fetch_site_status("Sec-Fetch-Site: none\n")).to_equal("invalid_fetch_site")
expect(ui_web_fetch_site_status("Sec-Fetch-Site: same-origin\nSec-Fetch-Site: same-origin\n")).to_equal("duplicate_fetch_site")
expect(ui_web_fetch_site_allowed("Sec-Fetch-Site: same-origin\n")).to_be(true)
expect(ui_web_fetch_site_allowed("Sec-Fetch-Site: cross-site\n")).to_be(false)
```

</details>

#### fails closed on unsafe methods for auth sensitive routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_sensitive_route_method_status("/ui/login", "POST")).to_equal("ok")
expect(ui_web_sensitive_route_method_status("/ui/resume", "POST")).to_equal("ok")
expect(ui_web_sensitive_route_method_status("/ui/ws", "GET")).to_equal("ok")
expect(ui_web_sensitive_route_method_status("/api/state", "GET")).to_equal("ok")
expect(ui_web_sensitive_route_method_status("/api/widgets", "GET")).to_equal("ok")
expect(ui_web_sensitive_route_method_status("/api/clients", "GET")).to_equal("ok")
expect(ui_web_sensitive_route_method_status("/ui/login", "GET")).to_equal("method_not_allowed")
expect(ui_web_sensitive_route_method_status("/ui/resume", "GET")).to_equal("method_not_allowed")
expect(ui_web_sensitive_route_method_status("/ui/ws", "POST")).to_equal("method_not_allowed")
expect(ui_web_sensitive_route_method_status("/api/state", "POST")).to_equal("method_not_allowed")
expect(ui_web_sensitive_route_method_status("/api/widgets?x=1", "POST")).to_equal("method_not_allowed")
expect(ui_web_sensitive_route_method_status("/assets/app.css", "POST")).to_equal("not_sensitive_route")
expect(ui_web_sensitive_route_method_allowed("/api/state", "POST")).to_be(false)
expect(ui_web_sensitive_route_method_allowed("/assets/app.css", "POST")).to_be(true)
```

</details>

<details>
<summary>Advanced: binds browser servers to loopback unless public bind is explicitly enabled</summary>

#### binds browser servers to loopback unless public bind is explicitly enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_allow_public_bind_from_env_value("")).to_be(false)
expect(ui_web_allow_public_bind_from_env_value("false")).to_be(false)
expect(ui_web_allow_public_bind_from_env_value("1")).to_be(true)
expect(ui_web_bind_host_from_env_value("", "")).to_equal("127.0.0.1")
expect(ui_web_bind_host_from_env_value("127.0.0.1", "")).to_equal("127.0.0.1")
expect(ui_web_bind_host_from_env_value("localhost", "")).to_equal("localhost")
expect(ui_web_bind_host_from_env_value("0.0.0.0", "")).to_equal("127.0.0.1")
expect(ui_web_bind_host_from_env_value("0.0.0.0", "1")).to_equal("0.0.0.0")
expect(ui_web_bind_host_from_env_value("http://0.0.0.0", "1")).to_equal("127.0.0.1")
```

</details>


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

#### bounds authenticated principal request bursts with a fixed window

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = ui_web_principal_rate_decision(0u64, 0, 1000u64)
expect(first.0).to_be(true)
expect(first.1).to_equal(1000u64)
expect(first.2).to_equal(1)

val last_allowed = ui_web_principal_rate_decision(1000u64, UI_WEB_PRINCIPAL_RATE_MAX_REQUESTS - 1, 2000u64)
expect(last_allowed.0).to_be(true)
expect(last_allowed.2).to_equal(UI_WEB_PRINCIPAL_RATE_MAX_REQUESTS)

val limited = ui_web_principal_rate_decision(1000u64, UI_WEB_PRINCIPAL_RATE_MAX_REQUESTS, 3000u64)
expect(limited.0).to_be(false)
expect(limited.1).to_equal(1000u64)
expect(limited.2).to_equal(UI_WEB_PRINCIPAL_RATE_MAX_REQUESTS)

val reset = ui_web_principal_rate_decision(1000u64, UI_WEB_PRINCIPAL_RATE_MAX_REQUESTS, 1000u64 + UI_WEB_PRINCIPAL_RATE_WINDOW_MS)
expect(reset.0).to_be(true)
expect(reset.2).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/simple_web_browser_production_hardening.md](doc/02_requirements/nfr/simple_web_browser_production_hardening.md)
- **Plan:** [doc/03_plan/agent_tasks/simple_browser_production_level.md](doc/03_plan/agent_tasks/simple_browser_production_level.md)
- **Design:** [doc/05_design/simple_web_browser_production_hardening.md](doc/05_design/simple_web_browser_production_hardening.md)
- **Research:** [doc/01_research/local/simple_browser_production_level.md](doc/01_research/local/simple_browser_production_level.md)


</details>
