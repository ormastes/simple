# Web Auth Hardening Specification

> <details>

<!-- sdn-diagram:id=web_auth_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_auth_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_auth_hardening_spec -> std
web_auth_hardening_spec -> app
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
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Auth Hardening Specification

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

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = OriginGuard(allowed: ["https://localhost"])
val secret = "unit-test-secret"
val now = 1000u64
expect(ui_web_authorization_status("Origin: https://localhost\n", "/api/state", guard, secret, now)).to_equal("missing_bearer")
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

#### generates token-authenticated websocket clients for legacy and wm browser paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy_js = generate_js(8080)
expect(legacy_js).to_contain("fetch('/ui/login'")
expect(legacy_js).to_contain("new WebSocket(legacyWsUrl(), ['simple-ui', 'bearer.' + encodeURIComponent(authToken)])")
expect(legacy_js.contains("/ws?token=")).to_be(false)
expect(legacy_js.contains("const wsUrl = wsProto + '://' + wsHost + '/ws';")).to_be(false)
val wm_js = generate_wm_js(8080)
expect(wm_js).to_contain("fetch('/ui/login'")
expect(wm_js).to_contain("new WebSocket(wsProto + '://' + wsHost + '/ui/ws', ['simple-ui', 'bearer.' + encodeURIComponent(authToken)])")
expect(wm_js.contains("/ui/ws?token=")).to_be(false)
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

#### fails oversized unauthenticated login bodies from content length alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Host: 127.0.0.1\nOrigin: http://localhost:8080\nContent-Length: 8193\n"
expect(ui_web_content_length(headers)).to_equal(8193)
expect(ui_web_body_exceeds_unauth_limit(headers)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/web_auth_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui.web production auth hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
