# csrf_spec

> Tests for CSRF token generation, constant-time token comparison, config defaults, method exemptions, and the fail-closed empty-secret guard in csrf_handler.  Rewrites the phantom spec that called non-existent symbols (validate_csrf_token / is_csrf_exempt_method / default_csrf_config / zero-arg generate_csrf_token) against the real API in src/lib/nogc_async_mut/http_server/csrf.spl.

<!-- sdn-diagram:id=csrf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=csrf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

csrf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=csrf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# csrf_spec

Tests for CSRF token generation, constant-time token comparison, config defaults, method exemptions, and the fail-closed empty-secret guard in csrf_handler.  Rewrites the phantom spec that called non-existent symbols (validate_csrf_token / is_csrf_exempt_method / default_csrf_config / zero-arg generate_csrf_token) against the real API in src/lib/nogc_async_mut/http_server/csrf.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-011 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/csrf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for CSRF token generation, constant-time token comparison, config
defaults, method exemptions, and the fail-closed empty-secret guard in
csrf_handler.  Rewrites the phantom spec that called non-existent symbols
(validate_csrf_token / is_csrf_exempt_method / default_csrf_config / zero-arg
generate_csrf_token) against the real API in
src/lib/nogc_async_mut/http_server/csrf.spl.

## Scenarios

### CSRF token generation

#### returns empty string when secret_key is empty (fail-closed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val token = generate_csrf_token(config, "session-abc")
expect(token).to_equal("")
```

</details>

#### generate_csrf_token_with_timestamp returns empty when secret_key is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val token = generate_csrf_token_with_timestamp(config, "session-abc", 1000000)
expect(token).to_equal("")
```

</details>

### CSRF token constant-time comparison

#### identical strings compare equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "abc123def456ghi789jkl012mno345pq"
val result = constant_time_eq(token, token)
expect(result).to_equal(true)
```

</details>

#### mismatched tokens compare unequal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token_a = "abc123def456ghi789jkl012mno345pq"
val token_b = "zzz999yyy888xxx777www666vvv555uu"
val result = constant_time_eq(token_a, token_b)
expect(result).to_equal(false)
```

</details>

#### empty string does not equal a non-empty token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "abc123def456ghi789jkl012mno345pq"
val result = constant_time_eq("", token)
expect(result).to_equal(false)
```

</details>

#### both empty strings compare equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = constant_time_eq("", "")
expect(result).to_equal(true)
```

</details>

### CsrfConfig defaults

#### default config has empty secret_key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
expect(config.secret_key).to_equal("")
```

</details>

#### default config uses X-CSRF-Token header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
expect(config.token_header).to_equal("X-CSRF-Token")
```

</details>

#### default config uses csrf_token cookie

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
expect(config.cookie_name).to_equal("csrf_token")
```

</details>

#### default exempt_methods includes GET

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val has_get = config.exempt_methods.contains("GET")
expect(has_get).to_equal(true)
```

</details>

#### default exempt_methods includes HEAD

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val has_head = config.exempt_methods.contains("HEAD")
expect(has_head).to_equal(true)
```

</details>

#### default exempt_methods includes OPTIONS

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val has_options = config.exempt_methods.contains("OPTIONS")
expect(has_options).to_equal(true)
```

</details>

#### default exempt_methods does not include POST

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val has_post = config.exempt_methods.contains("POST")
expect(has_post).to_equal(false)
```

</details>

#### default exempt_methods does not include DELETE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val has_delete = config.exempt_methods.contains("DELETE")
expect(has_delete).to_equal(false)
```

</details>

### csrf_handler exempt methods pass through

#### GET request continues without CSRF check

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = _test_config()
val server_config = _test_server_config()
val request = _test_request("GET", "/", [])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Continue:
        expect(true).to_equal(true)
    _:
        expect(false).to_equal(true)
```

</details>

#### HEAD request continues without CSRF check

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = _test_config()
val server_config = _test_server_config()
val request = _test_request("HEAD", "/", [])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Continue:
        expect(true).to_equal(true)
    _:
        expect(false).to_equal(true)
```

</details>

#### OPTIONS request continues without CSRF check

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = _test_config()
val server_config = _test_server_config()
val request = _test_request("OPTIONS", "/", [])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Continue:
        expect(true).to_equal(true)
    _:
        expect(false).to_equal(true)
```

</details>

### csrf_handler fail-closed on empty secret

#### POST with empty secret_key returns Error(403)

- [
- PhaseResult Error
   - Expected: status equals `403`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val server_config = _test_server_config()
val request = _test_request("POST", "/api/data",
    [("X-CSRF-Token", "sometoken"), ("Cookie", "csrf_token=sometoken")])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Error(status, _):
        expect(status).to_equal(403)
    _:
        expect(false).to_equal(true)
```

</details>

#### PUT with empty secret_key returns Error(403)

- [
- PhaseResult Error
   - Expected: status equals `403`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = CsrfConfig.default()
val server_config = _test_server_config()
val request = _test_request("PUT", "/api/data",
    [("X-CSRF-Token", "sometoken"), ("Cookie", "csrf_token=sometoken")])
val result = csrf_handler(request, server_config, config)
match result:
    PhaseResult.Error(status, _):
        expect(status).to_equal(403)
    _:
        expect(false).to_equal(true)
```

</details>

### CSRF header and cookie helpers

#### get_header_value finds a header case-insensitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = [("X-CSRF-Token", "mytoken123")]
val result = get_header_value(headers, "x-csrf-token")
expect(result).to_equal("mytoken123")
```

</details>

#### get_header_value returns empty when header not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = [("Content-Type", "text/html")]
val result = get_header_value(headers, "X-CSRF-Token")
expect(result).to_equal("")
```

</details>

#### get_cookie_value extracts named cookie

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = [("Cookie", "session=abc; csrf_token=tok456")]
val result = get_cookie_value(headers, "csrf_token")
expect(result).to_equal("tok456")
```

</details>

#### get_cookie_value returns empty when cookie not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = [("Cookie", "session=abc")]
val result = get_cookie_value(headers, "csrf_token")
expect(result).to_equal("")
```

</details>

#### get_cookie_value returns empty when no Cookie header present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = [("Content-Type", "application/json")]
val result = get_cookie_value(headers, "csrf_token")
expect(result).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
