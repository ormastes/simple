# Adapter Outlook Curl Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Outlook Curl Specification

## Scenarios

### outlook curl client

#### carries token and mailbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(c.access_token).to_equal("tk_abc")
expect(c.mailbox_upn).to_equal("ops@acme.com")
```

</details>

#### defaults to the v1.0 Graph base and curl binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _mk_client()
expect(c.base_url).to_equal("https://graph.microsoft.com/v1.0")
expect(c.curl_path).to_equal("curl")
```

</details>

### outlook token cache

#### is fresh only when expiry clears the safety margin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(outlook_curl_token_cache_is_fresh(1000, 900)).to_equal(true)
expect(outlook_curl_token_cache_is_fresh(1000, 950)).to_equal(false)
```

</details>

#### treats the exact margin boundary as not fresh

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(outlook_curl_token_cache_is_fresh(1000, 940)).to_equal(false)
```

</details>

#### renders and parses a token cache roundtrip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rendered = outlook_curl_render_token_cache("tok_xyz", 1700000000)
val (tok, exp) = outlook_curl_parse_token_cache(rendered)
expect(tok).to_equal("tok_xyz")
expect(exp).to_equal(1700000000)
```

</details>

#### parses an empty cache to empty token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (tok, exp) = outlook_curl_parse_token_cache("")
expect(tok).to_equal("")
expect(exp).to_equal(0)
```

</details>

### outlook argv builders

#### token POST uses POST verb and form content type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _build_curl_argv_token("https://login/token", "grant_type=client_credentials")
expect(_list_contains(args, "-X")).to_equal(true)
expect(_list_contains(args, "POST")).to_equal(true)
expect(_list_contains(args, "Content-Type: application/x-www-form-urlencoded")).to_equal(true)
expect(_list_contains(args, "grant_type=client_credentials")).to_equal(true)
expect(_list_contains(args, "https://login/token")).to_equal(true)
```

</details>

#### Graph GET carries a Bearer authorization header and url

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = _build_curl_argv_get("tok_abc", "https://graph/x")
expect(_list_contains(args, "Authorization: Bearer tok_abc")).to_equal(true)
expect(_list_contains(args, "https://graph/x")).to_equal(true)
```

</details>

### outlook status mapping

#### treats 2xx as ok and others as not ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_ok(200)).to_equal(true)
expect(_status_ok(299)).to_equal(true)
expect(_status_ok(300)).to_equal(false)
expect(_status_ok(401)).to_equal(false)
```

</details>

#### maps auth, not-found, rate-limit, server, and transport errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_status_message(401, "")).to_equal("authentication required (HTTP 401)")
expect(_status_message(403, "")).to_equal("authentication required (HTTP 403)")
expect(_status_message(404, "")).to_equal("not found (HTTP 404)")
expect(_status_message(429, "")).to_equal("rate limited (HTTP 429)")
expect(_status_message(500, "boom")).to_equal("server error (HTTP 500): boom")
expect(_status_message(0, "no route")).to_equal("transport error: no route")
```

</details>

#### parses a numeric status tail and rejects non-numeric

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_status("200")).to_equal(200)
expect(_parse_status("  404 ")).to_equal(404)
expect(_parse_status("abc")).to_equal(0)
```

</details>

#### splits curl body from the trailing status line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (body, code) = _split_response("hello world\n200")
expect(body).to_equal("hello world")
expect(code).to_equal(200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/adapter_outlook_curl_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- outlook curl client
- outlook token cache
- outlook argv builders
- outlook status mapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
