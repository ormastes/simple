# PhaseResult Response Headers Specification

> src/lib/nogc_async_mut/http_server/cors.spl,

<!-- sdn-diagram:id=phase_result_headers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=phase_result_headers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

phase_result_headers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=phase_result_headers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PhaseResult Response Headers Specification

src/lib/nogc_async_mut/http_server/cors.spl,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #E7-phase-result-headers |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/phase_result_headers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

src/lib/nogc_async_mut/http_server/cors.spl,
               src/lib/nogc_async_mut/http_server/response.spl

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `types.spl` | Artifact | `src/lib/nogc_async_mut/http_server/types.spl` |

## Scenarios

### PhaseResult.Respond 4-arg constructor shape

#### constructs Respond with empty headers list

- PhaseResult Respond
   - Expected: s equals `200`
   - Expected: reason equals `OK`
   - Expected: hdrs.len() equals `0`
   - Expected: body equals `hello`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = PhaseResult.Respond(200, "OK", [], "hello")
match r:
    PhaseResult.Respond(s, reason, hdrs, body):
        expect(s).to_equal(200)
        expect(reason).to_equal("OK")
        expect(hdrs.len()).to_equal(0)
        expect(body).to_equal("hello")
    _:
        expect(false).to_equal(true)
```

</details>

#### constructs Respond with a non-empty headers list

-
-
- PhaseResult Respond
   - Expected: s equals `204`
   - Expected: h.len() equals `2`
   - Expected: h[0].0 equals `X-Custom`
   - Expected: h[0].1 equals `value1`
   - Expected: h[1].0 equals `Cache-Control`
   - Expected: h[1].1 equals `no-store`
   - Expected: body equals ``
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdrs: [(text, text)] = [
    ("X-Custom", "value1"),
    ("Cache-Control", "no-store")
]
val r = PhaseResult.Respond(204, "No Content", hdrs, "")
match r:
    PhaseResult.Respond(s, reason, h, body):
        expect(s).to_equal(204)
        expect(h.len()).to_equal(2)
        expect(h[0].0).to_equal("X-Custom")
        expect(h[0].1).to_equal("value1")
        expect(h[1].0).to_equal("Cache-Control")
        expect(h[1].1).to_equal("no-store")
        expect(body).to_equal("")
    _:
        expect(false).to_equal(true)
```

</details>

### build_cors_headers returns header pairs not a string

#### returns Access-Control-Allow-Origin for non-wildcard origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = _make_cors_config()
val pairs = build_cors_headers("https://example.com", config)
expect(pairs.len() > 0).to_equal(true)
val first = pairs[0]
expect(first.0).to_equal("Access-Control-Allow-Origin")
expect(first.1).to_equal("https://example.com")
```

</details>

#### includes Vary: Origin for non-wildcard origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = _make_cors_config()
val pairs = build_cors_headers("https://example.com", config)
var found_vary = false
for p in pairs:
    if p.0 == "Vary" and p.1 == "Origin":
        found_vary = true
expect(found_vary).to_equal(true)
```

</details>

#### does not include Vary: Origin for wildcard origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = _make_cors_config()
val pairs = build_cors_headers("*", config)
var found_vary = false
for p in pairs:
    if p.0 == "Vary":
        found_vary = true
expect(found_vary).to_equal(false)
```

</details>

#### includes expose headers when configured

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = _make_cors_config()
val pairs = build_cors_headers("https://example.com", config)
var found_expose = false
for p in pairs:
    if p.0 == "Access-Control-Expose-Headers":
        found_expose = true
expect(found_expose).to_equal(true)
```

</details>

### cors_handler places CORS headers in Respond headers slot

#### normal CORS GET: ACAO header in headers slot, body is empty

- PhaseResult Respond
   - Expected: body equals ``
   - Expected: h.1 equals `https://example.com`
   - Expected: found_acao is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = _make_request("GET", "https://example.com")
val srv = _make_server_config()
val config = _make_cors_config()
val result = cors_handler(req, srv, config)
match result:
    PhaseResult.Respond(status, reason, hdrs, body):
        # Body must be empty — headers belong in the headers slot
        expect(body).to_equal("")
        # At least one header: Access-Control-Allow-Origin
        var found_acao = false
        for h in hdrs:
            if h.0 == "Access-Control-Allow-Origin":
                found_acao = true
                expect(h.1).to_equal("https://example.com")
        expect(found_acao).to_equal(true)
    _:
        expect(false).to_equal(true)
```

</details>

### handle_preflight places CORS headers in Respond headers slot

#### preflight: 204 status with empty body

- PhaseResult Respond
   - Expected: status equals `204`
   - Expected: body equals ``
   - Expected: hlen > 0 is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = _make_request("OPTIONS", "https://example.com")
val srv = _make_server_config()
val config = _make_cors_config()
val result = cors_handler(req, srv, config)
match result:
    PhaseResult.Respond(status, reason, hdrs, body):
        expect(status).to_equal(204)
        expect(body).to_equal("")
        val hlen = hdrs.len()
        expect(hlen > 0).to_equal(true)
    _:
        expect(false).to_equal(true)
```

</details>

#### preflight: ACAO header in headers list

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = _make_request("OPTIONS", "https://example.com")
val config = _make_cors_config()
val hdrs = _preflight_headers(config, "https://example.com")
var found = false
for h in hdrs:
    if h.0 == "Access-Control-Allow-Origin":
        found = true
        expect(h.1).to_equal("https://example.com")
expect(found).to_equal(true)
```

</details>

#### preflight: Vary: Origin present for non-wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = _make_cors_config()
val hdrs = _preflight_headers(config, "https://example.com")
var found_vary = false
for h in hdrs:
    if h.0 == "Vary" and h.1 == "Origin":
        found_vary = true
expect(found_vary).to_equal(true)
```

</details>

#### preflight: body does not contain raw header text

- PhaseResult Respond
   - Expected: body_has_acao is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = _make_request("OPTIONS", "https://example.com")
val srv = _make_server_config()
val config = _make_cors_config()
val result = cors_handler(req, srv, config)
match result:
    PhaseResult.Respond(status, reason, hdrs, body):
        # Body must not contain "Access-Control" — that goes in headers
        val body_has_acao = body.contains("Access-Control")
        expect(body_has_acao).to_equal(false)
    _:
        expect(false).to_equal(true)
```

</details>

### build_phase_response serializes extra headers into wire format

#### extra headers appear in serialized response

-
-
   - Expected: has_acao is true
   - Expected: has_vary is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdrs: [(text, text)] = [
    ("Access-Control-Allow-Origin", "https://example.com"),
    ("Vary", "Origin")
]
val resp = build_phase_response(200, "OK", hdrs, "")
val wire = serialize_response(resp)
val has_acao = wire.contains("Access-Control-Allow-Origin: https://example.com")
val has_vary = wire.contains("Vary: Origin")
expect(has_acao).to_equal(true)
expect(has_vary).to_equal(true)
```

</details>

#### status line is correct in serialized response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = build_phase_response(204, "No Content", [], "")
val wire = serialize_response(resp)
val has_status = wire.contains("HTTP/1.1 204 No Content")
expect(has_status).to_equal(true)
```

</details>

#### CRLF injection in header value is dropped

-
-
   - Expected: has_safe is true
   - Expected: has_evil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdrs: [(text, text)] = [
    ("X-Safe", "good"),
    ("X-Injected", "bad\r\nX-Evil: injected")
]
val resp = build_phase_response(200, "OK", hdrs, "")
val wire = serialize_response(resp)
val has_safe = wire.contains("X-Safe: good")
val has_evil = wire.contains("X-Evil")
expect(has_safe).to_equal(true)
expect(has_evil).to_equal(false)
```

</details>

#### CRLF injection in header name is dropped

-
-
   - Expected: has_safe is true
   - Expected: has_evil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdrs: [(text, text)] = [
    ("X-Safe", "good"),
    ("X-Bad\r\nX-Evil", "injected")
]
val resp = build_phase_response(200, "OK", hdrs, "")
val wire = serialize_response(resp)
val has_safe = wire.contains("X-Safe: good")
val has_evil = wire.contains("X-Evil")
expect(has_safe).to_equal(true)
expect(has_evil).to_equal(false)
```

</details>

#### LF-only injection in header value is dropped

-
-
   - Expected: has_safe is true
   - Expected: has_lf is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdrs: [(text, text)] = [
    ("X-Safe", "good"),
    ("X-Lf", "bad\nvalue")
]
val resp = build_phase_response(200, "OK", hdrs, "")
val wire = serialize_response(resp)
val has_safe = wire.contains("X-Safe: good")
val has_lf = wire.contains("X-Lf")
expect(has_safe).to_equal(true)
expect(has_lf).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
