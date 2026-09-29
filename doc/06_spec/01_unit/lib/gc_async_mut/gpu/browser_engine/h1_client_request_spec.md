# H1 Client Request Specification

> Tests covering Browser HTTP/1 request serialization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# H1 Client Request Specification

## Scenarios

### Browser HTTP/1 request serialization

#### uses one absolute request deadline instead of refreshing per read

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses one absolute request deadline instead of refreshing per read
   - Expected: h1_deadline_remaining_ms(1000, 6000) equals `5000`
   - Expected: h1_deadline_remaining_ms(5999, 6000) equals `1`
   - Expected: h1_deadline_remaining_ms(6000, 6000) equals `0`
   - Expected: h1_deadline_remaining_ms(7000, 6000) equals `0`
   - Expected: h1_connect_address("::1", 443) equals `[::1]:443`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses one absolute request deadline instead of refreshing per read")
expect(h1_deadline_remaining_ms(1000, 6000)).to_equal(5000)
expect(h1_deadline_remaining_ms(5999, 6000)).to_equal(1)
expect(h1_deadline_remaining_ms(6000, 6000)).to_equal(0)
expect(h1_deadline_remaining_ms(7000, 6000)).to_equal(0)
expect(h1_connect_address("127.0.0.1", 80)).to_equal(
    "127.0.0.1:80"
)
expect(h1_connect_address("::1", 443)).to_equal("[::1]:443")
```

</details>

#### bounds response accumulation at the cache-sized transport ceiling

- bounds response accumulation at the cache-sized transport ceiling
   - Expected: browser_resource_size_allowed(50 * 1024 * 1024) is true
   - Expected: browser_resource_size_allowed(50 * 1024 * 1024 + 1) is false
   - Expected: browser_subresource_count_allowed(1024) is true
   - Expected: browser_subresource_count_allowed(1025) is false
   - Expected: h1_response_size_allowed(50 * 1024 * 1024 - 1, 1) is true
   - Expected: h1_response_size_allowed(50 * 1024 * 1024, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds response accumulation at the cache-sized transport ceiling")
expect(browser_resource_size_allowed(50 * 1024 * 1024)).to_equal(true)
expect(browser_resource_size_allowed(50 * 1024 * 1024 + 1)).to_equal(false)
expect(browser_subresource_count_allowed(1024)).to_equal(true)
expect(browser_subresource_count_allowed(1025)).to_equal(false)
expect(h1_response_size_allowed(50 * 1024 * 1024 - 1, 1)).to_equal(true)
expect(h1_response_size_allowed(50 * 1024 * 1024, 1)).to_equal(false)
```

</details>

#### rejects short request writes

- rejects short request writes
   - Expected: h1_write_complete(128, 128) is true
   - Expected: h1_write_complete(127, 128) is false
   - Expected: h1_write_complete(-1, 128) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects short request writes")
expect(h1_write_complete(128, 128)).to_equal(true)
expect(h1_write_complete(127, 128)).to_equal(false)
expect(h1_write_complete(-1, 128)).to_equal(false)
```

</details>

#### rejects ambiguous invalid oversized and truncated response framing

- rejects ambiguous invalid oversized and truncated response framing


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects ambiguous invalid oversized and truncated response framing")
expect(h1_content_length([
    Pair("Content-Length", "52428800")
]).is_ok()).to_equal(true)
expect(h1_content_length([
    Pair("Content-Length", "52428801")
]).is_err()).to_equal(true)
expect(h1_content_length([
    Pair("Content-Length", "2"),
    Pair("content-length", "2")
]).is_err()).to_equal(true)
expect(h1_content_length([
    Pair("Content-Length", "nope")
]).is_err()).to_equal(true)
expect(read_response_body_bytes(
    [1u8],
    [Pair("Content-Length", "2")]
).is_err()).to_equal(true)
```

</details>

#### rejects obsolete folded response headers

- rejects obsolete folded response headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects obsolete folded response headers")
expect(parse_http_response_bytes(rt_text_to_bytes(
    "HTTP/1.1 200 OK\r\nSet-Cookie: secret=x;\r\n HttpOnly\r\n\r\n"
)).is_err()).to_equal(true)
expect(read_response_body_bytes(
    [48u8, 13u8, 10u8, 13u8, 10u8],
    [
        Pair("Transfer-Encoding", "chunked"),
        Pair("Content-Length", "0")
    ]
).is_err()).to_equal(true)
```

</details>

#### decodes bounded complete chunks and rejects malformed chunks

- decodes bounded complete chunks and rejects malformed chunks
   - Expected: h1_chunk_size_value("1;ext=yes") equals `1`
   - Expected: h1_chunk_size_value("xyz") equals `-1`
   - Expected: body equals `[97u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes bounded complete chunks and rejects malformed chunks")
expect(h1_chunk_size_value("1;ext=yes")).to_equal(1)
expect(h1_chunk_size_value("xyz")).to_equal(-1)
val decoded = parse_chunked_body_bytes([
    49u8, 13u8, 10u8, 97u8, 13u8, 10u8,
    48u8, 13u8, 10u8, 13u8, 10u8
])
match decoded:
    Ok(body):
        expect(body).to_equal([97u8])
    Err(error):
        fail("valid chunked body rejected: {error}")
expect(parse_chunked_body_bytes([
    51u8, 13u8, 10u8, 97u8
]).is_err()).to_equal(true)
expect(parse_chunked_body_bytes([
    48u8, 13u8, 10u8
]).is_err()).to_equal(true)
```

</details>

#### serializes raw request headers once and preserves the body

- serializes raw request headers once and preserves the body


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes raw request headers once and preserves the body")
val request = FetchRequest(
    method: "POST",
    url: Url.parse_or_opaque("https://example.test/submit?q=1"),
    headers: "Accept: application/json\r\nX-Test: yes\r\n",
    body: [111u8, 107u8],
    mode: RequestMode.SameOrigin,
    credentials: "same-origin"
)

val wire = build_request_bytes(request)

expect(wire).to_start_with("POST /submit?q=1 HTTP/1.1\r\nHost: example.test\r\n")
expect(wire).to_contain("Accept: application/json\r\n")
expect(wire).to_contain("X-Test: yes\r\n")
expect(wire).to_contain("Content-Length: 2\r\n")
expect(wire).to_end_with("\r\n\r\nok")
```

</details>

#### serializes the same raw headers for HTTP/2

- serializes the same raw headers for HTTP/2
   - Expected: headers[0].first equals `:method`
   - Expected: headers[0].second equals `POST`
   - Expected: headers[4].first equals `accept`
   - Expected: headers[4].second equals `application/json`
   - Expected: headers[5].first equals `x-test`
   - Expected: headers[5].second equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes the same raw headers for HTTP/2")
val request = FetchRequest(
    method: "POST",
    url: Url.parse_or_opaque("https://example.test/submit?q=1"),
    headers: "Accept: application/json\r\nX-Test: yes\r\n",
    body: [111u8, 107u8],
    mode: RequestMode.SameOrigin,
    credentials: "same-origin"
)

val headers = build_h2_headers(request)

expect(headers[0].first).to_equal(":method")
expect(headers[0].second).to_equal("POST")
expect(headers[4].first).to_equal("accept")
expect(headers[4].second).to_equal("application/json")
expect(headers[5].first).to_equal("x-test")
expect(headers[5].second).to_equal("yes")
```

</details>

#### includes a non-default port in HTTP authority

- includes a non-default port in HTTP authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("includes a non-default port in HTTP authority")
val request = FetchRequest(
    method: "GET",
    url: Url.parse_or_opaque("https://example.test:8443/path"),
    headers: "",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "same-origin"
)

expect(build_request_bytes(request)).to_contain(
    "\r\nHost: example.test:8443\r\n"
)
expect(build_h2_headers(request)[2].second).to_equal(
    "example.test:8443"
)
```

</details>

#### keeps request framing and authority transport-owned

- keeps request framing and authority transport-owned
   - Expected: wire does not contain `evil.test`
   - Expected: wire does not contain `Transfer-Encoding`
   - Expected: wire does not contain `keep-alive`
   - Expected: h2_headers.len() equals `7`
   - Expected: h2_headers[4].first equals `x-test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps request framing and authority transport-owned")
val request = FetchRequest(
    method: "POST",
    url: Url.parse_or_opaque("https://example.test/upload"),
    headers: "Host: evil.test\r\nContent-Length: 999\r\nTransfer-Encoding: chunked\r\nConnection: keep-alive\r\nX-Test: yes\r\n",
    body: [111u8, 107u8],
    mode: RequestMode.SameOrigin,
    credentials: "same-origin"
)

val wire = build_request_bytes(request)
expect(wire).to_contain("\r\nHost: example.test\r\n")
expect(wire).to_contain("\r\nConnection: close\r\n")
expect(wire).to_contain("\r\nContent-Length: 2\r\n")
expect(wire).to_contain("\r\nX-Test: yes\r\n")
expect(wire.contains("evil.test")).to_equal(false)
expect(wire.contains("Transfer-Encoding")).to_equal(false)
expect(wire.contains("keep-alive")).to_equal(false)

val h2_headers = build_h2_headers(request)
expect(h2_headers.len()).to_equal(7)
expect(h2_headers[4].first).to_equal("x-test")
```

</details>

#### returns an HTTPS mock without opening DNS or TLS

- returns an HTTPS mock without opening DNS or TLS
   - Expected: response.status equals `200`
   - Expected: response.body.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns an HTTPS mock without opening DNS or TLS")
var registry = MockResponseRegistry.create()
registry.register("https://offline.test/", 200, "ok")
set_mock_registry(registry)
val logger = Logger.new("h1-test", BrowserLogLevel.Error)
var client = H1Client.new(
    logger,
    DnsResolver.new(logger, 300),
    TlsManager.new(logger, TlsConfig(
        min_version: TlsVersion.Tls12,
        verify_peer: true,
        sni_hostname: "",
        root_store: [[]],
        enable_x25519_mlkem768: false,
        require_x25519_mlkem768: false
    ))
)
val request = FetchRequest(
    method: "GET",
    url: Url.parse_or_opaque("https://offline.test/"),
    headers: "",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "same-origin"
)

match client.request(request):
    Ok(response):
        expect(response.status).to_equal(200)
        expect(response.body.len()).to_equal(2)
    Err(error):
        fail("HTTPS mock unexpectedly touched the live transport: {error}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser HTTP/1 request serialization.
- Browser HTTP/1 request serialization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc8c4cb6f688a9604c633e9824375b47ae0cdaa1f966d88364b40188acbd477b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc8c4cb6f688a9604c633e9824375b47ae0cdaa1f966d88364b40188acbd477b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc8c4cb6f688a9604c633e9824375b47ae0cdaa1f966d88364b40188acbd477b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses one absolute request deadline instead of refreshing per read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds response accumulation at the cache-sized transport ceiling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_client_request_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects short request writes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
