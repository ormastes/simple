# Shared HTTP Protocol Core — limits, header policy, and path safety

> The shared core (`std.common.net.http_core`) is the single source of truth consumed by BOTH the sync (`nogc_sync_mut/http_server`) and async (`nogc_async_mut/http_server`) transports. An operator reading this manual learns exactly which malformed or hostile requests the server rejects and with which status code, independent of transport: oversized request lines, header floods, invalid or duplicate Content-Length, chunked-encoding smuggling ambiguity, and path traversal are all rejected by ONE policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared HTTP Protocol Core — limits, header policy, and path safety

The shared core (`std.common.net.http_core`) is the single source of truth consumed by BOTH the sync (`nogc_sync_mut/http_server`) and async (`nogc_async_mut/http_server`) transports. An operator reading this manual learns exactly which malformed or hostile requests the server rejects and with which status code, independent of transport: oversized request lines, header floods, invalid or duplicate Content-Length, chunked-encoding smuggling ambiguity, and path traversal are all rejected by ONE policy.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/common/net/http_core_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The shared core (`std.common.net.http_core`) is the single source of truth
consumed by BOTH the sync (`nogc_sync_mut/http_server`) and async
(`nogc_async_mut/http_server`) transports. An operator reading this manual
learns exactly which malformed or hostile requests the server rejects and
with which status code, independent of transport: oversized request lines,
header floods, invalid or duplicate Content-Length, chunked-encoding
smuggling ambiguity, and path traversal are all rejected by ONE policy.

## Shared limit contract

Both transports enforce the same defaults, and both accept caller-supplied
overrides through the same core functions:

| Limit | Default | Violation status |
|-------|---------|------------------|
| Request line length | 8192 bytes | 431 |
| Header count | 100 headers | 431 |
| Header line length | 8192 bytes | 431 |
| Body size (Content-Length or decoded chunked) | 10 MiB | 413 |

## Header policy (`body_decision`)

`body_decision(headers, max_body, allow_chunked)` is the single decision
point for how a request body must be handled:

| Condition | Result |
|-----------|--------|
| Single valid Content-Length within limit | accepted, length returned |
| Duplicate Content-Length | 400 (request-smuggling vector) |
| Negative / non-numeric / overflowing Content-Length | 400 |
| Content-Length above `max_body` | 413 |
| Transfer-Encoding: chunked, `allow_chunked=false` (sync server) | 501 fail closed |
| Transfer-Encoding: chunked, `allow_chunked=true` (async server) | accepted, chunked flag returned |
| Content-Length together with chunked | 400 (RFC 7230 §3.3.3 smuggling ambiguity) |

## Chunked decoding (`decode_chunked_bounded`)

The async transport decodes chunked bodies through the core so the DECODED
size is bounded by `max_body` (413 on overflow) and malformed framing (bad
hex size, truncated chunk, missing terminator) is rejected with 400 instead
of being silently misparsed.

## Path safety (`path_is_safe`)

Traversal guard shared by both routers. Rejected shapes: `..` segments (raw
or percent-encoded, including mixed forms like `..%2f`), double slashes,
backslash traversal, and null bytes (raw or `%00`). Legitimate names that
merely contain dots (`file..txt`, `/foo.%2ebar`) stay allowed.

## Syntax

```simple
use std.common.net.http_core.{
    MAX_REQUEST_LINE, MAX_HEADER_COUNT, MAX_HEADER_LINE, MAX_BODY_SIZE,
    content_length_from_text,      # fn(text) -> i32 (-1 on parse error)
    body_decision,                 # fn([(text,text)], i32, bool) -> (text, i32, bool)
    decode_chunked_bounded,        # fn(text, i32) -> (text, text)
    hex_chunk_size,                # fn(text) -> i32 (-1 on invalid)
    path_is_safe,                  # fn(text) -> bool
    match_route_pattern,           # fn(text, text) -> bool
    extract_route_params           # fn(text, text) -> [(text, text)]
}
```

`body_decision` returns `(err, content_length, is_chunked)`; `err` is `""`
when the request is acceptable, otherwise a status-prefixed message such as
`"413 Content-Length too large: 1025"`. `decode_chunked_bounded` returns
`(err, body)` with the same convention.

## Examples

A duplicate Content-Length header is a request-smuggling vector and is
rejected with 400 before any body byte is read; a path such as
`/static/../etc/passwd` never reaches a handler on either transport.

```simple
val d = body_decision([("Content-Length", "42")], MAX_BODY_SIZE, false)
# d == ("", 42, false)

val bad = body_decision([("Content-Length", "10"), ("Transfer-Encoding", "chunked")], 1024, true)
# bad.0 starts with "400" — smuggling ambiguity, rejected on both transports
```

## Troubleshooting

- A 431 response means a request-line or header limit fired; raise the
  limit at the parser construction site, not in the core defaults.
- A 501 from the sync server for chunked uploads is intentional fail-closed
  behavior — route chunked traffic to the async transport or send a
  Content-Length body.
- If sync and async reject the same request differently, that is a parity
  bug in a transport's wiring, not in this core — both must call the same
  `body_decision` and `path_is_safe`.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (Wave A, AC-1/AC-4).

## Scenarios

### http_core — default limits are the shared contract

#### publishes the same default limits both transports enforce

- Read the shared limit constants
   - Expected: MAX_REQUEST_LINE equals `8192`
   - Expected: MAX_HEADER_COUNT equals `100`
   - Expected: MAX_HEADER_LINE equals `8192`
   - Expected: MAX_BODY_SIZE equals `10485760`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the shared limit constants")
expect(MAX_REQUEST_LINE).to_equal(8192)
expect(MAX_HEADER_COUNT).to_equal(100)
expect(MAX_HEADER_LINE).to_equal(8192)
expect(MAX_BODY_SIZE).to_equal(10485760)
```

</details>

### http_core — Content-Length parsing fails closed

#### accepts a plain digit value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(content_length_from_text("42")).to_equal(42)
```

</details>

#### rejects an empty value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(content_length_from_text("")).to_equal(-1)
```

</details>

#### rejects a negative value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(content_length_from_text("-1")).to_equal(-1)
```

</details>

#### rejects a plus-signed value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(content_length_from_text("+5")).to_equal(-1)
```

</details>

#### rejects non-numeric characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(content_length_from_text("12abc")).to_equal(-1)
```

</details>

#### rejects values overflowing i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(content_length_from_text("2147483648")).to_equal(-1)
```

</details>

#### accepts the exact i32 maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(content_length_from_text("2147483647")).to_equal(2147483647)
```

</details>

### http_core — body_decision with chunked disallowed (sync transport)

#### rejects chunked Transfer-Encoding with 501

- Submit a request advertising Transfer-Encoding: chunked


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a request advertising Transfer-Encoding: chunked")
val d = body_decision([("Transfer-Encoding", "chunked")], 1024, false)
expect(d.0.starts_with("501")).to_be(true)
```

</details>

#### rejects duplicate Content-Length with 400

- Submit two Content-Length headers (request-smuggling vector)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit two Content-Length headers (request-smuggling vector)")
val d = body_decision([("Content-Length", "10"), ("Content-Length", "20")], 1024, false)
expect(d.0.starts_with("400")).to_be(true)
```

</details>

#### rejects Content-Length above the body limit with 413

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = body_decision([("Content-Length", "1025")], 1024, false)
expect(d.0.starts_with("413")).to_be(true)
```

</details>

#### accepts Content-Length exactly at the body limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = body_decision([("Content-Length", "1024")], 1024, false)
expect(d.0).to_equal("")
expect(d.1).to_equal(1024)
expect(d.2).to_be(false)
```

</details>

### http_core — body_decision with chunked allowed (async transport)

#### accepts chunked Transfer-Encoding and reports it

- Submit chunked Transfer-Encoding on the async transport
   - Expected: d.0 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit chunked Transfer-Encoding on the async transport")
val d = body_decision([("Transfer-Encoding", "chunked")], 1024, true)
expect(d.0).to_equal("")
expect(d.2).to_be(true)
```

</details>

#### rejects Content-Length combined with chunked as smuggling ambiguity

- Submit BOTH Content-Length and chunked Transfer-Encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit BOTH Content-Length and chunked Transfer-Encoding")
val d = body_decision([("Content-Length", "10"), ("Transfer-Encoding", "chunked")], 1024, true)
expect(d.0.starts_with("400")).to_be(true)
```

</details>

#### rejects the conflict regardless of header order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = body_decision([("Transfer-Encoding", "chunked"), ("Content-Length", "10")], 1024, true)
expect(d.0.starts_with("400")).to_be(true)
```

</details>

#### still rejects invalid Content-Length with 400

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = body_decision([("Content-Length", "abc")], 1024, true)
expect(d.0.starts_with("400")).to_be(true)
```

</details>

### http_core — path traversal guard

#### allows a normal document path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/index.html")).to_be(true)
```

</details>

#### allows dots inside a filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/file..txt")).to_be(true)
```

</details>

#### rejects a dot-dot segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/static/../etc/passwd")).to_be(false)
```

</details>

#### rejects an encoded dot-dot segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/static/%2e%2e/secret")).to_be(false)
```

</details>

#### rejects an encoded-slash traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/static/..%2fsecret")).to_be(false)
```

</details>

#### rejects double slash prefix bypass

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("//etc/passwd")).to_be(false)
```

</details>

#### rejects null byte injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/index.html%00.png")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
