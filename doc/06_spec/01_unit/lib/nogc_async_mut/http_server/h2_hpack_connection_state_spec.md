# H2 Hpack Connection State Specification

> Tests covering HTTP/2 connection HPACK and request validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# H2 Hpack Connection State Specification

## Scenarios

### HTTP/2 connection HPACK and request validation

#### retains incrementally indexed fields across blocks on one connection

- retains incrementally indexed fields across blocks on one connection
   - Expected: first.is_ok() is true
   - Expected: first_pair.0[0].name equals `x-a`
   - Expected: first_pair.1.table.current_size equals `38`
   - Expected: second.is_ok() is true
   - Expected: second.unwrap().0[0].value equals `one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("retains incrementally indexed fields across blocks on one connection")
# Literal with incremental indexing: x-a: one.
val block1: [u8] = [0x40, 0x03, 0x78, 0x2d, 0x61, 0x03, 0x6f, 0x6e, 0x65]
val first = hpack_decode(block1, hpack_decoder_new(256))
expect(first.is_ok()).to_equal(true)
val first_pair = first.unwrap()
expect(first_pair.0[0].name).to_equal("x-a")
expect(first_pair.1.table.current_size).to_equal(38)

# Unified index 62 refers to the newest dynamic entry.
val block2: [u8] = [0xbe]
val second = hpack_decode(block2, first_pair.1)
expect(second.is_ok()).to_equal(true)
expect(second.unwrap().0[0].value).to_equal("one")
```

</details>

#### rejects dynamic table growth above the connection limit

- rejects dynamic table growth above the connection limit
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects dynamic table growth above the connection limit")
# 001xxxxx with a 5-bit prefix: size update to 257.
val oversized_update: [u8] = [0x3f, 0xe2, 0x01]
val result = hpack_decode(oversized_update, hpack_decoder_new(256))
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects a table size update after a header field

- rejects a table size update after a header field
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a table size update after a header field")
val late_update: [u8] = [0x82, 0x20]
val result = hpack_decode(late_update, hpack_decoder_new(256))
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts a complete ordered request field section

- accepts a complete ordered request field section
   - Expected: h2_validate_request_headers(valid_get_headers()).valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a complete ordered request field section")
expect(h2_validate_request_headers(valid_get_headers()).valid).to_equal(true)
```

</details>

#### rejects missing duplicate late and response pseudo-headers

- rejects missing duplicate late and response pseudo-headers
   - Expected: h2_validate_request_headers([header(":method", "GET")]).valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects missing duplicate late and response pseudo-headers")
expect(h2_validate_request_headers([header(":method", "GET")]).valid).to_equal(false)
expect(h2_validate_request_headers([
    header(":method", "GET"), header(":method", "POST"),
    header(":scheme", "https"), header(":path", "/")
]).valid).to_equal(false)
expect(h2_validate_request_headers([
    header(":method", "GET"), header("accept", "*/*"),
    header(":scheme", "https"), header(":path", "/")
]).valid).to_equal(false)
expect(h2_validate_request_headers([
    header(":method", "GET"), header(":scheme", "https"),
    header(":path", "/"), header(":status", "200")
]).valid).to_equal(false)
```

</details>

#### rejects uppercase and connection-specific request fields

- rejects uppercase and connection-specific request fields
   - Expected: h2_validate_request_headers(uppercase).valid is false
   - Expected: h2_validate_request_headers(forbidden).valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects uppercase and connection-specific request fields")
var uppercase = valid_get_headers()
uppercase.push(header("X-Test", "bad"))
expect(h2_validate_request_headers(uppercase).valid).to_equal(false)
var forbidden = valid_get_headers()
forbidden.push(header("connection", "keep-alive"))
expect(h2_validate_request_headers(forbidden).valid).to_equal(false)
```

</details>

#### rejects invalid field bytes and oversized expanded lists

- rejects invalid field bytes and oversized expanded lists
   - Expected: h2_validate_request_headers(invalid_value).valid is false
   - Expected: h2_validate_request_headers(oversized).valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid field bytes and oversized expanded lists")
var invalid_value = valid_get_headers()
invalid_value.push(header("x-test", "bad\rvalue"))
expect(h2_validate_request_headers(invalid_value).valid).to_equal(false)
var oversized = valid_get_headers()
var i = 0
while i < 2000:
    oversized.push(header("x", "v"))
    i = i + 1
expect(h2_validate_request_headers(oversized).valid).to_equal(false)
```

</details>

#### enforces CONNECT pseudo-header shape

- enforces CONNECT pseudo-header shape
   - Expected: h2_validate_request_headers(valid_connect).valid is true
   - Expected: h2_validate_request_headers(invalid_connect).valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("enforces CONNECT pseudo-header shape")
val valid_connect = [header(":method", "CONNECT"), header(":authority", "example.test:443")]
expect(h2_validate_request_headers(valid_connect).valid).to_equal(true)
val invalid_connect = [
    header(":method", "CONNECT"), header(":scheme", "https"),
    header(":path", "/"), header(":authority", "example.test:443")
]
expect(h2_validate_request_headers(invalid_connect).valid).to_equal(false)
```

</details>

#### allows a matching Host field alongside :authority

- Host and `:authority` may both be present when their values match.
- This is a validator rule only; mismatch and no-authority validation policy remains open.

```simple
step("allows a matching Host field alongside :authority")
val host_only = [
    header(":method", "GET"), header(":scheme", "https"),
    header(":path", "/"), header("host", "example.test")
]
expect(h2_validate_request_headers(host_only).valid).to_equal(true)
var duplicate_authority = valid_get_headers()
duplicate_authority.push(header("host", "example.test"))
expect(h2_validate_request_headers(duplicate_authority).valid).to_equal(true)
```

#### canonicalizes matching conflicting and multiple Host fields to :authority

- Matching and conflicting pairs produce a single downstream Host from `:authority`.
- All incoming Host fields are removed when authority exists; unrelated headers retain their relative order.
- Authority-only requests synthesize one Host, and each decoded request is drained once.

```simple
step("canonicalizes matching conflicting and multiple Host fields to :authority")
val matching = h2_connection_with_headers(20, [
    header(":method", "GET"), header(":scheme", "https"),
    header(":path", "/"), header(":authority", "example.test"),
    header("x-before", "one"), header("host", "example.test"),
    header("x-after", "two")
])
val matching_requests = matching.take_decoded_requests()
expect(matching_requests.len()).to_equal(1)
expect(matching_requests[0].1.headers).to_equal([
    ("x-before", "one"), ("x-after", "two"), ("Host", "example.test")
])
```

#### retains Host without :authority and leaves requests with neither unchanged

- Without `:authority`, incoming Host is retained as received.
- Without either source, extraction adds no Host. This does not establish new validator policy.

```simple
step("retains Host without :authority and leaves requests with neither unchanged")
val host_only = h2_connection_with_headers(24, [
    header(":method", "GET"), header(":scheme", "https"),
    header(":path", "/"), header("host", "host-only.test")
])
val host_only_requests = host_only.take_decoded_requests()
expect(host_only_requests.len()).to_equal(1)
expect(host_only_requests[0].1.headers).to_equal([("host", "host-only.test")])
```

#### preserves OPTIONS star authority and no-authority behavior

- OPTIONS `*` with authority gets one synthesized Host.
- OPTIONS `*` without authority keeps its other headers and gets no Host.

```simple
step("preserves OPTIONS star authority and no-authority behavior")
val with_authority = h2_connection_with_headers(26, [
    header(":method", "OPTIONS"), header(":scheme", "https"),
    header(":path", "*"), header(":authority", "options.test")
])
val with_authority_requests = with_authority.take_decoded_requests()
expect(with_authority_requests.len()).to_equal(1)
expect(with_authority_requests[0].1.path).to_equal("*")
expect(with_authority_requests[0].1.headers).to_equal([("Host", "options.test")])
```

#### keeps CONNECT validation controls while canonicalizing valid authority

- Valid CONNECT with authority uses that value for downstream Host.
- Host-only CONNECT and CONNECT containing scheme/path remain rejected.

```simple
step("keeps CONNECT validation controls while canonicalizing valid authority")
val valid_connect = h2_connection_with_headers(28, [
    header(":method", "CONNECT"), header(":authority", "connect.test:443"),
    header("host", "other.test:443")
])
val valid_requests = valid_connect.take_decoded_requests()
expect(valid_requests.len()).to_equal(1)
expect(valid_requests[0].1.headers).to_equal([("Host", "connect.test:443")])
```

#### accepts only matching CONTINUATION frames inside an open envelope

- accepts only matching CONTINUATION frames inside an open envelope
   - Expected: opened is true
   - Expected: conn.pending_continuation_stream_id equals `1`
   - Expected: continued is true
   - Expected: conn.pending_continuation_stream_id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts only matching CONTINUATION frames inside an open envelope")
var conn = H2Connection.new(10, "peer", 1)
val opened = conn.dispatch_frame(H2Frame.Headers(H2HeadersFrame(
    stream_id: 1, flags: 0, header_block: [0x82]
)))
expect(opened).to_equal(true)
expect(conn.pending_continuation_stream_id).to_equal(1)
val continued = conn.dispatch_frame(H2Frame.Continuation(H2ContinuationFrame(
    stream_id: 1, flags: H2_FLAG_END_HEADERS, header_block: [0x86, 0x84]
)))
expect(continued).to_equal(true)
expect(conn.pending_continuation_stream_id).to_equal(0)
```

</details>

#### rejects a CONTINUATION on an unknown stream or after END_HEADERS

- rejects a CONTINUATION on an unknown stream or after END_HEADERS
   - Expected: unknown_ok is false
   - Expected: unknown.is_goaway_sent() is true
   - Expected: late_ok is false
   - Expected: ended.is_goaway_sent() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a CONTINUATION on an unknown stream or after END_HEADERS")
var unknown = H2Connection.new(11, "peer", 1)
val unknown_ok = unknown.dispatch_frame(H2Frame.Continuation(H2ContinuationFrame(
    stream_id: 1, flags: H2_FLAG_END_HEADERS, header_block: []
)))
expect(unknown_ok).to_equal(false)
expect(unknown.is_goaway_sent()).to_equal(true)

var ended = H2Connection.new(12, "peer", 1)
ended.dispatch_frame(H2Frame.Headers(H2HeadersFrame(
    stream_id: 1, flags: H2_FLAG_END_HEADERS, header_block: [0x82, 0x86, 0x84]
)))
val late_ok = ended.dispatch_frame(H2Frame.Continuation(H2ContinuationFrame(
    stream_id: 1, flags: H2_FLAG_END_HEADERS, header_block: []
)))
expect(late_ok).to_equal(false)
expect(ended.is_goaway_sent()).to_equal(true)
```

</details>

#### rejects interleaved frames and CONTINUATION on a different stream

- rejects interleaved frames and CONTINUATION on a different stream
   - Expected: data_ok is false
   - Expected: interleaved.is_goaway_sent() is true
   - Expected: wrong_ok is false
   - Expected: wrong_stream.is_goaway_sent() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects interleaved frames and CONTINUATION on a different stream")
var interleaved = H2Connection.new(13, "peer", 1)
interleaved.dispatch_frame(H2Frame.Headers(H2HeadersFrame(
    stream_id: 1, flags: 0, header_block: [0x82]
)))
val data_ok = interleaved.dispatch_frame(H2Frame.Data(H2DataFrame(
    stream_id: 1, flags: 0, data: []
)))
expect(data_ok).to_equal(false)
expect(interleaved.is_goaway_sent()).to_equal(true)

var wrong_stream = H2Connection.new(14, "peer", 1)
wrong_stream.dispatch_frame(H2Frame.Headers(H2HeadersFrame(
    stream_id: 1, flags: 0, header_block: [0x82]
)))
val wrong_ok = wrong_stream.dispatch_frame(H2Frame.Continuation(H2ContinuationFrame(
    stream_id: 3, flags: H2_FLAG_END_HEADERS, header_block: []
)))
expect(wrong_ok).to_equal(false)
expect(wrong_stream.is_goaway_sent()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/h2_hpack_connection_state_spec.spl` |
| Updated | 2026-10-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HTTP/2 connection HPACK and request validation.
- HTTP/2 connection HPACK and request validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

Manually synchronized with the executable spec because no admitted self-hosted
runner was available for canonical doc generation in this change. The targeted
spec and maintenance scorecard were not run.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Status: NOT RUN; score is unavailable without the admitted runner.
<!-- sspec-maintain:scorecard:end -->
