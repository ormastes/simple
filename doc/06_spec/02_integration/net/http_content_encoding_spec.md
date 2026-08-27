# Http Content Encoding Specification

> Tests covering Phase 1 HTTP Content-Encoding integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Http Content Encoding Specification

## Scenarios

### Phase 1 HTTP Content-Encoding integration

#### zstd wins when client offers gzip, zstd, lz4, deflate; body round-trips

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- zstd wins when client offers gzip, zstd, lz4, deflate; body round-trips
   - Expected: _get_header(out.headers, "content-encoding") equals `zstd`
   - Expected: out.body_bytes.len() > 0 is true
   - Expected: round_trip.is_ok() is true
   - Expected: decoded.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("zstd wins when client offers gzip, zstd, lz4, deflate; body round-trips")
val payload = _make_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "gzip, zstd, lz4, deflate")
expect(_get_header(out.headers, "content-encoding")).to_equal("zstd")
expect(out.body_bytes.len() > 0).to_equal(true)
val round_trip = decompress_bytes(out.body_bytes, nil)
expect(round_trip.is_ok()).to_equal(true)
val decoded = round_trip.unwrap()
expect(decoded.len()).to_equal(payload.len())
```

</details>

#### gzip-only client: Content-Encoding gzip, body round-trips via gzip_decompress

- gzip-only client: Content-Encoding gzip, body round-trips via gzip_decompress
   - Expected: _get_header(out.headers, "content-encoding") equals `gzip`
   - Expected: out.body_bytes.len() > 0 is true
   - Expected: out.body_bytes[0] equals `0x1fu8`
   - Expected: out.body_bytes[1] equals `0x8bu8`
   - Expected: decoded.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gzip-only client: Content-Encoding gzip, body round-trips via gzip_decompress")
val payload = _make_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "gzip")
expect(_get_header(out.headers, "content-encoding")).to_equal("gzip")
expect(out.body_bytes.len() > 0).to_equal(true)
# Verify gzip frame magic (RFC 1952)
expect(out.body_bytes[0]).to_equal(0x1fu8)
expect(out.body_bytes[1]).to_equal(0x8bu8)
val decoded = gzip_decompress(out.body_bytes) ?? []
expect(decoded.len()).to_equal(payload.len())
```

</details>

#### deflate-only client: Content-Encoding deflate, zlib 0x78 magic, round-trips

- deflate-only client: Content-Encoding deflate, zlib 0x78 magic, round-trips
   - Expected: _get_header(out.headers, "content-encoding") equals `deflate`
   - Expected: out.body_bytes.len() > 0 is true
   - Expected: out.body_bytes[0] equals `0x78u8`
   - Expected: decoded.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("deflate-only client: Content-Encoding deflate, zlib 0x78 magic, round-trips")
val payload = _make_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "deflate")
expect(_get_header(out.headers, "content-encoding")).to_equal("deflate")
expect(out.body_bytes.len() > 0).to_equal(true)
expect(out.body_bytes[0]).to_equal(0x78u8)
val decoded = zlib_decompress(out.body_bytes) ?? []
expect(decoded.len()).to_equal(payload.len())
```

</details>

#### lz4-only client: Content-Encoding lz4, body round-trips via decompress_bytes

- lz4-only client: Content-Encoding lz4, body round-trips via decompress_bytes
   - Expected: _get_header(out.headers, "content-encoding") equals `lz4`
   - Expected: out.body_bytes.len() > 0 is true
   - Expected: round_trip.is_ok() is true
   - Expected: decoded.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lz4-only client: Content-Encoding lz4, body round-trips via decompress_bytes")
val payload = _make_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "lz4")
expect(_get_header(out.headers, "content-encoding")).to_equal("lz4")
expect(out.body_bytes.len() > 0).to_equal(true)
val round_trip = decompress_bytes(out.body_bytes, nil)
expect(round_trip.is_ok()).to_equal(true)
val decoded = round_trip.unwrap()
expect(decoded.len()).to_equal(payload.len())
```

</details>

#### q-value: gzip;q=0.9 beats lz4;q=0.5 — highest q wins, server order breaks ties

- q-value: gzip;q=0.9 beats lz4;q=0.5 — highest q wins, server order breaks ties
   - Expected: _get_header(out.headers, "content-encoding") equals `gzip`
   - Expected: decoded.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("q-value: gzip;q=0.9 beats lz4;q=0.5 — highest q wins, server order breaks ties")
val payload = _make_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "lz4;q=0.5, gzip;q=0.9")
expect(_get_header(out.headers, "content-encoding")).to_equal("gzip")
val decoded = gzip_decompress(out.body_bytes) ?? []
expect(decoded.len()).to_equal(payload.len())
```

</details>

#### identity fallback when client only offers unsupported codecs

- identity fallback when client only offers unsupported codecs
   - Expected: _has_header(out.headers, "content-encoding") is false
   - Expected: out.body_bytes.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("identity fallback when client only offers unsupported codecs")
val payload = _make_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "br, snappy, weird")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_bytes.len()).to_equal(payload.len())
```

</details>

#### identity fallback for tiny body (below compression threshold)

- identity fallback for tiny body (below compression threshold)
   - Expected: _has_header(out.headers, "content-encoding") is false
   - Expected: out.body_bytes.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("identity fallback for tiny body (below compression threshold)")
val payload = _make_tiny_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "zstd")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_bytes.len()).to_equal(payload.len())
```

</details>

#### chunked response: compression skipped regardless of Accept-Encoding

- chunked response: compression skipped regardless of Accept-Encoding
   - Expected: _has_header(out.headers, "content-encoding") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("chunked response: compression skipped regardless of Accept-Encoding")
val payload = _make_payload()
val base = _resp_with_byte_body(payload)
val resp = HttpResponseData(
    status: base.status,
    reason: base.reason,
    headers: base.headers,
    body: base.body,
    body_bytes: base.body_bytes,
    body_file: base.body_file,
    body_offset: base.body_offset,
    body_length: base.body_length,
    chunked: true
)
val out = compress_response_for(resp, "zstd, gzip, lz4, deflate")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
```

</details>

#### body_file set: compression skipped, body_file preserved

- body_file set: compression skipped, body_file preserved
   - Expected: _has_header(out.headers, "content-encoding") is false
   - Expected: out.body_file equals `/tmp/foo.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("body_file set: compression skipped, body_file preserved")
val base = _resp_with_byte_body(_make_payload())
val resp = HttpResponseData(
    status: base.status,
    reason: base.reason,
    headers: base.headers,
    body: "",
    body_bytes: [],
    body_file: "/tmp/foo.html",
    body_offset: 0,
    body_length: 1024,
    chunked: false
)
val out = compress_response_for(resp, "zstd")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_file).to_equal("/tmp/foo.html")
```

</details>

#### Content-Length removed from headers after successful compression

- Content-Length removed from headers after successful compression
   - Expected: _get_header(out.headers, "content-encoding") equals `zstd`
   - Expected: _has_header(out.headers, "content-length") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Content-Length removed from headers after successful compression")
val payload = _make_payload()
val base = _resp_with_byte_body(payload)
val resp = HttpResponseData(
    status: base.status,
    reason: base.reason,
    headers: [("Content-Type", "text/plain"), ("Content-Length", "1120")],
    body: base.body,
    body_bytes: base.body_bytes,
    body_file: base.body_file,
    body_offset: base.body_offset,
    body_length: base.body_length,
    chunked: base.chunked
)
val out = compress_response_for(resp, "zstd")
expect(_get_header(out.headers, "content-encoding")).to_equal("zstd")
expect(_has_header(out.headers, "content-length")).to_equal(false)
```

</details>

#### existing Content-Encoding preserved: no double-encoding

- existing Content-Encoding preserved: no double-encoding
   - Expected: _get_header(out.headers, "content-encoding") equals `gzip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("existing Content-Encoding preserved: no double-encoding")
val payload = _make_payload()
val base = _resp_with_byte_body(payload)
val resp = HttpResponseData(
    status: base.status,
    reason: base.reason,
    headers: [("Content-Type", "image/png"), ("Content-Encoding", "gzip")],
    body: base.body,
    body_bytes: base.body_bytes,
    body_file: base.body_file,
    body_offset: base.body_offset,
    body_length: base.body_length,
    chunked: base.chunked
)
val out = compress_response_for(resp, "zstd")
expect(_get_header(out.headers, "content-encoding")).to_equal("gzip")
```

</details>

#### multi-codec selection is deterministic: zstd always wins over 3 runs

- multi-codec selection is deterministic: zstd always wins over 3 runs
   - Expected: _get_header(out1.headers, "content-encoding") equals `zstd`
   - Expected: _get_header(out2.headers, "content-encoding") equals `zstd`
   - Expected: _get_header(out3.headers, "content-encoding") equals `zstd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("multi-codec selection is deterministic: zstd always wins over 3 runs")
val payload = _make_payload()
val accept = "deflate, gzip, lz4, zstd"

val resp1 = _resp_with_byte_body(payload)
val out1 = compress_response_for(resp1, accept)
expect(_get_header(out1.headers, "content-encoding")).to_equal("zstd")

val resp2 = _resp_with_byte_body(payload)
val out2 = compress_response_for(resp2, accept)
expect(_get_header(out2.headers, "content-encoding")).to_equal("zstd")

val resp3 = _resp_with_byte_body(payload)
val out3 = compress_response_for(resp3, accept)
expect(_get_header(out3.headers, "content-encoding")).to_equal("zstd")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/net/http_content_encoding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Phase 1 HTTP Content-Encoding integration.
- Phase 1 HTTP Content-Encoding integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `544ff4e93ec6573a324189e9d4bea5839bd381cef5877849bb71292197f0f1dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `544ff4e93ec6573a324189e9d4bea5839bd381cef5877849bb71292197f0f1dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `544ff4e93ec6573a324189e9d4bea5839bd381cef5877849bb71292197f0f1dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/net/http_content_encoding_spec.spl
mirror: doc/06_spec/02_integration/net/http_content_encoding_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/net/http_content_encoding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/net/http_content_encoding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/net/http_content_encoding_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zstd wins when client offers gzip, zstd, lz4, deflate; body round-trips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/net/http_content_encoding_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gzip-only client: Content-Encoding gzip, body round-trips via gzip_decompress' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/net/http_content_encoding_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deflate-only client: Content-Encoding deflate, zlib 0x78 magic, round-trips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
