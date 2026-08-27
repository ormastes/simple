# Http Content Encoding Specification

> <details>

<!-- sdn-diagram:id=http_content_encoding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=http_content_encoding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

http_content_encoding_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=http_content_encoding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Http Content Encoding Specification

## Scenarios

### Phase 1 HTTP Content-Encoding integration

#### zstd wins when client offers gzip, zstd, lz4, deflate; body round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "lz4;q=0.5, gzip;q=0.9")
expect(_get_header(out.headers, "content-encoding")).to_equal("gzip")
val decoded = gzip_decompress(out.body_bytes) ?? []
expect(decoded.len()).to_equal(payload.len())
```

</details>

#### identity fallback when client only offers unsupported codecs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "br, snappy, weird")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_bytes.len()).to_equal(payload.len())
```

</details>

#### identity fallback for tiny body (below compression threshold)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_tiny_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "zstd")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_bytes.len()).to_equal(payload.len())
```

</details>

#### chunked response: compression skipped regardless of Accept-Encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. headers: [
   - Expected: _get_header(out.headers, "content-encoding") equals `zstd`
   - Expected: _has_header(out.headers, "content-length") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. headers: [
   - Expected: _get_header(out.headers, "content-encoding") equals `gzip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
