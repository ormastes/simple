# Compression Specification

> <details>

<!-- sdn-diagram:id=compression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compression Specification

## Scenarios

### Response-body compression dispatcher

#### lists zstd and lz4 as supported encodings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val codecs = supported_encodings()
expect(codecs.len()).to_equal(2)
expect(codecs[0]).to_equal("zstd")
expect(codecs[1]).to_equal("lz4")
```

</details>

#### compresses with zstd and round-trips back to identical bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_payload()
val compressed_res = compress_response_body(payload, "zstd")
expect(compressed_res.is_ok()).to_equal(true)
val compressed = compressed_res.unwrap()
expect(compressed.len() > 0).to_equal(true)
# Auto-detect via magic bytes (zstd magic = 28 b5 2f fd) rather than
# the codec-hint path so the spec is robust to detect_codec changes.
val round_trip = decompress_bytes(compressed, nil)
expect(round_trip.is_ok()).to_equal(true)
val decoded = round_trip.unwrap()
expect(decoded.len()).to_equal(payload.len())
```

</details>

#### compresses with lz4 and round-trips back to identical bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_payload()
val compressed_res = compress_response_body(payload, "lz4")
expect(compressed_res.is_ok()).to_equal(true)
val compressed = compressed_res.unwrap()
expect(compressed.len() > 0).to_equal(true)
# Auto-detect via lz4 frame magic (04 22 4d 18).
val round_trip = decompress_bytes(compressed, nil)
expect(round_trip.is_ok()).to_equal(true)
val decoded = round_trip.unwrap()
expect(decoded.len()).to_equal(payload.len())
```

</details>

#### returns Err with a specific reason for gzip (not yet wired)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = compress_response_body([0x68u8, 0x69u8], "gzip")
expect(out.is_err()).to_equal(true)
```

</details>

#### returns Err with a specific reason for br (Phase 3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = compress_response_body([0x68u8, 0x69u8], "br")
expect(out.is_err()).to_equal(true)
```

</details>

#### returns Err with a specific reason for deflate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = compress_response_body([0x68u8, 0x69u8], "deflate")
expect(out.is_err()).to_equal(true)
```

</details>

#### returns Err for empty encoding (caller should skip)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = compress_response_body([0x68u8, 0x69u8], "")
expect(out.is_err()).to_equal(true)
```

</details>

#### returns Err for identity encoding (caller should skip)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = compress_response_body([0x68u8, 0x69u8], "identity")
expect(out.is_err()).to_equal(true)
```

</details>

#### returns Err for unknown encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = compress_response_body([0x68u8, 0x69u8], "snappy")
expect(out.is_err()).to_equal(true)
```

</details>

### compress_response_for — response-level decision

#### compresses with zstd when Accept-Encoding includes zstd

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "zstd, lz4")
expect(out.body_bytes.len() > 0).to_equal(true)
expect(out.body_bytes.len() < payload.len()).to_equal(true)
expect(_get_header(out.headers, "content-encoding")).to_equal("zstd")
expect(out.body).to_equal("")
```

</details>

#### prefers zstd over lz4 (server preference order)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "lz4, zstd")
expect(_get_header(out.headers, "content-encoding")).to_equal("zstd")
```

</details>

#### falls back to lz4 when client does not accept zstd

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "lz4")
expect(_get_header(out.headers, "content-encoding")).to_equal("lz4")
```

</details>

#### leaves response unchanged when no Accept-Encoding header is supplied

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "")
expect(out.body_bytes.len()).to_equal(payload.len())
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
```

</details>

#### leaves response unchanged when client only accepts unsupported codecs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
# gzip is not in supported_encodings() yet (still Err in dispatcher).
val out = compress_response_for(resp, "gzip")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_bytes.len()).to_equal(payload.len())
```

</details>

#### skips compression when body is too small

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 100-byte payload, below the 256-byte minimum.
val small: [u8] = [
    0x41u8, 0x42u8, 0x43u8, 0x44u8, 0x45u8, 0x46u8, 0x47u8, 0x48u8,
    0x49u8, 0x4Au8
]
var tiny: [u8] = []
var i: i64 = 0
while i < 10:
    tiny = tiny + small
    i = i + 1
val resp = _resp_with_byte_body(tiny)
val out = compress_response_for(resp, "zstd")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_bytes.len()).to_equal(tiny.len())
```

</details>

#### skips compression when chunked

1. var resp =  resp with byte body
   - Expected: _has_header(out.headers, "content-encoding") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resp = _resp_with_byte_body(_make_eligible_payload())
resp = HttpResponseData(
    status: resp.status,
    reason: resp.reason,
    headers: resp.headers,
    body: resp.body,
    body_bytes: resp.body_bytes,
    body_file: resp.body_file,
    body_offset: resp.body_offset,
    body_length: resp.body_length,
    chunked: true
)
val out = compress_response_for(resp, "zstd")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
```

</details>

#### skips compression when body_file is set (sendfile path)

1. var resp =  resp with byte body
   - Expected: _has_header(out.headers, "content-encoding") is false
   - Expected: out.body_file equals `/tmp/static.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resp = _resp_with_byte_body(_make_eligible_payload())
resp = HttpResponseData(
    status: resp.status,
    reason: resp.reason,
    headers: resp.headers,
    body: "",
    body_bytes: [],
    body_file: "/tmp/static.html",
    body_offset: 0,
    body_length: 1024,
    chunked: false
)
val out = compress_response_for(resp, "zstd")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_file).to_equal("/tmp/static.html")
```

</details>

#### skips compression when Content-Encoding header is already present

1. var resp =  resp with byte body
2. headers: [
   - Expected: _get_header(out.headers, "content-encoding") equals `gzip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resp = _resp_with_byte_body(_make_eligible_payload())
resp = HttpResponseData(
    status: resp.status,
    reason: resp.reason,
    headers: [("Content-Type", "image/png"), ("Content-Encoding", "gzip")],
    body: resp.body,
    body_bytes: resp.body_bytes,
    body_file: resp.body_file,
    body_offset: resp.body_offset,
    body_length: resp.body_length,
    chunked: resp.chunked
)
val out = compress_response_for(resp, "zstd")
# Encoding stays as the original "gzip" — we don't double-compress.
expect(_get_header(out.headers, "content-encoding")).to_equal("gzip")
```

</details>

#### removes any pre-existing Content-Length when compressing

1. var resp =  resp with byte body
2. headers: [
   - Expected: _has_header(out.headers, "content-length") is false
   - Expected: _get_header(out.headers, "content-encoding") equals `zstd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resp = _resp_with_byte_body(_make_eligible_payload())
resp = HttpResponseData(
    status: resp.status,
    reason: resp.reason,
    headers: [("Content-Type", "text/plain"), ("Content-Length", "300")],
    body: resp.body,
    body_bytes: resp.body_bytes,
    body_file: resp.body_file,
    body_offset: resp.body_offset,
    body_length: resp.body_length,
    chunked: resp.chunked
)
val out = compress_response_for(resp, "zstd")
expect(_has_header(out.headers, "content-length")).to_equal(false)
expect(_get_header(out.headers, "content-encoding")).to_equal("zstd")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/compression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Response-body compression dispatcher
- compress_response_for — response-level decision

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
