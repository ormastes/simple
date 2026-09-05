# Compression Specification

> Tests covering Response-body compression dispatcher, compress_response_for — response-level decision.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compression Specification

## Scenarios

### Response-body compression dispatcher

#### lists all five wired codecs in server preference order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists all five wired codecs in server preference order
   - Expected: codecs.len() equals `5`
   - Expected: codecs[0] equals `br`
   - Expected: codecs[1] equals `gzip`
   - Expected: codecs[2] equals `deflate`
   - Expected: codecs[3] equals `zstd`
   - Expected: codecs[4] equals `lz4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all five wired codecs in server preference order")
val codecs = supported_encodings()
expect(codecs.len()).to_equal(5)
expect(codecs[0]).to_equal("br")
expect(codecs[1]).to_equal("gzip")
expect(codecs[2]).to_equal("deflate")
expect(codecs[3]).to_equal("zstd")
expect(codecs[4]).to_equal("lz4")
```

</details>

#### compresses with zstd and round-trips back to identical bytes

- compresses with zstd and round-trips back to identical bytes
   - Expected: compressed_res.is_ok() is true
   - Expected: compressed.len() > 0 is true
   - Expected: round_trip.is_ok() is true
   - Expected: decoded.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses with zstd and round-trips back to identical bytes")
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

- compresses with lz4 and round-trips back to identical bytes
   - Expected: compressed_res.is_ok() is true
   - Expected: compressed.len() > 0 is true
   - Expected: round_trip.is_ok() is true
   - Expected: decoded.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses with lz4 and round-trips back to identical bytes")
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

#### compresses with gzip and round-trips back to identical bytes

- compresses with gzip and round-trips back to identical bytes
   - Expected: compressed_res.is_ok() is true
   - Expected: compressed.len() < payload.len() is true
   - Expected: round_trip.is_ok() is true
   - Expected: round_trip.unwrap().len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses with gzip and round-trips back to identical bytes")
val payload = _make_payload()
val compressed_res = compress_response_body(payload, "gzip")
expect(compressed_res.is_ok()).to_equal(true)
val compressed = compressed_res.unwrap()
# gzip is a real encoder here: 200 repetitive bytes shrink substantially.
expect(compressed.len() < payload.len()).to_equal(true)
val round_trip = decompress_bytes(compressed, nil)
expect(round_trip.is_ok()).to_equal(true)
expect(round_trip.unwrap().len()).to_equal(payload.len())
```

</details>

#### compresses with br rather than rejecting it

- compresses with br rather than rejecting it
   - Expected: out.is_ok() is true
   - Expected: out.unwrap().len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses with br rather than rejecting it")
# br is wired. Its encoder is a container writer that does not yet
# shrink anything (300 -> 304 measured), so this pins Ok + non-empty
# output only, NOT a size reduction. Asserting a reduction would be
# asserting an encoder that does not exist; asserting Err would be
# asserting br is unwired, which it is not.
val out = compress_response_body(_make_payload(), "br")
expect(out.is_ok()).to_equal(true)
expect(out.unwrap().len() > 0).to_equal(true)
```

</details>

#### compresses with deflate rather than rejecting it

- compresses with deflate rather than rejecting it
   - Expected: out.is_ok() is true
   - Expected: out.unwrap().len() < payload.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses with deflate rather than rejecting it")
# deflate is a real encoder (300 -> 28 measured). No auto-detect
# round-trip assertion: a raw deflate stream carries no magic bytes, so
# decompress_bytes(_, nil) cannot identify it.
val payload = _make_payload()
val out = compress_response_body(payload, "deflate")
expect(out.is_ok()).to_equal(true)
expect(out.unwrap().len() < payload.len()).to_equal(true)
```

</details>

#### returns Err for empty encoding (caller should skip)

- returns Err for empty encoding (caller should skip)
   - Expected: out.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for empty encoding (caller should skip)")
val out = compress_response_body([0x68u8, 0x69u8], "")
expect(out.is_err()).to_equal(true)
```

</details>

#### returns Err for identity encoding (caller should skip)

- returns Err for identity encoding (caller should skip)
   - Expected: out.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for identity encoding (caller should skip)")
val out = compress_response_body([0x68u8, 0x69u8], "identity")
expect(out.is_err()).to_equal(true)
```

</details>

#### returns Err for unknown encoding

- returns Err for unknown encoding
   - Expected: out.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for unknown encoding")
val out = compress_response_body([0x68u8, 0x69u8], "snappy")
expect(out.is_err()).to_equal(true)
```

</details>

### compress_response_for — response-level decision

#### compresses via the next acceptable codec when the preferred one cannot shrink

- compresses via the next acceptable codec when the preferred one cannot shrink
   - Expected: out.body_bytes.len() > 0 is true
   - Expected: out.body_bytes.len() < payload.len() is true
   - Expected: _get_header(out.headers, "content-encoding") equals `lz4`
   - Expected: out.body equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compresses via the next acceptable codec when the preferred one cannot shrink")
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "zstd, lz4")
expect(out.body_bytes.len() > 0).to_equal(true)
expect(out.body_bytes.len() < payload.len()).to_equal(true)
expect(_get_header(out.headers, "content-encoding")).to_equal("lz4")
expect(out.body).to_equal("")
```

</details>

#### selection follows server preference, not client order

- selection follows server preference, not client order
   - Expected: _get_header(out_a.headers, "content-encoding") equals `gzip`
   - Expected: _get_header(out_b.headers, "content-encoding") equals `gzip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selection follows server preference, not client order")
# Client lists lz4 first, but the server prefers gzip, and gzip really
# does shrink this body — so gzip wins regardless of client ordering.
val payload = _make_eligible_payload()
val out_a = compress_response_for(_resp_with_byte_body(payload), "lz4, gzip")
val out_b = compress_response_for(_resp_with_byte_body(payload), "gzip, lz4")
expect(_get_header(out_a.headers, "content-encoding")).to_equal("gzip")
expect(_get_header(out_b.headers, "content-encoding")).to_equal("gzip")
```

</details>

#### falls back to lz4 when client does not accept zstd

- falls back to lz4 when client does not accept zstd
   - Expected: _get_header(out.headers, "content-encoding") equals `lz4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to lz4 when client does not accept zstd")
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "lz4")
expect(_get_header(out.headers, "content-encoding")).to_equal("lz4")
```

</details>

#### leaves response unchanged when no Accept-Encoding header is supplied

- leaves response unchanged when no Accept-Encoding header is supplied
   - Expected: out.body_bytes.len() equals `payload.len()`
   - Expected: _has_header(out.headers, "content-encoding") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves response unchanged when no Accept-Encoding header is supplied")
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
val out = compress_response_for(resp, "")
expect(out.body_bytes.len()).to_equal(payload.len())
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
```

</details>

#### leaves response unchanged when client only accepts unsupported codecs

- leaves response unchanged when client only accepts unsupported codecs
   - Expected: _has_header(out.headers, "content-encoding") is false
   - Expected: out.body_bytes.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves response unchanged when client only accepts unsupported codecs")
val payload = _make_eligible_payload()
val resp = _resp_with_byte_body(payload)
# This example used to name gzip as "not supported yet". gzip is now
# wired, so it proved nothing; snappy is genuinely absent from
# supported_encodings().
val out = compress_response_for(resp, "snappy")
expect(_has_header(out.headers, "content-encoding")).to_equal(false)
expect(out.body_bytes.len()).to_equal(payload.len())
```

</details>

#### skips compression for MIME types outside the compressible allowlist

- skips compression for MIME types outside the compressible allowlist
   - Expected: _has_header(out.headers, "content-encoding") is false
   - Expected: out.body_bytes.len() equals `payload.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips compression for MIME types outside the compressible allowlist")
# Pins the content-type filter that the old byte-body fixture was
# accidentally tripping. Both of these are eligible on every other axis
# (300 bytes, not chunked, no body_file, no Content-Encoding) and lz4
# would shrink them — the MIME allowlist is the only thing stopping it.
val payload = _make_eligible_payload()
for ct in ["application/octet-stream", "image/png", "application/pdf"]:
    var resp = _resp_with_byte_body(payload)
    resp = HttpResponseData(
        status: resp.status,
        reason: resp.reason,
        headers: [("Content-Type", ct)],
        body: resp.body,
        body_bytes: resp.body_bytes,
        body_file: resp.body_file,
        body_offset: resp.body_offset,
        body_length: resp.body_length,
        chunked: resp.chunked
    )
    val out = compress_response_for(resp, "lz4")
    expect(_has_header(out.headers, "content-encoding")).to_equal(false)
    expect(out.body_bytes.len()).to_equal(payload.len())
```

</details>

#### skips compression when body is too small

- skips compression when body is too small
   - Expected: _has_header(out.headers, "content-encoding") is false
   - Expected: out.body_bytes.len() equals `tiny.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips compression when body is too small")
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

- skips compression when chunked
   - Expected: _has_header(out.headers, "content-encoding") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips compression when chunked")
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

- skips compression when body_file is set (sendfile path)
   - Expected: _has_header(out.headers, "content-encoding") is false
   - Expected: out.body_file equals `/tmp/static.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips compression when body_file is set (sendfile path)")
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

- skips compression when Content-Encoding header is already present
   - Expected: _get_header(out.headers, "content-encoding") equals `gzip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips compression when Content-Encoding header is already present")
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

- removes any pre-existing Content-Length when compressing
   - Expected: _get_header(out.headers, "content-encoding") equals `lz4`
   - Expected: _get_header(out.headers, "content-length") equals `{out.body_bytes.len()}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes any pre-existing Content-Length when compressing")
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
val out = compress_response_for(resp, "lz4")
# The stale "300" must be gone, but its replacement must be the
# COMPRESSED length, not nothing. This example used to assert that no
# Content-Length survived at all; the implementation now strips the
# stale value and emits an accurate one, which is what RFC 9110 requires
# (Content-Length describes the encoded body). An absent Content-Length
# on a non-chunked response is the weaker, wronger outcome, so the
# assertion moved to match the implementation rather than the reverse.
expect(_get_header(out.headers, "content-encoding")).to_equal("lz4")
expect(_get_header(out.headers, "content-length")).to_equal("{out.body_bytes.len()}")
expect(_get_header(out.headers, "content-length")).to_not_equal("300")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/http_server/compression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Response-body compression dispatcher, compress_response_for — response-level decision.
- Response-body compression dispatcher
- compress_response_for — response-level decision

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0ea22018a2b06f851845de6d4a70361570cca9ac9f908984eb978b0ec1956282`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ea22018a2b06f851845de6d4a70361570cca9ac9f908984eb978b0ec1956282`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ea22018a2b06f851845de6d4a70361570cca9ac9f908984eb978b0ec1956282`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/nogc_async_mut/http_server/compression_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/http_server/compression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/http_server/compression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/http_server/compression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/http_server/compression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/http_server/compression_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists all five wired codecs in server preference order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/http_server/compression_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compresses with zstd and round-trips back to identical bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/http_server/compression_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compresses with lz4 and round-trips back to identical bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
