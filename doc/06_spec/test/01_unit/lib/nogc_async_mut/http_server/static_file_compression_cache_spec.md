# static_file_compression_cache_spec

> Specification for `serve_compressed_or_plain` — the compression-cache

<!-- sdn-diagram:id=static_file_compression_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_file_compression_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_file_compression_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_file_compression_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# static_file_compression_cache_spec

Specification for `serve_compressed_or_plain` — the compression-cache

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/static_file_compression_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Specification for `serve_compressed_or_plain` — the compression-cache
integration in `src/lib/nogc_async_mut/http_server/static_file.spl`.

Tests the per-request compression decision and cache wiring directly,
without spinning up a filesystem or HTTP server. The helper is the
exact path `StaticFileHandler.handle()` takes for files <= 64 KiB.

All compressible payloads must be >= COMPRESSION_MIN_BODY_BYTES (150)
once compressed — but `compress_response_body` itself does not enforce
that bound, so we just feed it >= 200 bytes of repeated text and the
zstd codec produces a valid frame regardless of compressibility.

Codec choice in this spec:
  - `zstd`   — succeeds in `compress_response_body` today.
  - `gzip`   — currently returns `Err(...)` from the dispatcher; used
               for the compression-error fallback case.

## Scenarios

### static_file compression cache integration

#### MIME helper accepts text/html and rejects image/png

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_mime_compressible("text/html; charset=utf-8")).to_equal(true)
expect(is_mime_compressible("application/javascript; charset=utf-8")).to_equal(true)
expect(is_mime_compressible("application/json; charset=utf-8")).to_equal(true)
expect(is_mime_compressible("image/svg+xml")).to_equal(true)
expect(is_mime_compressible("application/wasm")).to_equal(true)
expect(is_mime_compressible("image/png")).to_equal(false)
expect(is_mime_compressible("application/octet-stream")).to_equal(false)
```

</details>

#### no Accept-Encoding header serves a plain response

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(8, 65536)
val body = _make_text_payload()
val resp = serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/index.html", "", cache
)
expect(resp.status).to_equal(200)
expect(resp.body).to_equal(body)
expect(resp.body_bytes.len()).to_equal(0)
# No Content-Encoding header on the plain path.
var has_ce: bool = false
for h in resp.headers:
    if h.0.lower() == "content-encoding":
        has_ce = true
expect(has_ce).to_equal(false)
# Cache must remain empty — we never compressed.
expect(cache.entries.len()).to_equal(0)
```

</details>

#### ineligible MIME (image/png) skips compression even with Accept-Encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(8, 65536)
val body = _make_text_payload()
val resp = serve_compressed_or_plain(
    body, "image/png", "/logo.png", "zstd", cache
)
expect(resp.status).to_equal(200)
expect(resp.body).to_equal(body)
expect(resp.body_bytes.len()).to_equal(0)
expect(cache.entries.len()).to_equal(0)
```

</details>

#### cache miss compresses, caches, and emits Content-Encoding + Vary

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/index.html", "zstd", cache
)
expect(resp.status).to_equal(200)
# Compressed responses carry bytes, not text body.
expect(resp.body).to_equal("")
expect(resp.body_bytes.len() > 0).to_equal(true)
# Headers contain Content-Encoding: zstd and Vary: Accept-Encoding.
var enc: text = ""
var vary: text = ""
for h in resp.headers:
    if h.0.lower() == "content-encoding":
        enc = h.1
    if h.0.lower() == "vary":
        vary = h.1
expect(enc).to_equal("zstd")
expect(vary).to_equal("Accept-Encoding")
# Exactly one cached entry: keyed by (path, encoding).
expect(cache.entries.len()).to_equal(1)
```

</details>

#### cache hit serves identical bytes without recompressing

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
# Prime the cache.
val first = serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/index.html", "zstd", cache
)
expect(first.body_bytes.len() > 0).to_equal(true)
val first_len = first.body_bytes.len()
val cached_after_first = cache.entries.len()
# Second request: identical args. Must serve the same bytes from
# cache without growing the entry count.
val second = serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/index.html", "zstd", cache
)
expect(second.status).to_equal(200)
expect(second.body_bytes.len()).to_equal(first_len)
expect(cache.entries.len()).to_equal(cached_after_first)
# Content-Encoding still set on the hit.
var enc2: text = ""
for h in second.headers:
    if h.0.lower() == "content-encoding":
        enc2 = h.1
expect(enc2).to_equal("zstd")
```

</details>

#### compression error (gzip not yet wired) falls back to plain response

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `compress_response_body` returns Err for gzip today. The handler
# must NOT fail the request — it falls back to identity.
val cache = StaticCompressionCache.new(8, 65536)
val body = _make_text_payload()
val resp = serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/page.html", "gzip", cache
)
expect(resp.status).to_equal(200)
expect(resp.body).to_equal(body)
expect(resp.body_bytes.len()).to_equal(0)
# Cache must remain empty — failed compression never stores.
expect(cache.entries.len()).to_equal(0)
# No misleading Content-Encoding header on the fallback.
var has_ce: bool = false
for h in resp.headers:
    if h.0.lower() == "content-encoding":
        has_ce = true
expect(has_ce).to_equal(false)
```

</details>

#### different paths share the cache as separate entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val r1 = serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/a.html", "zstd", cache
)
val r2 = serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/b.html", "zstd", cache
)
expect(r1.body_bytes.len() > 0).to_equal(true)
expect(r2.body_bytes.len() > 0).to_equal(true)
expect(cache.entries.len()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
