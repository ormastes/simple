# static_file_handler_compression_spec

> Wave 15-D — Spec: StaticFileHandler ↔ StaticCompressionCache wiring.

<!-- sdn-diagram:id=static_file_handler_compression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_file_handler_compression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_file_handler_compression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_file_handler_compression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# static_file_handler_compression_spec

Wave 15-D — Spec: StaticFileHandler ↔ StaticCompressionCache wiring.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/static_file_handler_compression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Wave 15-D — Spec: StaticFileHandler ↔ StaticCompressionCache wiring.

Exercises the per-request compression decision at the handler-helper
boundary, focusing on `Accept-Encoding` negotiation cases the existing
`static_file_compression_cache_spec.spl` does NOT cover:

  - Codec preference order across multi-codec Accept-Encoding lists.
  - Server preference (zstd before lz4) when client lists both equally.
  - q=0 explicitly forbids an otherwise-supported codec.
  - Wildcard `*` falls back to the server's first supported codec.
  - Identity-only Accept-Encoding serves the raw response.
  - Wired client codecs (br / gzip) produce compressed responses.

Server's currently wired codecs (see
`src/lib/nogc_async_mut/http_server/compression.spl::supported_encodings`)
are `["br", "gzip", "deflate", "zstd", "lz4"]`.

All payloads are built from module-level fns to dodge the
interpreter-mode `it`-block var-mutation footgun.

## Scenarios

### StaticFileHandler Accept-Encoding negotiation

#### client prefers zstd → server emits zstd Content-Encoding

- var cache = StaticCompressionCache new
   - Expected: resp.status equals `200`
   - Expected: _content_encoding_of(resp.headers) equals `zstd`
   - Expected: _has_vary_accept_encoding(resp.headers) is true
   - Expected: resp.body_bytes.len() > 0 is true
   - Expected: resp.body equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# zstd is in supported_encodings() and the codec is wired.
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/index.html", "zstd"
)
expect(resp.status).to_equal(200)
expect(_content_encoding_of(resp.headers)).to_equal("zstd")
expect(_has_vary_accept_encoding(resp.headers)).to_equal(true)
expect(resp.body_bytes.len() > 0).to_equal(true)
expect(resp.body).to_equal("")
```

</details>

#### client prefers br only → server emits br Content-Encoding

- var cache = StaticCompressionCache new
   - Expected: resp.status equals `200`
   - Expected: _content_encoding_of(resp.headers) equals `br`
   - Expected: resp.body equals ``
   - Expected: resp.body_bytes.len() > 0 is true
   - Expected: cache.entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/page.html", "br"
)
expect(resp.status).to_equal(200)
expect(_content_encoding_of(resp.headers)).to_equal("br")
expect(resp.body).to_equal("")
expect(resp.body_bytes.len() > 0).to_equal(true)
expect(cache.entries.len()).to_equal(1)
```

</details>

#### Accept-Encoding: identity only → raw response, cache untouched

- var cache = StaticCompressionCache new
   - Expected: resp.status equals `200`
   - Expected: _content_encoding_of(resp.headers) equals ``
   - Expected: resp.body equals `body`
   - Expected: resp.body_bytes.len() equals `0`
   - Expected: cache.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/about.html", "identity"
)
expect(resp.status).to_equal(200)
expect(_content_encoding_of(resp.headers)).to_equal("")
expect(resp.body).to_equal(body)
expect(resp.body_bytes.len()).to_equal(0)
expect(cache.entries.len()).to_equal(0)
```

</details>

#### client lists gzip+br only → server preference picks br

- var cache = StaticCompressionCache new
   - Expected: resp.status equals `200`
   - Expected: _content_encoding_of(resp.headers) equals `br`
   - Expected: resp.body_bytes.len() > 0 is true
   - Expected: cache.entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/foo.html", "gzip, br"
)
expect(resp.status).to_equal(200)
expect(_content_encoding_of(resp.headers)).to_equal("br")
expect(resp.body_bytes.len() > 0).to_equal(true)
expect(cache.entries.len()).to_equal(1)
```

</details>

#### Accept-Encoding: zstd;q=0 forbids zstd → identity served

- var cache = StaticCompressionCache new
   - Expected: resp.status equals `200`
   - Expected: _content_encoding_of(resp.headers) equals ``
   - Expected: resp.body equals `body`
   - Expected: resp.body_bytes.len() equals `0`
   - Expected: cache.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# q=0 explicitly bans the coding. Even though zstd IS supported,
# the client has rejected it. With no other codec offered, the
# server falls through to identity.
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/q0.html", "zstd;q=0"
)
expect(resp.status).to_equal(200)
expect(_content_encoding_of(resp.headers)).to_equal("")
expect(resp.body).to_equal(body)
expect(resp.body_bytes.len()).to_equal(0)
expect(cache.entries.len()).to_equal(0)
```

</details>

#### Accept-Encoding: zstd, lz4 → server preference picks zstd first

- var cache = StaticCompressionCache new
   - Expected: resp.status equals `200`
   - Expected: _content_encoding_of(resp.headers) equals `zstd`
   - Expected: resp.body_bytes.len() > 0 is true
   - Expected: cache.entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both codecs supported, both at default q=1. negotiate_encoding
# ties on q and breaks ties by `supported_encodings()` order,
# which lists zstd before lz4.
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/multi.html", "zstd, lz4"
)
expect(resp.status).to_equal(200)
expect(_content_encoding_of(resp.headers)).to_equal("zstd")
expect(resp.body_bytes.len() > 0).to_equal(true)
expect(cache.entries.len()).to_equal(1)
```

</details>

#### client demotes zstd via q=0.1 but lz4 at q=1 → lz4 wins

- var cache = StaticCompressionCache new
   - Expected: resp.status equals `200`
   - Expected: _content_encoding_of(resp.headers) equals `lz4`
   - Expected: resp.body_bytes.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# zstd is otherwise server-preferred, but the client has lowered
# its quality to 0.1 while lz4 stays at q=1 → lz4 wins on q.
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/demote.html", "zstd;q=0.1, lz4;q=1.0"
)
expect(resp.status).to_equal(200)
expect(_content_encoding_of(resp.headers)).to_equal("lz4")
expect(resp.body_bytes.len() > 0).to_equal(true)
```

</details>

#### Accept-Encoding: * → first supported codec is chosen

- var cache = StaticCompressionCache new
   - Expected: resp.status equals `200`
   - Expected: _content_encoding_of(resp.headers) equals `br`
   - Expected: resp.body_bytes.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `*` matches any codec at q=1; server preference order picks br.
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val resp = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/star.html", "*"
)
expect(resp.status).to_equal(200)
expect(_content_encoding_of(resp.headers)).to_equal("br")
expect(resp.body_bytes.len() > 0).to_equal(true)
```

</details>

#### cache miss compresses+stores; second hit serves identical bytes

- var cache = StaticCompressionCache new
   - Expected: first.body_bytes.len() > 0 is true
   - Expected: cache.entries.len() equals `1`
   - Expected: second.status equals `200`
   - Expected: _content_encoding_of(second.headers) equals `zstd`
   - Expected: second.body_bytes.len() equals `first_len`
   - Expected: cache.entries.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# End-to-end (path,encoding) keyed cache check on the negotiation
# path — distinct from the existing spec because we route through
# a multi-codec Accept-Encoding header, not a single-codec one.
var cache = StaticCompressionCache.new(8, 1048576)
val body = _make_text_payload()
val first = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/cached.html", "zstd, lz4"
)
expect(first.body_bytes.len() > 0).to_equal(true)
val first_len = first.body_bytes.len()
expect(cache.entries.len()).to_equal(1)
val second = cache.serve_compressed_or_plain(
    body, "text/html; charset=utf-8", "/cached.html", "zstd, lz4"
)
expect(second.status).to_equal(200)
expect(_content_encoding_of(second.headers)).to_equal("zstd")
expect(second.body_bytes.len()).to_equal(first_len)
# Entry count unchanged → served from cache, not recompressed.
expect(cache.entries.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
