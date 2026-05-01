# Feature Request: Wire StaticCompressionCache into StaticFileHandler.handle()

**Date:** 2026-05-01
**Status:** Pending — cache class shipped, integration deferred.

## What was done

`StaticCompressionCache` and `CacheEntry` were added to
`src/lib/nogc_async_mut/http_server/static_file.spl` with full LRU
eviction (entry-count bound + total-byte bound) and 8 passing unit specs in
`test/unit/lib/nogc_async_mut/http_server/static_compression_cache_spec.spl`.

## What is deferred

Wiring the cache into `StaticFileHandler.handle()` so that repeat requests
for compressible small files hit the cache rather than re-compressing on every
call.

## Why deferred

The integration requires:

1. **New field on `StaticFileHandler`** — `cache: StaticCompressionCache`.
   This changes every call-site that constructs `StaticFileHandler(root: ...,
   index_file: ...)` or calls `StaticFileHandler.new(root, index_file)`.

2. **Read `Accept-Encoding`** from `HttpRequestData` inside `handle()`.
   The current signature passes `request: HttpRequestData` but never inspects
   its headers for compression negotiation.

3. **Text→bytes conversion** for the small-file branch (currently reads
   `rt_file_read_text` → `text`; compression needs `[u8]`). Needs
   `rt_text_to_bytes` (already present in `compression.spl` as an `extern`).

4. **sendfile branch (> 64 KiB) cannot be cached** —
   `_is_compression_eligible` in `compression.spl` rejects `body_file != ""`
   responses. The cache only helps the `size <= 65536` branch.

5. **MIME eligibility check** — only `text/html`, `text/css`,
   `application/javascript`, `application/json`, `application/xml`,
   `image/svg+xml`, `text/plain`, `text/xml`, `text/csv` are candidates;
   the mime-set guard needs to be added before checking the cache.

## Suggested implementation steps

1. Add `rt_text_to_bytes` `extern` import to `static_file.spl` (already in
   `compression.spl` — safe to repeat in this module).
2. Add `cache: StaticCompressionCache` field to `StaticFileHandler`; update
   `StaticFileHandler.new()` to accept optional cache params or default them.
3. In the `size <= 65536` branch of `handle()`:
   - Resolve `Accept-Encoding` header from `request.headers`.
   - Negotiate with `supported_encodings()` from `compression.spl`.
   - If chosen encoding != "" and MIME is compression-eligible:
     - `cache.get(actual_path, chosen)` → hit: build bytes response with
       `Content-Encoding` header.
     - miss: call `compress_response_body(rt_text_to_bytes(content), chosen)`;
       on `Ok`, `cache.put(actual_path, chosen, compressed)` and build bytes
       response; on `Err`, fall through to plain `build_html_or_typed`.
4. Update all callers of `StaticFileHandler.new` / direct construction.
5. Add integration spec covering cache-hit path (mock or real file on disk).
