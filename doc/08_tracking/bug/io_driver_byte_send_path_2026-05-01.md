# Feature: io driver needs `submit_send_bytes(fd, data: [u8])`

- **Date:** 2026-05-01
- **Status:** Proposed
- **Module:** `src/lib/nogc_async_mut/io/driver.spl` + io backends
- **Driver:** Phase 1C of the HTTPS/HTTP2 compression+cipher pass

## Background

Phase 1C of the compression pass shipped:

- `HttpResponseData.body_bytes: [u8]` field (already in HEAD).
- `serialize_response_bytes(resp) -> [u8]` (already in HEAD).
- `Connection.set_response_bytes` / `get_response_bytes_buf` (already in HEAD).
- `compress_response_for(resp, accept_header) -> HttpResponseData` (`cd7c8688`,
  this pass).

All the response-side scaffolding is in place. The remaining gap is the
**socket write path**: the io driver only exposes
`fn submit_send(fd: i64, data: text) -> i64` — there is no byte-array variant.

## Why text won't work

Compressed response bodies contain arbitrary bytes including:

- `0x00` (NUL — terminates many text representations)
- High-bit bytes that are not valid UTF-8 leading bytes
- Sequences that are valid UTF-8 leading bytes followed by invalid continuations

Round-tripping `[u8] → text → [u8]` for arbitrary bytes is not safe in Simple's
text representation; depending on the runtime, it may either drop bytes,
substitute U+FFFD replacements, or panic. Even the cases that "work" are not
byte-identical, which means the wire would carry the wrong compressed payload
and the client would fail decompression.

## Proposed fix

Add a sibling method to `IoDriver`:

```simple
fn submit_send_bytes(fd: i64, data: [u8]) -> i64:
    rt_io_tcp_submit_send_bytes(fd, data)
```

Plus a runtime extern at `src/compiler_rust/runtime/src/value/ffi/` that
calls `send(2)` with the raw bytes (or the io_uring `IORING_OP_SEND`
equivalent on Linux). The existing `submit_send` can stay as a convenience
wrapper that converts text to bytes via `rt_text_to_bytes` and calls the
new path.

Once this lands, the worker `send_response` flow becomes:

```simple
val accept = _accept_encoding(conn.request)
response = compress_response_for(response, accept)
if response.body_bytes.len() > 0:
    c.set_response_bytes(response, keepalive_s)
    self.connections[fd] = c
    val buf = c.get_response_bytes_buf()
    val op = self.driver.submit_send_bytes(fd, buf)
    ...
else:
    c.set_response(response, keepalive_s)
    self.connections[fd] = c
    val bytes = c.get_response_bytes()
    val op = self.driver.submit_send(fd, bytes)
    ...
```

## Workaround until landed

`compress_response_for` is fully implemented and unit-tested (19/19 specs in
`test/unit/lib/nogc_async_mut/http_server/compression_spec.spl`). The worker
does not call it yet; the server emits identity bodies regardless of
`Accept-Encoding`. This is honest: emitting `Content-Encoding: zstd` without
the actual zstd bytes (because they were corrupted by text conversion) would
be worse than emitting nothing.

The Phase 1B response dispatcher and Phase 1C response decision are
test-callable directly (round-trip via `decompress_bytes` confirmed); only
the worker-to-socket path is missing.

## Cross-references

- Plan: `/home/ormastes/.claude/plans/see-next-and-impl-ethereal-scott.md` Phase 1
- Helper: `src/lib/nogc_async_mut/http_server/compression.spl::compress_response_for`
- Connection wrapper: `src/lib/nogc_async_mut/http_server/connection.spl`
  (already has `response_bytes_buf: [u8]`, `set_response_bytes`,
  `get_response_bytes_buf`)
- Driver: `src/lib/nogc_async_mut/io/driver.spl` (currently text-only)
- Bug doc explicitly preferring zstd-only over half-broken gzip:
  `doc/08_tracking/bug/gzip_module_crc32_unresolved_2026-05-01.md`
