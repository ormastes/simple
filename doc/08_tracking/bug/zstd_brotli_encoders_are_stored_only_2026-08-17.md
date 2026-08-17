# zstd and brotli encoders are container writers only — they never compress

**Found:** 2026-08-17, lane W11-B of `.spipe/simple_enterprise_suite`, while
determining whether `test/01_unit/lib/nogc_async_mut/http_server/compression_spec.spl`
or `src/lib/nogc_async_mut/http_server/compression.spl` was wrong.

## Symptom

Measured directly, on 300 bytes of highly repetitive ASCII (`"abcdefghij"` x 30),
via the response-compression dispatcher's own entry point:

| codec | output bytes | round-trips via `decompress_bytes` auto-detect |
|-------|--------------|-----------------------------------------------|
| br      | **304** (larger than input) | no |
| gzip    | 42  | yes |
| deflate | 28  | no (raw deflate has no magic; auto-detect limitation, not a codec fault) |
| zstd    | **310** (larger than input) | yes |
| lz4     | 36  | yes |

## Cause

`src/lib/common/compress/zstd.spl` `zstd_compress_frame` is documented in its own
body as emitting "RLE block if all bytes are identical, raw block otherwise" —
it writes a valid zstd *container* around the untouched input. It therefore
always expands by the frame-header overhead. `brotli_compress` behaves the same
way in practice (300 -> 304). Both decoders are real; only the encoders are stubs.

This is a real capability gap, not a spec problem. It is recorded here rather
than absorbed into a spec expectation, per `.claude/rules/code-style.md`.

## Consequence that WAS a live defect (fixed 2026-08-17)

`compress_response_for` negotiated exactly one codec — the highest
server-preference codec the client accepted — and, when the size guard
correctly refused its non-shrinking output, returned the response uncompressed
with no attempt at the next acceptable codec. A client sending
`Accept-Encoding: zstd, lz4` therefore received a **fully uncompressed** 300-byte
body, even though it also offered lz4, which compresses the same body to 36
bytes. Fixed by walking the server preference order and taking the first
mutually-acceptable codec that actually shrinks the body; preference order is
otherwise unchanged (`Accept-Encoding: gzip, lz4` still selects gzip).

## Triage 2026-08-17 — encoders DEFERRED, no live defect remains

Re-verified 2026-08-17: `compression_spec.spl` is green (20/20) including the
multi-codec fallback fixed above, so nothing user-visible is broken — the
dispatcher never serves a non-shrinking zstd/br body. Implementing real
encoders means FSE + Huffman entropy coding (zstd, RFC 8878 §4) and brotli's
static-dictionary/context modeling (RFC 7932) — a multi-week feature, not a
bug fix, and no C-runtime `libzstd`/`libbrotli` binding exists in-tree to
shortcut it. Deferred as a capability gap; the items below remain the frontier.

## Still open

- `zstd_compress_frame` performs no actual compression.
- `brotli_compress` performs no actual compression.
- `decompress_bytes(_, nil)` auto-detect cannot recognise a raw deflate stream
  (no magic bytes). Callers must pass the codec hint for deflate.

Until the encoders are implemented, `supported_encodings()` legitimately lists
zstd and br — the dispatcher will simply never select them for a body they
cannot shrink.
