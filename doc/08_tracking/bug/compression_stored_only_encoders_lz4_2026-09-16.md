# Compression encoders are stored-only: even lz4 never shrinks repetitive input

Date: 2026-09-16
Status: OPEN
Related: doc/08_tracking/bug/zstd_brotli_encoders_are_stored_only_2026-08-17.md

## Observed

`http_server/compression_spec.spl` — 4 examples still red after the
wired-container-writer rename: every "compresses" example (gzip, br, deflate,
lz4) receives `is_ok() == true` but the compressed output is never smaller
than the ~300-byte highly repetitive input. The lib's own comment claims
300 bytes compress to 36; measured: no shrink for ANY encoder, including lz4,
which the 2026-08-17 record (zstd/brotli) did not cover.

## Impact

`Content-Encoding` negotiation advertises 5 encodings (br, gzip, deflate,
zstd, lz4) that all ship stored-only payloads — negative-value compression
for clients.

## Expectation

At least the dictionary/fallback encoders shrink repetitive input (lz4 literal
run encoding alone should collapse 300 repeated bytes far below 300).

## Unblock condition

Implement real entropy/back-reference coding for the container writers (or
stop advertising the encodings). Re-run
`test/01_unit/lib/nogc_async_mut/http_server/compression_spec.spl` — the four
examples are deliberately left RED.
