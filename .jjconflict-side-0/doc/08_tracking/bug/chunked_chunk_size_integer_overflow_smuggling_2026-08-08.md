# Chunked chunk-size integer overflow accepted as last-chunk (request smuggling)

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** High (protocol parsing on untrusted input; smuggling primitive)
- **Found by:** adversarial review of `df13e306e9f` (boundary-aware chunked body-end detection)
- **Sites:** 4 (all tiers)

## Defect

RFC 7230 §4.1 requires a `chunk-size` that does not fit the recipient's integer
type to be **rejected**. Every chunked size parser in the tree accumulated
`acc * 16 + digit` with no overflow check, so a 17-hex-digit size wraps modulo
2^64:

| chunk-size token      | value read back | effect                     |
|-----------------------|-----------------|----------------------------|
| `10000000000000000`   | **0**           | accepted as the LAST-CHUNK |
| `10000000000000005`   | **5**           | declares a 5-byte chunk    |

`header_is_hex_digits` accepted the token (it *is* 1*HEXDIG), so the size passed
validation and then silently wrapped.

## Measured before the fix

```
chunked_body_end("10000000000000000\r\nX\r\n\r\n")                    -> 24   (complete)
async_proxy_chunked_body_complete("10000000000000000\r\nX\r\n\r\n")   -> true
```

Both said "message ends here". A peer (front-end proxy, upstream origin) that
correctly rejects the overflow disagrees about the message boundary, so the
bytes after the fake last-chunk are read by one party as body and by the other
as the start of a new request — an HTTP request-smuggling primitive. It applies
to the server parser (`HttpRequestParser`) **and** to the async proxy, which is
the worse of the two: a proxy is exactly the desync point smuggling needs.

## Not a hang

Adversarial probes for a non-terminating walk were run and did **not** reproduce
one: `FFFFFFFFFFFFFFFF` (-1) and `FFFFFFFFFFFFFFFE` (-2) both return `-2`
(framing error) via the chunk-data CRLF check, and a crafted backwards-`pos`
buffer terminated. The overflow is a *misframing* defect, not a DoS.

## Family (the original commit under-enumerated it)

`df13e306e9f` claimed "Family enumerated across all tiers: these were the only
two sites — other tiers have no chunked body-end detector." True for *body-end
detectors*, but two further **chunked decoders** carry the identical hole:

| file | function | hex parser |
|------|----------|-----------|
| `src/lib/nogc_async_mut/http/headers.spl` | `chunked_body_end`, `decode_chunked` | `parse_hex_text` |
| `src/lib/nogc_async_mut/http_server/proxy.spl` | `async_proxy_parse_chunk_size` | inline |
| `src/lib/nogc_sync_mut/http/headers.spl` | `decode_chunked` | `parse_hex_text` |
| `src/lib/nogc_sync_mut/http/http1.spl` | `decode_chunked_with_trailers` | `http1_parse_hex` |

## Fix

A `*_hex_fits_i64(token)` guard at each site: strip leading zeros, reject a
remainder wider than 15 hex digits (max `0xFFFFFFFFFFFFFFF` ~= 1.15e18, ~1 EB —
far past any real chunk, and the widest token that cannot overflow i64).
`chunked_body_end` returns `-2` (framing error); the decoders return `Err`.

## Coverage the original spec lacked

`test/01_unit/lib/http_server/chunked_body_boundary_spec.spl` ships 14 examples
but **zero** hostile ones: no overflow size, no huge size, no trailer confusion,
no backwards-progress case — happy path plus the embedded-terminator case it was
written for. Regression coverage added:

- `test/01_unit/lib/http_server/chunked_size_overflow_spec.spl` (10 examples)
- `test/01_unit/lib/http/chunked_size_overflow_sync_spec.spl` (7 examples)

Both include negative controls (normal stream, leading-zero-padded size, widest
non-overflowing size). Sabotage (widening the guard to 64 digits) takes them
5-red and 4-red respectively.

## Engine caveat

All verdicts were produced on the interpreter path via `bin/simple test`, and
`bin/simple` is currently the Rust bootstrap seed. GREEN here does not prove
self-hosted or native-codegen behavior.
