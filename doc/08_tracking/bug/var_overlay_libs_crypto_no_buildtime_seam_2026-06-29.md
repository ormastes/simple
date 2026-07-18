# Variant Overlay — libs/crypto constant_time: No Build-Time Seam

Date: 2026-06-29
Candidate: `variants/libs/crypto/` overlay keyed on `constant_time` backend (e.g. "pure" vs "openssl")

## Verdict: FAILS criterion (1) — no real alternative backend exists

### Evidence

File: `src/lib/common/crypto/constant_time.spl` (all 34 lines)

- The entire module is a pure-Simple XOR accumulator:
  `diff = diff | (ab[i] ^ bb[i])` (line 18) and `diff == 0` (line 20).
- Zero `extern fn`, zero `rt_*` call, zero SFFI binding, zero OpenSSL/mbedtls symbol.
- No second implementation anywhere in the tree: grep for
  `CRYPTO_memcmp`, `openssl`, `mbedtls`, `constant_time` across `.spl` returns
  only callers of this one module plus the module itself.

### Criterion check

| Criterion | Result |
|-----------|--------|
| (1) Real existing variation (refactor out branching) | FAIL — only one impl exists |
| (2) Build/deploy-target choice, not runtime-host | N/A (blocked by (1)) |

### Precondition to qualify later

A real `extern fn rt_crypto_memcmp(a: [i64], b: [i64], n: i64) -> i64` wired to
OpenSSL's `CRYPTO_memcmp` (or equivalent mbedtls / libsodium symbol) must exist
and be registered at all 6 rt_* sites. Only then is there a real alternative to
refactor out into `variants/libs/crypto/openssl/constant_time.spl` vs
`variants/libs/crypto/pure/constant_time.spl`.

## Other libs candidate considered AND REJECTED: compression codec

`std.common.compress.utilities` has a pure-Simple `match opts.codec:` over
lz4/zstd/gzip/brotli (all 0 extern) — real variation. But it FAILS criterion (2):
the codec is RUNTIME-parameterized, not a build-time choice.
- `default_compression_options(codec: CompressionCodec)` takes the codec as an
  ARGUMENT (utilities.spl:18); there is no implicit `DEFAULT_CODEC` / no-arg
  `compress()` to override at build time.
- The one place that "defaults" a codec —
  `src/lib/nogc_async_mut/http_server/compression.spl:263-265` — selects zstd vs
  lz4 from the client's `Accept-Encoding` at request time (runtime negotiation).
Baking one codec via a build-time variant would either break explicit-codec
callers or break content negotiation. No clean default-selection chokepoint to
extract (unlike ui.renderer's `renderer_priority_order()` or os
`target_lib_ext()`). NOT pursued.
