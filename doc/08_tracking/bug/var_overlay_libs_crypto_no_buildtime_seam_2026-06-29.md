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
