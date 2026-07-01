# Bug: `std.crypto` SHA-512 common digest aborts under the spec harness

- **Slug:** `std_crypto_sha512_common_digest_aborts_in_harness`
- **Date:** 2026-06-15
- **Severity:** P2 (SHA-512 unusable from the canonical common-digest entry path in tests)
- **Area:** `src/lib/common/crypto/sha512.spl` + spec harness interaction
- **Status:** OPEN (needs minimal-repro narrowing)

## Symptom
Driving SHA-512 through the common digest entry point inside an sspec `it`
block aborts the harness rather than returning a digest (observed during the
2026-06-15 crypto-algorithm audit). SHA-256 through the equivalent path is
fine; the abort is specific to the SHA-512 path. Source `sha512.spl` is
present (so this is not a missing-source case like base32).

## Why it matters
SHA-512 (and SHA-384, which shares the 64-bit core) underpins HKDF-SHA512,
JWT ES512/HS512, and TLS 1.3 cipher suites using SHA-384. If the common-digest
entry aborts under the harness, none of those can be verified against
NIST known-answer vectors via specs.

## Next step (to make this actionable)
Narrow to a minimal `bin/simple run` repro: call the SHA-512 common-digest
entry on a fixed input (e.g. empty string → expected
`cf83e1357eefb8bd...a538327af927da3e`) both at top level and inside an
`it`-block, and capture the abort site. Likely related to the 64-bit-word
arithmetic path or a cross-module/return-frame interaction (cf. the
`interp_text_bytes_corrupts_across_frame` finding). File the narrowed repro
here when isolated.
