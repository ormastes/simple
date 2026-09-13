# Bug: `std.crypto` SHA-512 common digest aborts under the spec harness

## Closed 2026-09-13 — FIXED in `src/lib/common/crypto/sha512.spl` (index-assign on the input array)

### Regression specs (added 2026-09-13)

- `test/01_unit/lib/common/crypto/sha512_nonempty_input_spec.spl` —
  reproducing + generalization, 7/7 green (FIPS 180-4 vectors for
  SHA-512/384/512-256, multi-block input, input non-mutation, determinism).
- **Limitation, stated rather than implied:** a true A/B against the pre-fix
  source was NOT possible — the concurrent bootstrap holds `src/lib` read-only
  and the revert failed with "Permission denied". The buggy pattern in
  isolation also does not abort on this host's run lane. So this spec proves
  the current code correct; it does not prove it fails pre-fix. Re-run the A/B
  when no bootstrap is holding `src/lib`.
- **measured** — root cause: `_sha512_core` did `var padded = data` then
  `padded[pi] = padded[pi] & 255`, which fails at runtime with
  `semantic: invalid assignment: cannot index assign value of type array`. That loop only
  executes when `data_len > 0`, which is exactly why `sha512("")` passed and
  `sha512("abc")` did not.
- **measured** — fix applied: copy into a fresh `var padded: [i64] = []` via
  `padded.push(data[pi] & 255)` (this also stops mutating the caller's array). After the
  fix `sha512_bytes([97,98,99])` returns 64 bytes starting `221, 175` = `0xdd 0xaf`
  (correct `ddaf35a1…`); `sha512_bytes([])` starts `207` = `0xcf` (`cf83e135…`).
- **measured** — `sha512_verify_spec.spl` still shows 2 failures, but the reason changed to
  `stack overflow: recursion depth 1000 exceeded in function 'bytes_to_hex'`, driven by the
  spec's own imports (the run warns `'text_to_bytes' is named in use std.crypto.types.{...}
  but module … does not provide it`). That is the separate
  `crypto_types_text_to_bytes_collides_with_base_encoding_2026-08-21` defect, not SHA-512.
- **measured** — consumer regression check: `bin/simple run
  test/01_unit/lib/common/crypto/hkdf_sha512_256_spec.spl` is
  `outcome=OK declared>=10 executed=10 passed=10 failed=0` after the fix.
- **measured** — NEW, SEPARATE defect found while verifying and NOT closed here: the same
  `sha512_bytes([97,98,99])` returns the correct `0xdd 0xaf …` under the spec harness
  (interpreter) but `d[0] = 145` (`0x91`) when the same file is run standalone through
  `bin/simple run`'s JIT, and `sha384_bytes` likewise gives `86` (`0x56`) instead of
  `0xcb`. So the harness/abort bug this entry tracks is fixed, but SHA-512 is still wrong
  on the JIT path. That belongs in a new bug against JIT codegen, not in this entry.
- **inferred** — binary used: Rust seed `bin/simple` v1.0.0-rc.1 on Windows, not the
  self-hosted compiler.

- **Slug:** `std_crypto_sha512_common_digest_aborts_in_harness`
- **Date:** 2026-06-15
- **Severity:** P2 (SHA-512 unusable from the canonical common-digest entry path in tests)
- **Area:** `src/lib/common/crypto/sha512.spl` + spec harness interaction
- **Status:** CLOSED 2026-09-13 (triage shard 03) — see the Closed section below

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
