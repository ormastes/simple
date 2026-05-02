# FR: Native PBKDF2-HMAC-SHA-256/512 runtime helpers

- **Date filed:** 2026-05-01
- **Status:** Open (FR — not yet scheduled)
- **Cross-ref:** `doc/08_tracking/bug/pbkdf2_interpreter_perf_2026-05-01.md` (Partially Fixed)
- **Cross-ref:** `.claude/memory/feedback_interpreter_bulk_buffer.md` (B2 family — extern-backed crypto helpers)

## Summary

Add interpreter-side runtime helpers for PBKDF2-HMAC-SHA-256 and
PBKDF2-HMAC-SHA-512 so that crypto unit tests can exercise the standard
RFC iteration counts (4096, 80000, …) under the test-runner's 60 s
wall-clock watchdog without relying on compiled-mode artifacts.

## Why pure-Simple optimisation is not sufficient

`src/lib/common/crypto/pbkdf2.spl` was optimised on 2026-05-01 with two
layered improvements (commits in this branch):

1. Cache K_ipad / K_opad prefix SHA-256 states across all PBKDF2
   iterations (1 SHA-256 first-block compute per HMAC call → 0).
2. Pre-build the deterministic 96-byte HMAC tail block template once;
   per-iteration just patches the 32 leading payload bytes via
   in-place `[i] = …` index assignment, eliminating ~190 list pushes
   per HMAC call.

Net effect: PBKDF2-HMAC-SHA-256 c=4096 in interpreter mode dropped
from ≈180 s to ≈78 s — a 2.3× speedup, but still ≈30% over the
60 s test-runner watchdog. The remaining cost is dominated by
`sha256_process_block` (64-round main loop with ≈15 function calls
per round). Inlining further would require duplicating SHA-256 round
logic into pbkdf2.spl, which we explicitly want to avoid.

## Proposed externs

Two new interpreter externs, alongside the existing `rt_bytes_alloc`
family in `src/compiler_rust/compiler/src/interpreter_extern/`:

```
extern fn rt_pbkdf2_hmac_sha256(password: [u8], salt: [u8],
                                 iterations: i64, key_length: i64) -> [u8]
extern fn rt_pbkdf2_hmac_sha512(password: [u8], salt: [u8],
                                 iterations: i64, key_length: i64) -> [u8]
```

Both delegate to the existing Rust `sha2` / vendored `pbkdf2` crate
already pulled in by other interpreter helpers (`signatures.rs`),
returning a freshly-allocated `[u8]` of length `key_length`.

`pbkdf2.spl` would call these via a feature-detected fast path,
falling back to the pure-Simple impl when the extern is unavailable
(e.g. early bootstrap stages, baremetal targets).

## Acceptance

- AC-1: PBKDF2-HMAC-SHA-256 c=4096, key_length=32: ≤ 1 s wall-clock
  in interpreter mode (currently 78 s).
- AC-2: PBKDF2-HMAC-SHA-512 c=80000, key_length=64: ≤ 1 s wall-clock
  in interpreter mode (currently >5 min, never observed within
  watchdog).
- AC-3: Pure-Simple fallback path remains functional for environments
  without the extern.
- AC-4: TC3, TC5, TC6 (SHA-256) and TC2 (SHA-512) of
  `draft-josefsson-pbkdf2-test-vectors-00` re-enabled in
  `test/unit/lib/crypto/pbkdf2_industry_vectors_spec.spl`.

## Why this is in a separate FR (not the 2026-05-01 perf bug)

Per `feedback_extern_bootstrap_rebuild.md`: extern additions require a
full bootstrap rebuild (`scripts/bootstrap/bootstrap-from-scratch.sh
--deploy`), and another agent on this date is already doing one. To
avoid colliding with that, the 2026-05-01 fix lands as a
*pure-Simple-only* perf improvement and the extern path is queued for
the next bootstrap cycle.
