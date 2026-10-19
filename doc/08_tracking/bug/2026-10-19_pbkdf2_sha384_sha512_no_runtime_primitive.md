# PBKDF2-HMAC-SHA-384/512 has no runtime fast path

- Date: 2026-10-19
- Status: open
- Spec: test/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.spl (SHA-384 c=4096, SHA-512 c=80000) stays red; not skipped.
- Cause: the only runtime hash extern is `rt_tls13_sha256` (SHA-256). No SHA-384/512 or HMAC extern exists, so these variants run pure Simple in the interpreter (~9.5 ms per HMAC; 160k HMACs for c=80000 cannot fit the 900 s budget).
- Done: PBKDF2-HMAC-SHA-256 now uses a fast path over `rt_tls13_sha256` (`pbkdf2_sha256_fast_spec`).
- Needed: a runtime SHA-384/512 primitive backed in Simple/the embedded runtime, then the same HMAC-on-hash construction in `src/lib/common/crypto/pbkdf2.spl`. Owner decision (no new C symbol was added).
