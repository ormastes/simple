## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: Resolved 2026-05-13

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# AES-GCM Pure Empty-AAD Tag Mismatch

Date: 2026-05-12
Status: Resolved 2026-05-13

`test/01_unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl` was a known blocker for the cipher/compression algorithm gate. The failure presented as a wrong tag for the AES-256-GCM CAVS V3 vector with empty AAD and 16-byte plaintext.

Resolution: the V3 fixture key bytes did not match the documented CAVS key suffix. The helper encoded `66 66 b8 f2`; the documented vector requires `66 6b 8f 22`.

Verification: `src/compiler_rust/target/release/simple test test/01_unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl --mode=interpreter --no-cache` passes 11 examples, 0 failures. The strict core cipher/compression gate reports `passed=13 skipped=0 failed=0`.
