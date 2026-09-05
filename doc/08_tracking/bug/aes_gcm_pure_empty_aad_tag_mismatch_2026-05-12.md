# AES-GCM Pure Empty-AAD Tag Mismatch

Date: 2026-05-12
Status: Resolved 2026-05-13

`test/01_unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl` was a known blocker for the cipher/compression algorithm gate. The failure presented as a wrong tag for the AES-256-GCM CAVS V3 vector with empty AAD and 16-byte plaintext.

Resolution: the V3 fixture key bytes did not match the documented CAVS key suffix. The helper encoded `66 66 b8 f2`; the documented vector requires `66 6b 8f 22`.

Verification: `src/compiler_rust/target/release/simple test test/01_unit/lib/crypto/aes_gcm_rfc_vectors_spec.spl --mode=interpreter --no-cache` passes 11 examples, 0 failures. The strict core cipher/compression gate reports `passed=13 skipped=0 failed=0`.
