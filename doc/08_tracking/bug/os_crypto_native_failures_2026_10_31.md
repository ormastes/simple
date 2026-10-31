# os.crypto native failures on the pinned Phase 2 producer

**Status:** Open (not verified on a rebuilt compiler)
**Severity:** P1
**Date:** 2026-10-31

## Symptom

On the pinned Phase 2 producer (13d73267...), `test/fixtures/devhub/native_os_crypto_kat` failed in several ways:

- AES-128 GCM: test case TC2 and TC4 produced wrong ciphertext and wrong tags. Decrypts with the correct tag were rejected.
- X25519: RFC 7748 test vectors TV1 and TV2 returned all zeros.
- The binary then exited with code 139 (segmentation fault).
- AES-256 GCM did not link: `rt_tls13_aes256_gcm_encrypt` and `rt_tls13_aes256_gcm_decrypt` have no native implementation (`lld-link: undefined symbol`).

## Evidence

- These modules pass on the Phase 1 seed.
- The Messenger read path uses `src/lib/common/crypto/aes_gcm.spl` instead, and that module passes native vectors.
- Suspected cause, not proven: the old producer's `.to_i64()` defect. See `native_to_i64_compound_receiver_2026_10_31.md`.

## Unverified

- Whether the failures reproduce on a rebuilt compiler. Re-test first on a rebuilt compiler.
- Whether the `.to_i64()` defect is the cause of the wrong AES and X25519 results.
- Whether the segmentation fault (exit 139) has the same cause as the wrong results.
