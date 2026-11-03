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

**Revalidated 2026-11-02: still plausible because Open (not verified on a rebuilt compiler); no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 blocker (lane p1blk)

Root cause of the AES-256 GCM link failure confirmed. `src/os/crypto/aes256_gcm.spl:22-23`
declares `extern fn rt_tls13_aes256_gcm_encrypt/decrypt`, and `:650` / `:689` call them
on the fast path. The only definitions are in the Rust seed runtime
(`src/compiler_rust/runtime/src/value/aes.rs:1099`, plus aes128 at `:801`). There is **no**
`rt_tls13_*` definition in the C runtime (`git grep rt_tls13_aes -- src/runtime` = 0 hits).
The Phase 2 lld-link uses the C runtime, so the symbol is undefined. Fix direction (owner
decision): route the native lane to the pure-Simple `src/lib/common/crypto/aes_gcm.spl`,
which is already native-verified, instead of the extern. Do not add a C AES. The AES-128 and
X25519 wrong-output and SIGSEGV parts still need a rebuilt-compiler rerun of
`test/fixtures/devhub/native_os_crypto_kat`.

## 2026-11-03 fix (AES-256 GCM link) — fix-implemented-verification-pending

`src/os/crypto/aes256_gcm.spl` no longer declares or calls `rt_tls13_aes256_gcm_*`.
`aes256_gcm_encrypt` and `aes256_gcm_decrypt` now delegate to the pure-Simple
`std.common.crypto.aes_gcm`. Interpreter evidence: `aes256_gcm_nist_vectors_spec.spl` passes 12/12, and
the new `test/01_unit/lib/crypto/aes256_gcm_no_seed_extern_spec.spl` passes 2/2. That spec fails on the
old source because the extern was present.

Native repro (pending a Phase 2 producer): native-build
`test/fixtures/devhub/native_os_crypto_kat/main.spl`, then confirm lld-link reports no
undefined `rt_tls13_aes256_gcm_*` and that the AES-256 vectors pass. The AES-128 GCM and X25519
wrong-output and SIGSEGV parts are not addressed by this change.
