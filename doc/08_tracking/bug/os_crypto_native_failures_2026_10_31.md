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

## 2026-11-05 verification attempt (lane libbug-linux-oscrypto-20261105, aarch64 Linux)

Fixture: `test/fixtures/devhub/native_os_crypto_kat/main.spl` (added on branch
`work/libbug-linux-oscrypto-20261105`; it did not exist in any commit before).
Known-answer vectors only: NIST SP 800-38D Appendix B TC1-TC4 (AES-128-GCM) and
TC13-TC16 (AES-256-GCM); RFC 7748 §5.2 TV1/TV2 and §6.1 Alice/Bob ECDH (X25519).
RFC 7748 TV1/TV2 and the ECDH shared secret were re-verified against the Python
`cryptography` library before embedding (TV2 u-coordinate/output corrected to
the published RFC values `e5210f12...715a493` / `95cbde94...ac7957`). `bin/simple`
does not exist on this host; the Rust seed
(`src/compiler_rust/target/bootstrap/simple`) and the Phase 1 full CLI
(`build/phase_snapshots/phase1_1793422538/simple`) were substituted.

Interpreter evidence (seed binary, `run --source src/os --source src/lib`):
all 20 checks PASS, `KAT FAILURES 0`, exit 0. Covers AES-128-GCM TC1-TC4
(encrypt ct+tag, decrypt-ok, corrupt-tag-rejected on TC2), AES-256-GCM
TC13-TC16 (same shape; confirms the pure-Simple delegation links and computes),
and X25519 TV1, TV2, Alice public key, and the ECDH shared secret — i.e. the
os.crypto modules produce the published vectors under the seed interpreter.

Native evidence: NOT OBTAINED — build budget exhausted. Two native-build
attempts on this loaded host (load avg ~7, other lanes building concurrently)
both ran >60 min in single-threaded codegen without reaching the link stage and
without emitting the output binary:
1. Seed compiler `native-build --source src/os --source src/lib --entry .../main.spl`
   — killed at its 60-minute task limit; log `build/test_tmp/native_build.log`.
2. Phase 1 CLI `native-build --source src/os --source src/lib --entry-closure
   --entry .../main.spl --threads 6 --cache-dir build/test_tmp/cache`
   — killed at 60:37 elapsed for the same reason; log
   `build/test_tmp/native_build_p1.log`. (`--threads 6` did not parallelize the
   observed phase; process stayed at ~1 core, RSS ~1.4 GB.)

Residuals / next steps: the AES-256-GCM link fix in `src/os/crypto/aes256_gcm.spl`
is interpreter-verified here (12/12 and 2/2 in the cited specs, plus the new
fixture's TC13-TC16 passing under the seed), and that module no longer declares
or calls `rt_tls13_aes256_gcm_*` (only a comment mentions the old extern).
Caveat found during this pass: `src/os/apps/sshd/ssh_cipher_live.spl:8-10,150,235`
still declares and calls `rt_tls13_aes256_gcm_*` externs, so any native closure
that includes the sshd live cipher would hit the same `lld-link: undefined
symbol` failure the fixed module avoided; it should be routed to
`std.common.crypto.aes_gcm` the same way. (`rt_tls13_aes128_gcm_*` externs also
remain in `src/lib/nogc_async_mut_noalloc/tls/aes128_gcm.spl`,
`src/lib/nogc_sync_mut/sffi/host.spl`, and `src/os/tls13/record13.spl`; whether
those link depends on the runtime those modules target.)
Native confirmation of AES-128-GCM TC2/TC4, X25519 TV1/TV2, and the AES-256
link on a native producer still requires a finished native-build of the
fixture; rerun on a less contended host or with a cached/warm native cache.
