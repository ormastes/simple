# AES-GCM encrypt reads past short key/nonce; canonical hardening still rewound

- **ID:** aes_gcm_encrypt_length_unchecked_and_rewound_hardening_2026-11-13
- **Severity:** P2 (fail-open crypto input handling)
- **Status:** open
- **Found by:** lane work/aesgcm-copies-20261113 (follow-up to PR #8878)
- **Related:** `aes128_gcm_verification_blocked_by_env_access_parse_2026-08-25.md`

## Summary

Decrypt now fails closed on wrong-length key, nonce and tag in every AES-GCM
copy under `src/os` plus the noalloc TLS copy. The NVFS copy got its full
hardening back from `db9fa3350a4`, encrypt included. The items below are still
open.

## Open

1. **Encrypt reads past a short key or nonce** in:
   - `src/os/crypto/aes128_gcm.spl`
   - `src/lib/nogc_async_mut_noalloc/tls/aes128_gcm.spl`
   - `src/os/crypto/aes256_gcm.spl`
   - `src/lib/common/crypto/aes_gcm.spl` (aes128/192/256)

   `rt_bytes_u8_at` reads an out-of-range index as 0, so a short key or nonce
   is silently zero-extended. The result is valid-looking ciphertext under a
   weak key or IV.

   - All four return bare `[u8]`. Changing them to a result type touches
     about 60 call sites in about 30 files (canonical callers
     `tls_common_hooks`, `record13`, `ssh_cipher_live`, `gmac`, the devhub KAT
     fixture, and the KAT specs).
   - `db9fa3350a4` solved this without a signature change by checking length
     and calling `panic` before the validated core. The NVFS copy has that
     again. The canonical copy lost it (item 2).
   - No spec pins the encrypt panic yet. The spec runner has no way to assert
     a panic, so the NVFS encrypt guard is restored but not pinned by a test.
2. **Canonical `src/os/crypto/aes128_gcm.spl` is still the rewound blob.**
   - `e274cd33719`, a stale-snapshot merge on 2026-08-27, reverted
     `db9fa3350a4` (2026-08-25) in both the canonical and the NVFS copy.
   - PR #8878 put back the decrypt guards only. The canonical copy is still
     missing the `@unsafe` annotations, the `_a128gcm_new_u8` owner and the
     encrypt guards.
   - `sh scripts/audit/aes128-gcm-sffi-authority.shs` fails at its second
     line, which expects 15 `@unsafe` annotations in canonical and finds 1. The
     NVFS half of the audit passes.
3. **`std.common.crypto.aes_gcm` has no length checks in decrypt** for
   aes128/192/256.
   - Direct callers: `typed/aead`, `quic_crypto`, `os/apps/sshd/ssh_cipher`
     and `os.crypto.aes_gcm`.
   - `os/crypto/aes256_gcm.spl` now checks lengths before it calls into this
     module. The module's other callers get no check.
4. **`rt_tls13_aes128_gcm_decrypt` returns different encodings depending on
   the backing.**
   - The Rust interpreter (`interpreter_extern/simd.rs`) and the Rust runtime
     (`runtime/src/value/aes.rs`) return status-prefixed bytes: `[]` for
     invalid input, `[0x00]` for a tag mismatch, and `[0x01, ...pt]` on
     success.
   - The baremetal C stub (`examples/.../baremetal_stubs.c`) returns raw
     plaintext, or `NIL` on failure.
   - `src/os/tls13/record13.spl:294,346` and `sffi/host.spl:606` still read
     the result as if it were raw plaintext (found by reading the code; no
     spec reproduces it yet). In record13, a `[0x00]` tag
     mismatch falls into the "missing content type" error, so it fails closed
     only by accident. A successful decrypt keeps the 0x01 status byte at the
     front of the plaintext.
   - The noalloc TLS copy no longer calls this extern. Its fast path accepted
     a forged tag as `Ok`; see the bug doc above.
5. **Neither NVFS block provider is backed in the C runtime.**
   `rt_aes128_encrypt_block_pure` is defined only in the Rust interpreter and
   the Rust runtime. The rewound `rt_aes128_encrypt_block_into` had no C
   backing either. A C-runtime native NVFS lane needs a backing or the import
   of canonical that FR-NVFS-N6a-002 describes.
