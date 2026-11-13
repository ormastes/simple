# AES-GCM encrypt reads past short key/nonce; canonical hardening still rewound

- **ID:** aes_gcm_encrypt_length_unchecked_and_rewound_hardening_2026-11-13
- **Severity:** P2 (fail-open crypto input handling)
- **Status:** open (decrypt side and canonical restore fixed; encrypt side open)
- **Found by:** lane work/aesgcm-copies-20261113 (follow-up to PR #8878)
- **Related:** `aes128_gcm_verification_blocked_by_env_access_parse_2026-08-25.md`

## Summary

Every AES-GCM decrypt copy now fails closed on a wrong-length key, nonce or
tag before it reads any input byte. The canonical copy has its `db9fa3350a4`
hardening back, encrypt guard included. No caller reads the
`rt_tls13_aes128_gcm_decrypt` result as raw plaintext any more. The items
under "Open" remain.

## Fixed

| Item | Where | Fix |
|---|---|---|
| Decrypt length guards (NVFS, noalloc TLS, os AES-256 wrapper) | PR #8890 | key/nonce/tag checked first |
| Decrypt length guards, sshd copy | `src/os/crypto/aes_gcm.spl` | key 32, nonce 12, tag 16 checked first |
| Decrypt length guards, `std.common.crypto.aes_gcm` | aes128/192/256 decrypt | key 16/24/32, nonce 12, tag 16 checked first |
| Canonical copy rewound by `e274cd33719` | `src/os/crypto/aes128_gcm.spl` | `db9fa3350a4` blob restored; #8878's length-profile docstring kept on the public decrypt |
| `rt_tls13_aes128_gcm_decrypt` read as raw plaintext | `record13_decrypt_fd`, `sffi/host.spl` | see below |

Notes on the fixed items:

- **Decrypt guards.** On base, an empty key or nonce zero-extended to the
  all-zero TC2/TC14 key or IV and decrypted to `Ok`. In the sshd copy, a wrong
  length raised an out-of-bounds index error. The constant-time tag compare
  is unchanged in every copy.
- **Canonical restore.** `git diff db9fa3350a4 -- src/os/crypto/aes128_gcm.spl`
  is now only that docstring. The `e274cd33719` rewind had also renamed
  `_aes128_gcm_ghash_block` back to `_ghash_block`; that is undone too.
  `sh scripts/audit/aes128-gcm-sffi-authority.shs` passes both halves.
- **record13.** `record13_decrypt_fd` now delegates to `record13_decrypt`,
  which uses the canonical pure decrypt. Before, a forged tag read raw gave
  `Ok(content_type: 0, data: [])`. That is not the "missing content type"
  error this doc used to claim; the trailing-zero scan stops at index 0. A
  genuine record kept the `0x01` status byte as data.
  - On hosted runtimes the fd path never reached the decrypt. Its
    `rt_tls13_record_payload_len` has no Rust backing, so the call failed with
    "unknown extern function".
  - The unused `record13_decrypt_fd_inner` and both externs are deleted, and
    so is the unused extern declaration in `nogc_async_mut_noalloc/tls/record.spl`.
- **sffi/host.spl.** `tls13_aes128_gcm_decrypt` now returns
  `Result<[u8], text>`. It checks key, nonce and tag lengths before the
  provider runs. `tls13_aes128_gcm_decrypt_decode` maps the status-prefixed
  result:
  - `[0x01, ...pt]` → `Ok(pt)`
  - `[0x00]` → `Err("authentication tag mismatch")`
  - `[]` → `Err` (rejected inputs)
  - anything else → `Err` (invalid result)

  The `rt_alias_map.sdn` entry is now `class: adapted`, so `rt_migrate` will
  not mechanically rewrite raw call sites to it.
- **Raw-SFFI baseline.** Removed 12 rows for declarations that no longer
  exist or are now `@unsafe`-tagged:
  - 6 for the NVFS copy (stale since #8890)
  - 1 for the noalloc TLS copy (stale since #8890)
  - 2 for the canonical copy
  - 1 for the noalloc TLS `record.spl` declaration
  - 2 for `record13`

Specs:

- `test/01_unit/lib/crypto/aes_gcm_common_kat_spec.spl`
- `test/01_unit/os/apps/sshd/ssh_aes256_gcm_length_guard_spec.spl`
- `test/01_unit/os/tls13/record13_checked_seal_spec.spl` ("record13_decrypt_fd authenticates fail closed")
- `test/01_unit/lib/nogc_sync_mut/sffi/tls13_aes128_gcm_decrypt_decode_spec.spl`

## Open

1. **Encrypt reads past a short key or nonce** in:
   - `src/lib/nogc_async_mut_noalloc/tls/aes128_gcm.spl`
   - `src/os/crypto/aes256_gcm.spl`
   - `src/lib/common/crypto/aes_gcm.spl` (aes128/192/256)
   - `src/os/crypto/aes_gcm.spl` (sshd copy; not listed before)

   `rt_bytes_u8_at` reads an out-of-range index as 0, so a short key or nonce
   is silently zero-extended. The result is valid-looking ciphertext under a
   weak key or IV.

   - All of these return bare `[u8]`. Changing them to a result type touches
     about 60 call sites in about 30 files.
   - The canonical and NVFS copies use `db9fa3350a4`'s approach instead: check
     the lengths and `panic` before the validated core.
   - No spec pins the encrypt panic. The spec runner has no way to assert a
     panic.
2. **`rt_tls13_aes128_gcm_decrypt` backings still disagree.**
   - The Rust interpreter (`interpreter_extern/simd.rs`) and the Rust runtime
     (`runtime/src/value/aes.rs`) return status-prefixed bytes. On invalid
     input the runtime returns `[]` and the interpreter raises
     `rejected its inputs`.
   - The baremetal C stub (`examples/.../baremetal_stubs.c`) returns raw
     plaintext, or `NIL` on failure. An empty plaintext is indistinguishable
     from failure there.
   - Until the stub moves to the status-prefixed encoding, no SimpleOS caller
     may use the decoded `sffi/host.spl` alias. It would reject the stub's
     output, or strip a genuine leading `0x01` byte.
   - **Perf, not measured:** on baremetal, `record13_decrypt_fd` (TLS
     application-data receive over an fd) now runs the pure-Simple AES-GCM
     instead of the C stub. The handshake already used the pure path.
     Restoring the fast path means moving the stub to the status-prefixed
     encoding and routing through the decoded alias.
3. **record13 does not check the IV length** in the unchecked
   `record13_encrypt` and `record13_decrypt` paths. `record13_make_nonce`
   zero-extends a short IV. `record13_encrypt_for_suite_checked` already
   rejects one.
4. **Neither NVFS block provider is backed in the C runtime.**
   `rt_aes128_encrypt_block_pure` is defined only in the Rust interpreter and
   the Rust runtime. A C-runtime native NVFS lane needs a backing, or the
   import of the canonical copy that FR-NVFS-N6a-002 describes.
5. **`check-raw-sffi-unsafe-ratchet.shs` cannot check anything.** Its
   inventory fails the whole-tree ceiling (`source_variants=400/399`,
   `migration=3857/3546`) on base and after this change.
   - Reproducing the comparison by hand shows the baseline has drifted by
     thousands of rows: new=3969 and stale=5605 on base. The head of this
     change, before the baseline edit, measured new=3969 and stale=5610.
   - So this change adds 0 new rows and 5 stale ones. Those 5, plus the 7
     stale since #8890, are the 12 rows removed above.
