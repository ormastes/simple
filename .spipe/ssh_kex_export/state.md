# ssh_kex_export — state

## Task
Re-export `ssh_sign_exchange_hash` from `src/os/apps/sshd/ssh_kex.spl` (defined in
sibling `ssh_kex_crypto.spl:352`), unblocking five specs that died with
`semantic: function ssh_sign_exchange_hash not found`.

## Change (own path: src/os/apps/sshd/ssh_kex.spl only)
Two lines, matching the sibling re-export pattern already used for
`ssh_kex_core` / `ssh_kex_random` / `ssh_kex_primitives`:

- `use os.apps.sshd.ssh_kex_crypto.{ssh_sign_exchange_hash}` (after the
  `ssh_kex_core` use block)
- `export ssh_sign_exchange_hash` (appended to the export list)

Found already present as uncommitted work in the working copy on entry
(a parallel session had applied the identical edit). Verified by `git diff`;
kept as-is. Backup: `/tmp/ssh_kex_export_backup/ssh_kex.spl`.

## Verdict
Semantic error is GONE — the export resolves. All five specs now compile.

| spec | result |
|---|---|
| `test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl` | **1 example, 0 failures** (PASS) |
| `test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` | 8 ed25519/x25519 examples PASS, then stalls in the RSA describes; no summary line within 55 min |
| `test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl` | 0 examples emitted; stalls immediately after the describe header |
| `test/03_system/os/os_ssh_rsa_hostkey_spec.spl` | 0 examples emitted; stalls before any output |
| `test/03_system/os/os_ssh_rsa_sha512_hostkey_spec.spl` | 0 examples emitted; stalls before any output |

## Newly-revealed blocker: RSA signing runs fully interpreted
Every run logs:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown type: u128
```

The RSA bignum path uses `u128`, which the JIT cannot lower, so the whole
program drops to the interpreter. A 2048-bit RSA private-exponent modexp
(the specs generate a real key via `openssl ... rsa_keygen_bits:2048`) is then
effectively non-terminating. This is why the RSA halves of all four specs emit
zero examples. Ed25519/X25519 signing is fine (transcript spec is green).

Not fixed here — out of lane scope. Needs either JIT `u128` lowering or an
RSA path that avoids `u128`.

## Also observed (not fixed here, per lane scope)
The two suspected failures (daemon advertising `ssh-ed25519` when config
disables it; interactive shell bridge never executing commands) did NOT
reproduce. A concurrent session has uncommitted fixes in
`src/os/apps/sshd/sshd.spl` (`advertise_ed25519` / `advertise_ed25519_host_key`
plumbing) and `src/os/apps/sshd/ssh_remote_shell.spl`, which appear to have
already addressed them — the transcript spec walks version/KEX/NEWKEYS/service/
password-auth/channel packets clean.

## Not done
No commit, no push (per lane instruction). No spec was weakened.

## Secondary warnings seen (pre-existing, all specs)
`compiler_cross_module_private_symbol_collision` for `_cswap_pair`,
`_hex_digit`, `_ladder_step`, `_u8_at` — duplicate private helper names with
differing signatures co-compiled; JIT may dispatch to the wrong one.
