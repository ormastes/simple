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
Semantic error is GONE — the export resolves and all five specs compile.
Host-key signing for ed25519 / rsa-sha2-256 / rsa-sha2-512 / ecdsa-p256 is now
actually exercised and passes.

| spec | result |
|---|---|
| `test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl` | **1 example, 0 failures** — PASS (exit 0) |
| `test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` | completed, exit 0 — **27 pass / 1 fail** across 6 describes (below) |
| `test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl` | **0 examples**, timeout at 3300s (exit 124) |
| `test/03_system/os/os_ssh_rsa_hostkey_spec.spl` | **0 examples**, timeout at 3300s (exit 124) |
| `test/03_system/os/os_ssh_rsa_sha512_hostkey_spec.spl` | **0 examples**, timeout at 3300s (exit 124) |

### ssh_kex_hostkey_matrix_spec per-describe
| describe | line |
|---|---|
| ssh-ed25519 host key signing | `10 examples, 0 failures` |
| host-key aware KEXINIT builder | **`2 examples, 1 failure`** |
| rsa-sha2-256 host key signing | `3 examples, 0 failures` |
| rsa-sha2-512 host key signing | `3 examples, 0 failures` |
| ecdsa-sha2-nistp256 host key signing | `4 examples, 0 failures` |
| unknown host key algorithm + host_key_set_advertised_algorithms | `5 examples, 0 failures` |

## Newly-revealed failure #1 — KEXINIT fixed-offset layout
`test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl:347`
`✗ encodes the KEXINIT cookie, languages, and reserved trailer at fixed offsets`

Runner message: `expected call result to be truthy, got 0`.

The example builds an ed25519-only KEXINIT via
`ssh_build_kexinit_for_host_keys` and walks the wire layout: msg byte `20`,
16 zero cookie bytes, `ssh_get_u32(payload, 17) == 17`, then skips 10 name-list
fields, then expects the `first_kex_packet_follows` bool `0`, a reserved u32
`0`, and `off + 4 == payload.len()`. One of those offset reads returns 0.
The runner's message is generic (no offset/line), so the exact failing
assertion is not pinned down; the `ssh_get_u32(payload, 17)` length-field read
is the most likely culprit. NOT fixed here and NOT weakened — out of lane scope
(the fix would land in the KEXINIT builder, not in `ssh_kex.spl`).

## Newly-revealed failure #2 — three RSA specs never emit a single example
`ssh_kex_rsa_contract_spec`, `os_ssh_rsa_hostkey_spec`,
`os_ssh_rsa_sha512_hostkey_spec` all hit the 3300s timeout (exit 124) having
printed zero `✓`/`✗` and no `N examples` line. `ssh_kex_rsa_contract_spec`
prints only its describe header, then stalls; the two system specs stall before
any output at all. A solo 900s run of `ssh_kex_rsa_contract_spec` behaved
identically, so this is not contention.

These specs generate a real key by shelling out to
`openssl ... -pkeyopt rsa_keygen_bits:2048` and then drive the Simple RSA path.
Every run also logs:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown type: u128
```

so the RSA bignum code (which uses `u128`) runs fully interpreted. Note this is
a *hang in these three specs specifically* — the RSA signing describes inside
`ssh_kex_hostkey_matrix_spec` DO complete and pass, so interpreted RSA is not
categorically non-terminating. The stall is more likely in the openssl
subprocess / key-import step these three share. Root cause not isolated here.

## Suspected failures that did NOT reproduce
The two flagged in the task brief — daemon advertising `ssh-ed25519` when config
disables it, and the interactive shell bridge never executing commands — did not
appear. A concurrent session has uncommitted fixes in paths I do not own:
`src/os/apps/sshd/sshd.spl` (+37, adds `advertise_ed25519` /
`advertise_ed25519_host_key` plumbing that gates `ed25519_seed`) and
`src/os/apps/sshd/ssh_remote_shell.spl` (+34/-18). These appear to have already
addressed both. The transcript spec walks version/KEX/NEWKEYS/service/
password-auth/channel packets clean.

## Not done
No commit, no push (per lane instruction). No spec was weakened.

## Pre-existing warnings (every run, not caused by this change)
`compiler_cross_module_private_symbol_collision` for `_cswap_pair`,
`_hex_digit`, `_ladder_step`, `_u8_at` — duplicate private helper names with
differing signatures co-compiled; JIT may dispatch to the wrong definition.
