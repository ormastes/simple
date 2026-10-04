# sshd stale-snapshot rewind via transplant 88aac2ffe28 (2026-10-04)

**Status:** repaired (see PR referenced in the fixing commit).

## What was lost

`88aac2ffe28` ("rebase(main): transplant current main tree onto release/1.0",
single parent `d921e11599e`) replaced `src/os/apps/sshd/` and
`test/01_unit/os/apps/sshd/` with the tree of the pre-rebase main lineage
(`origin/agent/pr1453-required-gate-repair-20260924`, sshd tree `8ac8c0d2`).
That lineage had itself rewound sshd in the share-history merges
`a8244005f9b` / `e274cd33719`: eight of its sshd files were byte-identical to
*older* release blobs, and several more were older blobs plus a few genuine
edits. The true merge base (`b2bd1e635b7`) had sshd == release, so a normal
3-way merge would have accepted every rewind.

Rewound (pure, file == an older release blob): `ssh_cipher`, `ssh_kex`,
`ssh_kex_crypto`, `ssh_kex_primitives`, `ssh_mac`, `ssh_pty`,
`ssh_remote_shell`, `ssh_session_lifecycle`; specs
`ssh_channel_open_capacity`, `ssh_kex_rsa_contract`, `ssh_kexinit_packet_layout`,
and (main edits on a stale base that reverted release fixes, e.g. "empty host
key set advertises nothing" -> "ssh-ed25519") `ssh_kex_hostkey_matrix`.

Rewound in part (older blob + genuine main edits): `ssh_auth` (public-key-only
auth, `ssh_check_public_key_auth` + helpers, `add_user_identity`,
`add_password_verifier`, verifier-only storage), `ssh_channel` (channel-cap /
invalid-id / replay guards, checked window arithmetic), `host_key_loader`
(`file_exists` facade -> raw `rt_file_exists`), `ssh_session_helpers`
(`ssh_session_u8_at`, KEXINIT helpers), plus 8 specs.

## How detected

Session code and specs referenced names with no definition
(`ssh_check_public_key_auth`, `host_key_set_has_any_algorithm`,
`ssh_session_u8_at`, `SshUserDb.add_user_identity`, ...); the x86_64 SSH kernel
(`ssh_ring3_clang_entry.spl`) failed with `hir: cannot infer field type ...
key_blob`. Per-file, the closest historical release blob to the transplanted
file was found; distance 0 identified pure rewinds.

## What was restored

- Pure rewinds: release blob from `88aac2ffe28~1`.
- Partial: release version + only the genuine main additions, reviewed hunk by
  hunk: `SshAuthAttemptBudgetV1` / `MAX_AUTH_EMPTY_POLLS` (ssh_auth),
  `split_whitespace` free-function fix (host_key_loader),
  `_name_list_range_is_well_formed` KEXINIT check (ssh_session_helpers).
  Main-side deletions of release hardening, a dangling
  `export ssh_parse_channel_data_header_v1` (never defined anywhere) and a
  dead `_build_publickey_signed_data` were not taken.
- `ssh_packet_spec`: two error-path vectors predated the release's RFC 4253
  8-byte alignment check (failing at `88aac2ffe28~1` too); re-encoded as
  aligned packets so the intended check is the one that rejects.
- Files main changed on top of the current release blob (`ssh_cipher_live`,
  `ssh_session`, `ssh_session_channel`, `ssh_transport`) and the six files main
  added are kept as-is.

## Crypto (pointed to by the sshd KEX specs)

The same transplant rewound `src/os/crypto/`: 27 of 35 changed files were
byte-identical to older release blobs (`ed25519*`, `curve25519`, `ecdsa_p256/p521`,
`ml_kem*`, `sha384/512`, `aes_gcm*`, `rsa_fallback`, `random`, ...). Those 27 are
restored to `88aac2ffe28~1`; no exported symbol is lost (only private helpers
the release refactor had removed). `curve25519_smalllimb` (patched after the
transplant in `728a98d4791`) gets the transplant diff reverse-applied on top of
that patch, which lands byte-identical to `88aac2ffe28~1` — restoring
`curve25519` alone would have left it calling the removed `_cswap_pair`. Not
touched: `aes128_gcm`, `aes256_gcm`, `paseto`, `pem`, `rsa`, `rsa_pss`,
`sha256` — these mix older content with edits and need a hunk-level review.

## Wider footprint (open)

`88aac2ffe28` changed 44,803 files. Only sshd, its specs and the pure crypto
rewinds are repaired here; the rest of the tree needs the same
closest-older-blob audit (a file byte-identical to an older blob of its own
release history is a rewind, not new work).

## Not restored (pre-existing, different root cause)

Specs that arrived with the transplant reference names that were never defined
on release (also absent at `88aac2ffe28~1`), lost on the main lineage before the
transplant (`4edef8fab8e`, `e274cd33719`) or never landed anywhere — see the
spec table in the fixing PR.
