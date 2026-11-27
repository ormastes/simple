# v1 credential records are never rewritten: no config writer owns the upgrade

Status: RESOLVED 2026-11-25 — upgrade-on-write owner landed (see dated note at bottom)
Update 2026-11-06: persist spec 11/12 -> 12/12; spec declared unregistered extern rt_ensure_dir, replaced by std.io_runtime dir_create_all.
Status re-verified 2026-08-17 by source inspection (triage shard 00).

- **Filed:** 2026-08-08
- **Severity:** LOW-MED
- **Area:** `src/lib/nogc_sync_mut/terminal/credential/`

## What is wrong

Legacy **v1** credential records — `"encrypted:<hex_iv><hex_ct>"`, written
before 2026-08-08 — were produced by AES-256-CTR under an IV **derived from the
plaintext**, behind a function then named `aes_cbc_encrypt`. Two stored secrets
that collided reused the identical keystream and leaked
`plaintext_A XOR plaintext_B`. See
`doc/08_tracking/bug/credential_store_aes_cbc_label_is_actually_ctr_with_deterministic_iv_2026-08-07.md`.

They stay readable by design, but **nothing ever replaces them**, so the weak
records linger for the life of the install.

## Why it isn't fixed in the store

The re-encryption primitive now exists and is verified:

- `credential_needs_upgrade(value)` — flags a v1 record, ignores v2/plaintext.
- `credential_upgrade_record(value, key_path)` — returns the v2 replacement,
  but only after decrypting the new ciphertext again and confirming it matches
  the original plaintext. Returns `""` otherwise, which the caller must read as
  *keep what you have*, never as *write an empty credential*.

Both are pinned by
`test/01_unit/lib/terminal/credential_key_derivation_hardening_spec.spl`.

What is missing is a **persister**. `credential_upgrade_record` performs no
file I/O on purpose: `credential_decrypt` takes a record, not a location, and
has no idea which config file or field it came from — persisting from inside a
decrypt path is how config files get corrupted.

The natural owner would be `src/lib/nogc_sync_mut/terminal/credential/config_parser.spl`,
which resolves credentials at lines 270 and 398 — but **that module is
read-only**: it contains no `rt_file_write_text`, no rename, no atomic write
path of any kind. There is currently no in-tree caller that both knows a
record's location and can write it back.

## Fix

Give the config layer an atomic write, then wire the upgrade:

1. `config_write_atomic(path, content)` — write `path.tmp`, fsync, `rename(2)`
   over the original. Rename is atomic on POSIX, so an interrupted upgrade
   leaves the original v1 record fully intact and still readable.
2. On load, for each resolved field: if `credential_needs_upgrade(raw)`, call
   `credential_upgrade_record(raw, "")`; if the result is non-empty, substitute
   it and mark the config dirty; flush once through `config_write_atomic`.
3. Never write when the upgrade returns `""`.

## Verification owed once the caller lands

- a v1 record in a config file is v2 after one load-and-save cycle, and still
  decrypts to the same plaintext;
- killing the process between the temp write and the rename leaves the original
  v1 record byte-for-byte intact.

## See also

- `doc/09_report/lib/crypto/credential_store_aes_cbc_adversarial_review_2026-08-08.md` (finding F5)

## Re-verification 2026-08-17 (terminal slice) — STILL OPEN

Classified by CONTENT. `src/lib/nogc_sync_mut/terminal/credential/config_parser.spl`
was grepped for `v1`, `upgrade`, and `rewrite`: **zero matches**. No
upgrade-on-write path exists in the natural owner identified by this doc, so v1
credential records are still never rewritten to v2 on a config write.

Status: OPEN (unchanged). Severity remains LOW-MED — a stale-format record is
still readable; this is a migration gap, not a wrong-result defect.

## Triage 2026-09-13
Reconfirmed: v1 credential records still never get rewritten to a newer
format; needs a config writer/owner design decision, not a quick fix.
Left OPEN (P3), no code change attempted.
## Triage 2026-09-13 (BUGFIX-12 shard 22)

Re-confirmed unchanged at `f26970e9d93`: `config_parser.spl` (400 lines) still
has no `v1`/`upgrade`/`rewrite` match and still no `rt_file_write_text`/rename
call — it is read-only, and `credential_upgrade_record` still performs no I/O
by design. Implementing this properly needs a round-trip SDN serializer (the
parser has no matching writer that preserves untouched fields/formatting)
plus the atomic-write primitive and load-time wiring described above — a real
feature addition past a shard triage budget, not a local one-line fix. No
change made. Leaving OPEN as filed.

## Resolution 2026-11-25 (p3-bau fleet, worktree wt-p3-bau, release/1.0.0 @ e3902cdaa78)

The exact fix this doc specified has since landed; the "read-only owner /
no upgrade path" claims above are stale. Verified by code inspection:

- `src/lib/nogc_sync_mut/terminal/credential/config_parser.spl` now imports
  `credential_needs_upgrade` / `credential_upgrade_file` (lines 19-20),
  defines `config_write_atomic` (line 52), and wires upgrade-on-load via
  `_maybe_upgrade_v1_entries` (line 161) into both the terminals (line 197)
  and power (line 237) parse paths, plus `config_save_atomic` /
  `config_update_entry_field_atomic` write paths.
- `src/lib/nogc_sync_mut/terminal/credential/store.spl:729`
  `credential_upgrade_file` implements the prescribed atomic persist:
  same-directory temp write, fsync, `rename(2)` over the original
  (documented at store.spl:752-753, matching fix step 1 verbatim), and fails
  closed when the upgrade re-decrypt check does not match (fix step 3).
- Pinned by two dedicated specs:
  `test/01_unit/lib/terminal/credential_config_upgrade_on_write_spec.spl`
  (8 examples, REQ-LIB-CREDENTIAL-CONFIG-UPGRADE-001, exercises
  `parse_terminal_config_with_key` / `config_write_atomic` /
  `config_update_entry_field_atomic` against temp files) and
  `test/01_unit/lib/terminal/credential_upgrade_persist_spec.spl`
  (20 examples).

LIMIT: spec re-execution environment-blocked on this host — pinned seed
`bin/simple.exe` (2026-11-17) cannot parse the 2026-11-25
`@representation_boundary` annotations (`cfd89933699`) and aborts before any
spec loads. Closure rests on the inspection above plus the 2026-11-06
12/12 pass recorded in the header.
