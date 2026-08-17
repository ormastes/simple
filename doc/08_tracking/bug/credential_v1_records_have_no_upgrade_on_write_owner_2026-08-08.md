# v1 credential records are never rewritten: no config writer owns the upgrade

Status: OPEN (P3)
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
