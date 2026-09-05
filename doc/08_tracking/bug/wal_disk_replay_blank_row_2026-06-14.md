# wal_disk_replay_blank_row

- **ID:** wal_disk_replay_blank_row
- **Severity:** P0 (data integrity)
- **Status:** FIXED
- **Date found / fixed:** 2026-06-14
- **File:** `src/lib/nogc_sync_mut/db/dbfs_engine/meta_store.spl`
- **Found via:** simple-db-hardening research; tracked as `wal-disk-replay-blank-row-p0`
  in `test/05_perf/db/db_ram_vs_persistent_bench_spec.spl`.

## Symptom

WAL disk replay dropped **all** field data. After writing inode/dentry rows to the
DBFS `MetaStore` journal and reopening a fresh handle (forcing disk replay), every
replayed row came back blank — or replay failed outright.

## Root cause

Two distinct defects on the disk-replay path, both in `meta_store.spl`:

1. **Serialization collapsed every op to an empty CHECKPOINT.**
   `_serialize_journal_entry` discriminated the journaled operation with
   `if entry.op is MetaOp.InodeWrite: ... else if entry.op is MetaOp.DentryWrite: ...`.
   The qualified enum-variant test `op is MetaOp.Variant` evaluates **false** under
   the interpreter even for a freshly constructed payload-carrying variant (see
   `interp_qualified_enum_is_payload_variant`). Every branch fell through to the
   `else` arms, producing op tag `"CHECKPOINT"` and an empty payload. The on-disk
   journal therefore contained `1~CHECKPOINT~<ts>~` with **no field data** — the
   data was already gone at write time, so replay had nothing to reconstruct.

2. **Replay pushed un-unwrapped Options into a typed array.**
   `_parse_journal_text` did `val entry = _parse_journal_entry(line); if entry: result.push(entry)`.
   `if entry:` is a truthiness test, not a binding/unwrap, so an `Option`-wrapped
   `MetaJournalEntry` was pushed into `[MetaJournalEntry]`. The subsequent
   `entries[i].sequence` access then failed with
   `unknown property or method 'sequence' on Option`.

## Fix

- Rewrote `_serialize_journal_entry`'s op-tag and payload selection to use `match`
  (which discriminates payload-carrying variants correctly and binds their fields).
- Rewrote `_parse_journal_entry` to construct and `return` the `MetaJournalEntry`
  directly per branch, unwrapping parsed-row Options with `.?` / `.unwrap()`.
- Fixed `_parse_journal_text` to unwrap with `if entry.?: result.push(entry.unwrap())`.

Only `nogc_sync_mut/db/dbfs_engine/meta_store.spl` carried the broken pattern; the
`gc_async_mut`, `gc_sync_mut`, and `nogc_async_mut` tier copies re-export from it,
so the single fix covers all tiers.

## Before / after (seed driver)

Raw `.meta.wal` after two writes (inode ino_id=42 size=420; dentry name="hello.txt"):

- **Before:** `1~CHECKPOINT~<ts>~` and `2~CHECKPOINT~<ts>~` (payload empty), replay
  errored `unknown property or method 'sequence' on Option`.
- **After:** `1~INODE_WRITE~<ts>~42|1|33188|1000|1000|1|420|111|222|7` and
  `2~DENTRY_WRITE~<ts>~1|hello.txt|42|1`; replay reconstructs
  `inode ino_id=42 gen=1 size=420 mtime=111 flags=7` and
  `dentry parent=1 name=[hello.txt] child=42 gen=1` — exact field round-trip.

## Test

`test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` "wal disk-replay path" was
un-`pending`'d into a real assertion (`run_wal_disk_replay_field()` →
`expect(result).to_equal("42|420|bench.txt")`). Verified non-stub: flipping the
expected value in-file moves the runner count from 7 pass / 6 fail to 6 pass / 7
fail. A dedicated isolation spec
(`test/05_perf/db/wal_disk_replay_repro_spec.spl`) passes on the correct value and
fails on a wrong value.

(The 6 remaining failures in the bench spec are pre-existing/baseline —
`interp_cross_module_struct_unit` PureDatabase persistent-path issues — unrelated
to this fix; count is identical before and after.)

## Known limitation (not this bug, not fixed — no gold-plating)

`_parse_journal_entry` splits the line on `~` and takes `parts[3]` as payload, so a
dentry `name` containing a literal `~` would still truncate. Pre-existing, not the
blank-row bug, and not exercised by this fix.
