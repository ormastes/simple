# bug-add: rename_path infinite recursion, and its temp DB drops existing rows (2026-10-04)

**Severity:** P1 — the tracker's own write path cannot record a bug, and the
half-written output would destroy data if renamed into place.
**Component:** `src/app/bug_add/main.spl` -> `nogc_sync_mut.database.bug` save path;
`src/lib/nogc_sync_mut/io_runtime.spl:469 rename_path`.

## Repro

```sh
simple run src/app/bug_add/main.spl --id=x --severity=p1 --title=t \
  --file=doc/08_tracking/bug/<some>.md --date=2026-10-04
```

Seed built from origin/main 616fba69588 (+ #2459), interpreter path:

```
error: stack overflow: recursion depth 1000 exceeded limit 1000 in function 'rename_path'
```

It leaves `bug_db.sdn.tmp` and `bug_db.sdn.lock` behind; `bug_db.sdn` is unchanged.

## Second defect: the temp file is not a superset

`bug_db.sdn.tmp` contains the new row and a valid `#sdn-crc32` header, but
`git diff` of tmp vs the committed DB is +1888 / -3590 lines: the rewrite drops
existing rows. Renaming it into place (what the crashed step was about to do)
would silently delete roughly 1,700 lines of tracked bugs.

## Notes

`io_runtime.rename_path` only calls the `rt_file_rename` extern, so the recursion
comes from name resolution in the import closure (several modules declare
`rename_path` — `fs_driver` / `dbfs_driver` / `nvfs` trait methods), consistent
with the same-name flattening defect in
`caret_jit_fallback_flatten_same_name_types_2026-10-04.md`. Not yet bisected.

Workaround used on 2026-10-04: rows appended by hand and resealed with
`scripts/check/reseal-sdn-crc32.shs`.

**Revalidated 2026-11-02: still plausible because the report title (bug-add crashes with rename_path infinite recursion) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

**Closed 2026-11-03 (verified on origin/release/1.0.0):** the recursion is gone. `file_ops.file_rename` now delegates to the exact rename-only `io_runtime.rename_path` (extern `rt_file_rename`), and the bug-add save path (`database/atomic.spl`) uses `io_runtime.file_rename`. Probe with `bin/simple.exe run src/app/bug_add/main.spl --id=a1`, then `--id=a2` in a fresh project root: both runs saved, the DB grew 23 -> 27 lines with both rows present, no `.tmp`/`.lock` left behind (only the `.wal`). The "temp file drops rows" half is covered by the fail-closed load behaviour (775e005dc65, `bug_add_overwrites_unreadable_existing_database_2026-10-27.md`) and `test/02_integration/app/bug_add_database_preservation_spec.spl`. Note: on this Windows host, loading the full 9k-line canonical DB returns nil, so bug-add refuses to write (safe, does not overwrite); that is a separate SDN load issue, not rename_path.
