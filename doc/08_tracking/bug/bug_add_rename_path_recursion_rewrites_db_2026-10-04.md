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
