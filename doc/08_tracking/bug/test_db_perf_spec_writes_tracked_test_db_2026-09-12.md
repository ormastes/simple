# `test_db_performance_spec` writes the repository's tracked `test_db.sdn`

- Status: OPEN (2026-09-12)
- Area: test / app / tooling
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 prefix `3d120a6f`
- Found while implementing todo row 232

## Symptom

`test/01_unit/app/tooling/test_db_performance_spec.spl` calls `db.save()` at
four remaining sites (lines 139, 167, 191, 368 at the time of writing).
`RunnerTestDbCore.save()` / `TestDatabase.save()` write the global
`DB_PATH = "doc/08_tracking/test/test_db.sdn"` — there is no path parameter on
`save()`. Running the spec therefore overwrites the repository's tracked test
database with up to 10,000 synthetic records, and leaves a
`doc/08_tracking/test/test_db.sdn.bak` behind.

Measured directly:

```
$ git status --porcelain
 M doc/08_tracking/test/test_db.sdn
?? doc/08_tracking/test/test_db.sdn.bak
```

after a single `bin/simple test test/01_unit/app/tooling/test_db_performance_spec.spl`.

## Why it surfaced now

Until `write_db_file_locked` was repaired (Option-vs-Result match defect in
`src/lib/nogc_sync_mut/test_runner/test_db_io.spl`), every one of those saves
aborted and wrote nothing, so the clobber was masked by a second defect. With
the writer working, the spec's writes land.

## Partly addressed

The "maintains reasonable memory footprint" scenario now uses
`db.save_to(temp_db_path(...))`, which takes an explicit path, and no longer
touches the tracked database. The other four sites are not converted here
because they are paired with `TestDatabase.load()`, which has **no**
`load_from(path)` counterpart — reading back from an isolated path needs a
library addition, not a spec edit. Those four scenarios are additionally RED for
unrelated pre-existing reasons (7 of 11 examples fail at
`work/todofix-1-2026-09-12` base `79a67e79135`).

## Expected

`TestDatabase.load_from(path)` beside the existing `save_to(path)`, then every
scenario in this file pinned to an isolated path. No spec should be able to
write a tracked artifact.
