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

## Spec sites: DISARMED (2026-09-12)

**Correction to an earlier draft of this record**, which claimed
`TestDatabase.load()` had no `load_from(path)` counterpart and that converting
the remaining sites needed a library addition. That was wrong — it was based on
grepping `src/lib/nogc_sync_mut/database/test.spl` and `test_db_compat.spl`
rather than the class the spec actually imports. Both counterparts have existed
all along:

- `src/app/test_runner_new/test_db_core.spl:146` `static fn load_from(path: text)`
  and `:161` `me save_to(path: text)`
- `src/lib/nogc_sync_mut/test_runner/test_db_core.spl:189` / `:203`, likewise

Every `db.save()` and `TestDatabase.load()` call in **both** live copies of the
spec (`test/01_unit/app/tooling/` and the `test/unit/` mirror) is now
`save_to(temp_db_path(test_name))` / `load_from(temp_db_path(test_name))`. The
count of global-path calls in those two files is 0, and `cleanup_temp_db` also
clears the `{path}.lock` sidecar so a stale lock cannot make an isolated write
silently produce nothing.

### A second defect this exposed

`"maintains bounded file size with window capping"` saved to the **tracked**
database and then measured `file_size(temp_db_path(test_name))` — a path nothing
ever wrote. Every sample in its `file_sizes` list came from a file that did not
exist, so its growth-ratio assertion was measuring nothing at all. Pointing the
save at the same path it measures makes that scenario real rather than merely
safe.

## Still OPEN: `save()` defaults to the tracked path

Disarming the spec sites does not address the underlying hazard, which is why
this record stays open: `save()` and `load()` silently target
`doc/08_tracking/test/test_db.sdn`, so the *next* spec or tool that calls the
zero-argument form re-arms the same clobber with nothing to warn its author. The
repository has no gate asserting that a unit spec leaves tracked files clean.

Worth considering: make the zero-argument `save()` refuse to run when a spec
runner is the caller, or add a cheap post-suite check that
`git status --porcelain doc/08_tracking/test/` is empty for any spec not
explicitly allowlisted to write it.
