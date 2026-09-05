# Test database never created: every run silently recorded nothing

- **Status:** FIXED (cold-start hole) + one residual open (see § Residual)
- **Verification 2026-08-21 (bug-status-consistency audit): PARTIAL, not fully fixed.** the cold-start hole is closed (`factory.spl:185`), but the § Residual directory-run abort ("cannot convert string to int" before persistence) is still open — this is a DATA-PERSISTENCE residual, not cosmetic. `bug_db.sdn` row is `fix-implemented-verification-pending`.
- **Date:** 2026-08-10
- **Files:** `src/lib/nogc_sync_mut/database/test_extended/factory.spl`,
  `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`

## Symptom

Every spec run ended with `Warning: Could not load test database`, and
`doc/08_tracking/test/test_db.sdn` + `doc/08_tracking/test/test_result.md` were
never regenerated, despite `.claude/rules/structure.md` declaring both are
rewritten on every test run.

## Emission site

Exactly one live site (`/usr/bin/grep -rn`, 17-hit-capable, not the wrapped
ugrep):

- `src/lib/nogc_sync_mut/test_runner/test_runner_helpers.spl:234` — inside
  `update_test_database`, on the `Err` arm of `load_test_db_compat()`.
- `src/lib/nogc_sync_mut/test_runner/test_runner_config.spl:289` is the same
  text but **commented out** — not a second emitter.

## Root cause

`load_with_migration(base_path)` (`factory.spl:152`) had three branches:

1. unified `{base}.sdn` exists → load it;
2. dual-file `{base}_stable.sdn` **and** `{base}_runs.sdn` exist → migrate;
3. otherwise → `nil`.

Measured on-disk state: **neither `test_db.sdn` nor `test_db_stable.sdn`
exists**; only an orphan `test_db_runs.sdn` (192 KB, dated Jun 26). So branch 3
fired on every run. Nothing anywhere in the tree creates `test_db.sdn`, so this
is a **permanent cold-start hole**: the first run could never succeed, and
therefore neither could any run after it.

`RunnerTestDb.load()` then flattened the `nil` into a generic
`Err("Failed to load test database")`, which the runner printed as the warning
and returned early — so `generate_test_result_md` (`test_runner_main.spl:1113`,
guarded on the `db` result) never ran either. **One root cause, both dark
channels.**

## Fix

- `factory.spl`: branch 3 now returns `Some(create_test_database_extended(unified_path))`
  — the constructor was already in scope and already used by the migration path.
  The branch fires **only when no file exists**, so an existing (even corrupt)
  file is never silently replaced.
- `test_db_compat.spl`: the remaining `Err` now names the path and the two real
  causes (unreadable file / failed migration) instead of a generic string. The
  warning stays **loud** — cold start is fixed, it is not silenced.

## Proof (probe: `build/test/probe_coldstart.spl`, `bin/simple run`)

| | pre-exists | loaded | saved | post-exists | reload total |
|---|---|---|---|---|---|
| fixed    | false | Some | true  | true  | **1** |
| sabotage (`nil`) | false | nil | false | false | -1 |
| restored | false | Some | true  | true  | **1** |

`reload total = 1` is a **content** check (the run is read back out of the saved
file), not an mtime check.

## Residual (open)

A directory run (`bin/simple test test/01_unit/lib/blink`, 24 files,
`Results: 104 total, 59 passed, 45 failed`) terminates immediately after the
results banner with:

```
Some tests failed.
error: semantic: type mismatch: cannot convert string to int
```

This aborts the persistence block **before** the DB load is even attempted (that
run printed the warning **zero** times). Whether this predates the fix above is
not established — the interpreter compiles that path lazily, at call time, so
the observation window overlapped this session's edits. It must be re-measured
against a clean tree. Until then, the cold-start fix is proven at unit level but
**not** end-to-end through `bin/simple test`.

## Why nothing caught it

The mechanism for noticing broken tests was itself broken, and nothing watches
the watcher. No spec asserted that a run records to the database, so the only
signal was a warning line at the end of a multi-thousand-line log — and it
compounded a second fail-open (specs that fail to load emit no
`SPEC FILE VERDICT:` line, so verdict-counting sweeps saw nothing either). Two
independent observation channels, both dark, neither monitored.

Regression spec added: `test/01_unit/lib/test_runner/test_db_cold_start_spec.spl`.

## Duplication

`src/lib/nogc_async_mut/database/test_extended/factory.spl` is a 4-line
re-export shim, **not** a second implementation — the loader exists once, so
there was nothing to merge here.

Separately noted (not merged; owned by another session):
`src/app/test_runner_new/test_runner_main.spl` (1138 lines) and
`src/lib/nogc_sync_mut/test_runner/test_runner_main.spl` (939 lines) are two
**diverged** copies of the runner main. Only the `app` copy calls
`update_test_database`. This divergence is a real rule-2 finding and should be
reconciled by whoever owns `src/app/test_runner_new/**`.
