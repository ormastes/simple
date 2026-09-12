# Interp TestDatabase class-name collision kills every aggregate `simple test` run

**Date:** 2026-07-17
**Severity:** P1 (directory runs, sdoctest/md phase, and test_result.md generation all die)
**Status:** fix in progress (runner-side rename), interpreter root cause remains open

## Symptom

Any aggregate run — `simple test <directory>`, or any non-single-file target —
finishes executing specs and then dies:

```
Results: 1 total, 0 passed, 1 failed
error: semantic: class `TestDatabase` has no field named `db`
```

Because the crash is in the post-run database phase
(`src/app/test_runner_new/test_runner_main.spl:824-861`,
`update_test_database` → `generate_test_result_md`), it also prevents the
sdoctest/markdown-fence phase from ever running and blocks
`doc/08_tracking/test/test_result.md` generation. Single-file spec runs are
unaffected (they route through the light-daemon client path).

Repro: `timeout 300 src/compiler_rust/target/release/simple test test/01_unit/os/smf`

## Root cause

The documented interpreter landmine: same class name in multiple modules
collides in the seed interpreter's global struct registry. Three definitions
exist:

- `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl:24` (runner compat
  wrapper — HAS the `db` field)
- `src/lib/nogc_sync_mut/database/test.spl:143`
- `src/lib/nogc_async_mut/database/test.spl:123`

The aggregate path loads both the runner compat class and a database-tier
module; field lookup then resolves against the wrong definition.

## Fix

- Runner-side (.spl, sanctioned mitigation, in progress 2026-07-17): rename
  the runner-internal compat class to `RunnerTestDb` across
  `src/app/test_runner_new/**` and `src/lib/nogc_sync_mut/test_runner/**`;
  database-tier classes stay (public stdlib surface for check-dbs/fix-dbs/MCP).
- Regression contract: an aggregate directory run must complete its post-run
  phase (no `no field named` output; exit code reflects spec results).
- Interpreter root cause (global registry not module-scoped) stays open —
  seed-side, out of .spl scope; see memory
  `feedback_interp_struct_name_collision_global_registry`.

## How found

Tooling-surface smoke matrix during the 2026-07-17 test-runner hardening
campaign (md/sdoctest lane probe hit it first; directory probe confirmed).

## Second (internal) collision found 2026-07-17 — fixed

The rename exposed a SECOND, runner-internal instance of the same landmine:
`test_db_core.spl` defines a `struct` and `test_db_compat.spl` a `class`
that shared the name (`TestDatabase` before the rename, `RunnerTestDb`
after it), so DB-writing runs could still resolve the wrong definition.
Fixed by renaming the core-struct cluster to `RunnerTestDbCore`
(`test_db_core.spl`, `test_db_validation.spl`, `test_db_migrate.spl`,
`test_db_perf.spl`; compat class and its users unchanged; 0 leftovers,
green single-file and md-lane probes pass). The underlying interpreter
defect (global struct registry not module-scoped) remains open seed-side.

## Re-check 2026-09-12 — symptom gone across three aggregate runs; root cause unverified, left OPEN

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1` (aarch64 host).

Three full directory runs of `test/01_unit/bugs/` (an aggregate target, i.e.
exactly the shape this row says always dies):

```
Results: 349 total, 339 passed, 10 failed, 7 skipped     (with 8 new guards)
Results: 341 total, 331 passed, 10 failed, 7 skipped     (same tree, 8 guards held out)
Results: 369 total, 359 passed, 10 failed, 7 skipped     (with 11 new guards)
```

All three reached the summary block and exited through the normal reporting
path. The documented terminator —

```
error: semantic: class `TestDatabase` has no field named `db`
```

— did **not** appear in any of them.

What DID appear, on every run, is a non-fatal line at the very end:

```
Warning: Could not load test database: could not open or parse
doc/08_tracking/test/test_db.sdn (existing file is unreadable or migration from
doc/08_tracking/test/test_db_stable.sdn failed)
```

### Why this is not closed

The record's own framing separates two things: the runner-side rename (which
was already "fix in progress") and the **interpreter root cause**, the
class-name collision itself. Three clean aggregate runs are strong evidence the
*symptom* is gone; they are no evidence at all about the *collision*, which was
not probed here. The warning above is also unexplained — it is the surviving
trace of the test-DB path this row is about, and a row whose failure mode has
merely softened from fatal to a warning should not be closed on that basis.

Left OPEN. Whoever owns it needs a direct probe of the class-name collision,
plus a decision on whether the `test_db.sdn` load failure is the same defect
wearing a quieter face.
