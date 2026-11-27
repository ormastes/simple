# Interp TestDatabase class-name collision kills every aggregate `simple test` run

## Triage 2026-11-25 (release/1.0.0, Windows host) — root cause seed-side; .spl mitigation incomplete in app tree

- **root cause remains Rust-seed-only** (global struct/class registry not
  module-scoped) and is out of .spl scope; the pinned seed must not be patched.
- **.spl mitigation state by inspection**: the lib tree rename landed —
  `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl:42` defines
  `class RunnerTestDb` and exports it (line 458), and
  `test_db_core.spl:34` defines `struct RunnerTestDbCore`.
  BUT the app tree was never renamed (or was resurrected by the 2026-09 tree
  transplant 88aac2ffe28): `src/app/test_runner_new/test_db_compat.spl:30`
  still defines `class TestDatabase` and `src/app/test_runner_new/test_db_core.spl:19`
  still defines `struct TestDatabase` — the same class+struct same-name pair
  this entry's "Second collision" section claims was fixed with "0 leftovers".
  Users `test_db_migrate.spl:6` / `test_db_perf.spl:5` import
  `app.test_runner_new.test_db_core.{TestDatabase, ...}`, and
  `test_runner_helpers.spl:12` / `doc_generator.spl:15` import
  `std.test_runner.test_db_compat.{TestDatabase, ...}` (the flattened `std.`
  alias family in `src/compiler/00.common/source_root_resolution.spl` maps
  `std.test_runner` to the lib tree, which no longer exports `TestDatabase` —
  a dangling import the seed appears to tolerate).
- **verification limit**: the aggregate repro
  (`bin/simple.exe test test/01_unit/os/smf`) cannot run at release/1.0.0 HEAD —
  the pinned seed rejects `@representation_boundary` repo-wide
  (`src/app/test_runner_new/test_runner_client.spl:9`), so whether the
  post-run phase still dies could not be executed. Classified SKIP for this
  pass: the root cause is seed-only, and a blind app-tree rename across 7+
  files cannot be executably verified in this environment.
- **follow-up**: rename the app-tree `TestDatabase` class/struct cluster to
  match the lib tree (`RunnerTestDb` / `RunnerTestDbCore`) once a binary that
  accepts `@representation_boundary` is available to verify the aggregate run.

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

