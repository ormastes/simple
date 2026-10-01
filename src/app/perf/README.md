# Performance Tools

CLI entry point for recording, comparing, and explaining per-test performance
baselines. Pure Simple (`src/app/perf/main.spl`), wired at
`src/app/cli/dispatch/table.spl` and discoverable via
`src/app/cli/command_registry.spl` as the `perf` command.

## Real subcommands (verified 2026-09-05)

```
Usage: simple perf <record|compare|explain|baseline promote> ...
  record <test-path> <cohort-id> <duration-ms>
  compare <test-path> <cohort-id> <candidate-ms> [--confirmed]
  explain <test-path>
  baseline promote <test-path> <cohort-id>
```

- **record** — attach a new duration sample (ms) to a test's baseline history
  for the given cohort.
- **compare** — evaluate a candidate duration against the test's
  `ApprovedBaseline` (`src/lib/common/perf/execution_metrics.spl`) using the
  anomaly policy (10%/3x-MAD warning, 15%/4x-MAD failure, 5ms absolute floor).
  `--confirmed` accepts a flagged regression as intentional.
- **explain** — print the decision status and the samples/thresholds behind
  it for a test path.
- **baseline promote** — move a cohort's provisional/suspect baseline to
  `Approved`.

All state is read through `RunnerTestDb` /
`std.test_runner.test_db_compat` — the SAME `doc/08_tracking/test/test_db.sdn`
the test runner writes, **not** a separate JSON file. This repo uses SDN, not
JSON/YAML, for all config/data — see `.claude/rules/language.md`.

**Known gap (verified 2026-09-05):** on this host `record`/`explain` both
fail with `perf-error: could not open or parse doc/08_tracking/test/test_db.sdn
(existing file is unreadable or migration from
doc/08_tracking/test/test_db_stable.sdn failed)`. The file's own
`#sdn-crc32:` header does not match its body's CRC32 (checked directly), so
this is a genuine stale/corrupt tracked artifact, not a CLI bug. Regenerate
`test_db.sdn` via a full test run (`bin/simple test`, which is itself
bootstrap-only on this host — see `.claude/skills/lib/perf_ladder.md`) before
relying on `perf record`/`compare`/`explain` here.

## Relation to the perf gates

`simple perf` is a manual/ad-hoc workflow for one test at a time. The
automated gates that run on push or on demand are separate and check
different things — see `.claude/skills/lib/perf_ladder.md` for the full
symptom -> gate table:

- `scripts/check/check-perf-regression-tests.shs` — push-tier ADVISORY;
  pins ~191 named performance-fix mechanisms by exact file:needle match
  (source text, not measured wall time).
- `scripts/check/check-startup-perf-budget.shs` — startup wall-time budgets
  from `test/05_perf/startup/budgets.sdn`.
- `scripts/check/check-memory-budget.shs` — RSS/memory budgets.
- `scripts/check/check-lint-cost-budget.shs` — lint wall-time budget.
- `scripts/check/check-cross-language-perf.shs` — cross-language compute
  comparisons.

## Files in this directory

- `main.spl` — the `perf` CLI entry point described above.
- `render_adapter.spl` — bridges perf profiling data to the shared
  `app.ui.render` contract for text/HTML report views; not wired to any
  `perf` subcommand above.

## What was here before (removed 2026-09-05)

This file previously documented `simple perf optimize|profile|benchmark|compare`
and a `profiler.spl`/`benchmark.spl`/`optimizer.spl` module layout with JSON
baseline files (`baseline.json`, `current.json`). None of that exists in
`src/app/perf/` today, and there is no JSON baseline format anywhere in this
CLI's I/O path. Do not resurrect that API from memory or from an old copy of
this file — it was fiction.
