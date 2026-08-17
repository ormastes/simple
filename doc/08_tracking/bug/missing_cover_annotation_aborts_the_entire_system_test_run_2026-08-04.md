# A single system spec without `# @cover` abandons the WHOLE run — 488 specs never execute in three directories (2026-08-04)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-04
**Related — SAME gate, other tiers, found by parallel lanes the same day. Fix
once, close all three:**
`cover_gate_fails_every_system_test_without_running_one_2026-08-04.md`
(`test/03_system/app` — 227 specs) and
`system_cover_gate_reports_791_legacy_feature_specs_as_failures_2026-08-04.md`
(legacy feature tier — 791 specs). This file covers
`test/03_system/{compiler,core,stdlib}` — 488 more specs.
**Class:** harness blind spot. Not a false green (the run does exit non-zero),
but the reported total is 4 instead of 1503, so the operator sees a tiny failure
count where hundreds of specs were silently never started.

## Symptom

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/03_system/stdlib
ERROR: System test(s) missing required # @cover annotation:
  test/03_system/stdlib/database/sdn_checksum_spec.spl
  test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl
  test/03_system/stdlib/simple_db_nvfs_constants_spec.spl
  test/03_system/stdlib/vector_spec.spl
Found 4 system test(s) without # @cover.

Results: 4 total, 0 passed, 4 failed
Time:    0ms
```

`Time: 0ms` is the tell — **nothing ran**. The same directory with the gate
bypassed:

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/03_system/stdlib --no-cover-check
Running 70 test file(s) [mode: interpreter]...
Results: 1503 total, 1440 passed, 63 failed
```

Three directories in the `test/03_system` tier are affected today:

| directory | specs never run | files missing `# @cover` |
|-----------|-----------------|--------------------------|
| `test/03_system/compiler` | 191 | ~20 |
| `test/03_system/core` | 227 | 5 |
| `test/03_system/stdlib` | 70 | 4 |

## Root cause (what is PROVEN)

`src/app/test_runner_new/test_runner_main.spl:191-204` (duplicated verbatim at
`src/lib/nogc_sync_mut/test_runner/test_runner_main.spl:156`):

```
    if not updated_options.no_cover_check:
        val missing_covers = validate_system_test_covers(all_files)
        if missing_covers.len() > 0:
            ...
            return TestRunResult(files: [], total_passed: 0,
                                 total_failed: missing_covers.len(), ...)
```

The gate runs **after** discovery and returns early with `files: []`, so every
discovered spec — annotated or not — is discarded. `validate_system_test_covers`
(`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:151`) flags a file
purely on `extract_cover_annotations(f).len() == 0`; the annotation must be a
`# @cover <path> <N>%` line within the **first 30 lines**
(`test_runner_coverage.spl:579-591`).

The gate itself is fail-closed and loud, which is right. What is wrong is its
**blast radius**: one un-annotated file suppresses hundreds of unrelated specs
in the same directory, and the summary line reports the annotation count as if
it were the test count.

## Why not fixed now

Two candidate fixes, and choosing between them is a policy call, not a local
patch:

1. **Narrow the blast radius (preferred).** Exclude only the un-annotated files
   from `files`, run the rest, and add `missing_covers.len()` to the final
   failure total so the verdict and exit code are unchanged. This keeps the gate
   strict while restoring visibility. It is not a two-line edit: `run_tests` has
   three separate accumulation paths (`test_runner_main.spl:318`, `:544`,
   `:776`) that each build `total_failed` independently, so the extra count has
   to be threaded through all three or it will be dropped on whichever path a
   given invocation takes — and getting that wrong in the shared test runner
   would corrupt every session's verdict in this tree.

2. **Annotate the ~29 files.** Mechanically correct, but the right `@cover`
   target is only unambiguous for the source-grep specs (it is the file they
   read). For several — `native_*_regression_spec.spl`,
   `driver_synthetic_registration_live_spec.spl`,
   `stage4_streaming_live_slope_gate_spec.spl` — the covered component has to be
   decided, and a guessed path writes a false coverage claim into the tree,
   which is worse than the gate. Five of the affected files are
   `test/03_system/core/sys/wm_compare/.spipe_matchers_*_spec.spl`, which sit in
   the WM/browser area this lane was scoped away from.

Note for anyone measuring this tier: **every measurement in this lane required
`--no-cover-check`**, and any historical "0 total" result for
`test/03_system/{compiler,core,stdlib}` should be re-read as "the gate fired",
not "there are no tests".

## Re-confirmed 2026-08-10 — still OPEN, source-level

`src/lib/nogc_sync_mut/test_runner/test_runner_main.spl:154-168` still
contains the unmodified early-return: the gate computes `missing_covers` and,
if non-empty, returns `TestRunResult(files: [], total_passed: 0,
total_failed: missing_covers.len(), ...)` — the exact code quoted in "Root
cause" above, byte-for-byte unchanged. `bin/simple test test/03_system/stdlib`
was re-attempted for a live repro but the currently-deployed `bin/simple` is
the Rust seed (`bin/simple --version` prints the bootstrap-seed warning) and
the invocation did not return within 20-60s, consistent with this repo's
documented seed-hang lore rather than a fresh finding — not used as evidence
either way.

Chose not to land the "narrow the blast radius" fix (option 1) in this pass:
the doc's own analysis is correct that the three accumulation paths
(session-daemon return at `test_runner_main.spl:220`, parallel-mode return at
`:243`, and the sequential loop's own totals) would each need the
`missing_covers.len()` folded into `total_failed` independently, and this file
is the **shared** test runner every concurrent session in this working copy
depends on — a wrong thread-through here corrupts every session's verdict,
not just this investigation's. Given the current shared-WC session load, that
edit needs a dedicated, low-traffic pass with real execution verification
across all three paths, not a fast patch.

**Status stays OPEN.** Classified **ARCHITECTURAL/OUT-OF-SCOPE for this pass**
per the standing mandate: the fix is well-specified (see "Why not fixed now"
above) but requires touching a shared, heavily-depended-on file across three
independent code paths, which is unsafe to do quickly in a shared working
copy. No code changed this pass.

## Re-verified 2026-08-17 (app-rest lane) — still OPEN, and the stated blocker is WEAKER than believed

Content re-check (no SHA/ancestry reasoning used) confirms the defect is live:

- `src/app/test_runner_new/test_runner_main.spl:241-257` still holds the
  unmodified gate. Line 257 is byte-for-byte the early return quoted in "Root
  cause": `return TestRunResult(files: [], total_passed: 0, total_failed:
  missing_covers.len(), ...)`. Discovery has already completed at :236, so the
  discarded `all_files` is the full list.
- The reproducer named in triage, `test/03_system/stdlib/database/sdn_checksum_spec.spl`,
  still has **0** occurrences of `@cover` (`grep -c '@cover'` → `0`), so the gate
  still fires for that directory.
- `validate_system_test_covers` is imported at `test_runner_main.spl:21` from
  `std.test_runner.test_runner_files` — it is **not** defined under `src/app/`,
  so the flagging predicate itself is out of this file's reach.

**Correction to "Why not fixed now" option 1.** That analysis says the extra
count "has to be threaded through all three" accumulation paths or it will be
dropped, and both the 2026-08-04 and 2026-08-10 passes declined the fix on that
basis. The premise is narrower than stated: those three paths are all *internal*
returns of a single function, and that function has exactly **one call site in
the whole tree** —

```
$ grep -rn "run_tests(" src/app/ src/lib/nogc_sync_mut/test_runner/ \
    | grep -v "fn run_tests\|run_tests_parallel_mode\|run_tests_via_daemon\|run_tests_sequential"
src/app/test_runner_new/test_runner_main.spl:1082:        spec_result = run_tests(options)
```

(The other `run_tests` hits — `src/app/test/ci_runner.spl:310`,
`src/app/release/prepare.spl:55`, `cli_run_tests` in `src/app/io/**` — are
unrelated functions with different signatures. `src/lib/nogc_sync_mut/test_runner/test_runner_modes.spl:139`
is commented out.)

So the failure total can be folded **once** at `:1082` rather than three times
inside `run_tests`, which removes the "wrong thread-through corrupts every
session's verdict" hazard that blocked the previous two passes. What genuinely
remains unsolved is *communicating the count outward*: `TestRunResult` has no
field for a non-executed gate failure, so option 1 still needs one of
(a) an added field on the shared `TestRunResult` struct, (b) splitting
`run_tests` into an inner worker plus a thin folding wrapper, or (c) injecting
synthetic failed `TestFileResult` entries at the gate. That is a real design
choice, not a two-line edit — but it is a *smaller* one than this doc has been
recording.

**Not fixed in this pass either, and the reason is host state, not design.**
The lane could not obtain a single `Results:` line to satisfy the mandatory
reproduce-first rule: four spec invocations
(`sdn_checksum_spec`, `mcp_debug_log_tree_stdio_spec`, `mcpgdb_log_modes_spec`,
`model3d_nested_nodes_spec`) were launched under `nice -n 19` via
`scripts/resource/test-slot.shs` and each produced **0 bytes of output after
25+ minutes** while alive in state `SNl`, with the box at load average 346 on
32 cores and 87 concurrent `simple` processes (a live bootstrap plus ~15
parallel lanes). Landing an unverified restructure of the shared test runner
under those conditions is exactly the clobber class the session brief forbids.
**Unblock condition:** re-attempt when load is below ~32 and a
`Results: N total, ...` line can actually be captured before and after.

## Re-verification 2026-08-17 (app-rest lane) — LIVE (by content)

`src/app/test_runner_new/test_runner_main.spl:257` still early-returns before
any spec executes:

    return TestRunResult(files: [], total_passed: 0,
                         total_failed: missing_covers.len(), ...)

This is the same shape as the `TestRunResult::success()` defect called out in
the session brief: a run in which ZERO specs executed is reported through the
normal result type. Verdict: LIVE, P1 retained.
Not proven in this lane: that no outer caller downgrades the early return.
