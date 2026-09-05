# `simple test a.spl b.spl` silently runs ONLY the first spec and exits 0 — a failing second spec is dropped

**Status:** fixed 2026-08-01 (runner-fix lane)
**Severity:** high (fail-open in the test runner itself)
**Found:** 2026-08-01
**Lane:** vacuous-spec audit (found) / test-runner multi-path (root-caused + fixed)
**Engine:** `bin/simple_seed test` — PROVED. That binary runs the
**tree-walking interpreter**, so every result below is interpreter evidence
only. No spec runs on the JIT or native lanes today, because the deployed
`bin/simple` has no `test` subcommand at all (`error: unknown command 'test'`,
exit 1 — PROVED).

## Symptom

When more than one spec path is passed on the command line, the runner executes
only the first and reports a summary covering that one file. The remaining paths
are neither run nor reported, and the exit code reflects only the first spec.

A failing spec passed as the second argument is therefore invisible: the command
exits **0**.

## Reproduction (PROVED)

Two probe specs, one green and one red:

    # ctrl_pass_spec.spl
    describe "control":
        it "passes":
            expect 1 to_equal 1

    # ctrl_fail_spec.spl
    describe "control":
        it "fails":
            expect 1 to_equal 2

Each alone behaves correctly:

    $ simple_seed test test/_probe/ctrl_pass_spec.spl
    rc=0   Results: 1 total, 1 passed, 0 failed
    $ simple_seed test test/_probe/ctrl_fail_spec.spl
    rc=1   Results: 1 total, 0 passed, 1 failed

Both together:

    $ simple_seed test test/_probe/ctrl_pass_spec.spl test/_probe/ctrl_fail_spec.spl
    rc=0   Results: 1 total, 1 passed, 0 failed
    per-file lines emitted:  PASS test/_probe/ctrl_pass_spec.spl

`Files: 1`. The failing spec produced no PASS/FAIL line at all — it was not run,
not skipped-with-notice, not counted.

## Why this matters beyond ergonomics

Any wrapper, script, or CI step that batches spec paths onto one `simple test`
invocation reports GREEN while silently testing a single file. This is the same
class of defect as a vacuous spec — a green signal that covers nothing — but it
lives in the runner, so it can hide arbitrarily many real specs at once.

## Root cause — TWO independent latches, not one (PROVED)

It is neither `argv[1]`-only parsing, an early loop `break`, nor an
overwriting result aggregator. It is a **"first positional wins" latch on a
scalar path field, with no `else` arm**, so arguments 2..N match no branch and
fall out of the parser with zero diagnostics. The same mistake exists twice, on
complementary input shapes, and the driver routes between them:

`src/compiler_rust/driver/src/main.rs:235` `test_should_use_light_daemon_client`
sends the invocation to the client when **any** positional ends in `.spl`,
otherwise to the main runner. So:

1. **`.spl` file targets → `src/app/test_runner_new/test_runner_client.spl`.**
   `parse_client_run` latched on `path == ""`, keeping only the first path, and
   `main()` forwarded only that one path into the light-daemon request
   (`light_request_encode(run.path, …)` — the protocol carries a single path).
   *This is the latch the reproduction above hits.*
2. **Directory / non-`.spl` targets → `parse_test_args`**
   (`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:532`), whose arm read
   `elif not arg.starts_with("-") and not path_explicit:`. Once the first
   positional set `path_explicit`, every later positional reached the end of the
   `elif` chain and was discarded silently. `TestOptions.path` was a scalar
   `text`, and discovery only ever saw that one value.

## Fix

- `test_runner_client.spl` — `ClientRun` gains `paths: [text]`; every positional
  is collected and **each** is validated (`.spl` suffix + existence) rather than
  only the first; `main()` loops over all of them, one daemon request per path
  (request ids gain a sequence suffix so two fast iterations cannot collide),
  and aggregates: any non-zero spec fails the run, and the loop does **not**
  stop at the first failure.
- `test_runner_args.spl` / `test_runner_types.spl` — `TestOptions` gains
  `paths: [text] = []`; the positional arm accumulates instead of latching.
- `test_runner_main.spl` (both the `src/app/test_runner_new/` and
  `src/lib/nogc_sync_mut/test_runner/` copies) — new
  `discover_all_requested_files()` unions discovery across all targets,
  de-duplicating with `contains_key` + bracket assign only (`Dict.len()`/`.get()`
  are unreliable under native codegen).

## Fail-closed accounting (non-vacuity PROVED)

`count_positional_args()` counts positional arguments **independently** of
`parse_client_run`. `main()` compares that count against the number of paths
actually parsed and against the number actually executed, and fails on either
mismatch. Per-target discovery counts are printed so a target contributing zero
files is visible in the log instead of silent.

This guard was proved non-vacuous by **reintroducing the latch** and re-running
the repro:

    ERROR: dropped spec path(s) while parsing arguments: 2 requested, 1 parsed
    exit 1

The identical sabotage under the old code exited **0** silently.

## Verification (all `bin/simple_seed test` = tree-walking interpreter)

| Case | Before | After |
|---|---|---|
| pass.spl alone | 0 | 0 |
| fail.spl alone | 1 | 1 |
| pass.spl fail.spl | **0**, second spec absent from output | **1**, both specs present, `Requested 2 spec file(s); executed 2.` |
| fail.spl pass.spl | — | **1**, both present (no stop-at-first-failure) |
| two directories | second dir dropped at parse time | both reported with per-target counts |

Single-path runs are byte-for-byte unchanged in behaviour and emit no extra
output (the accounting line is printed only when more than one path is given).

## Blast radius — how much verification was fictional

Repo-wide sweep with `/usr/bin/grep` (not ugrep):

- **0** invocations in `scripts/**`, `.github/workflows/**`, `bin/`, `tools/`,
  `config/` pass more than one path. All 91 shipped invocations pass exactly one
  path or one directory, so **CI and the check scripts were never affected**.
- **40 documentation lines** show multi-path or multi-glob invocations and have
  therefore been documenting — and in one case claiming as evidence — runs that
  only ever executed their first file. Concentrated in
  `doc/10_metrics/coverage/*` (stale coverage reports),
  `doc/09_report/2026/**`, and `doc/07_guide/testing/*`. The one real evidence
  claim is
  `doc/03_plan/app/spipe/sspec_traceability_reorg_plan.md:226`, which cites a
  two-spec invocation as verification — that evidence is void.
- **4 guard specs are vacuous**: `test/01_unit/app/cli_dispatch_unit_spec.spl:157`
  ("parses multiple file paths") and
  `test/01_unit/app/tooling/command_dispatch_spec.spl:501`, plus their
  `test/unit/` duplicates, assert on a locally-constructed array and never
  invoke the runner. That is why a bug this loud survived: the spec named after
  the exact behaviour never exercised it.

## Related fail-opens (same family, still open)

- `bin/simple lint` emits a file-level `PARSE001` that discards every other
  diagnostic in that file.
- ~70 of 92 `scripts/check/**` scripts are fail-open.
- `simple compile` invoked by absolute path exits 0 without compiling.
- The default JIT exits 0 while printing "whole module dropped to the
  interpreter".
