# `bin/simple test <spec>` emits no pass/fail summary and exits 0 (silent green)

- **Date:** 2026-08-17
- **Status:** FIXED (seed fix pending redeploy; shell guard live)
- **Severity:** HIGH — a spec that never runs is indistinguishable from a spec
  that passes, on the command every session uses as its evidence.

## Symptom (measured)

```
$ nice -n 15 bin/simple test test/01_unit/lib/common/text_advanced_case_conversion_spec.spl
... 1897 lines, all of them warnings ...
$ echo $?
0
```

`grep -E 'Total|Passed|Failed|Suite|[Ss]cenario|assert'` over the captured
stdout+stderr returns **one** line, and it is an unrelated `export use` warning
quotation — there is no result line of any kind. Same shape for
`test/unit/lib/common/text_advanced_case_class_generalization_spec.spl`.

The output that *is* produced is entirely diagnostic noise: `export use *`
lint warnings, `compiler_cross_module_private_symbol_collision` warnings for
`dir_remove_all` / `file_read_bytes` / `shell` / `DebugConfig`, and a
`higher_layer_runtime_family` gc-warning.

## Why this matters

Exit 0 with no summary is read as GREEN by every caller — humans and scripts
alike. Any claim of the form "spec X passes" that was established by running
`bin/simple test X` and checking the exit code is unsupported until this is
fixed. Note the binary here is the Rust seed (`bin/simple` prints the
bootstrap-seed warning), so this may be a seed-only dispatch gap rather than a
defect in the pure-Simple runner.

## Expected

Either a result summary (counts of scenarios run / passed / failed) with a
non-zero exit on failure, or an explicit `ERROR — nothing was run` with a
non-zero exit. A run that executed zero assertions must never exit 0.

## Root cause (2026-08-17, two independent causes)

**1. The observed symptom is a SIGTERM kill, not a runner code path.**
`test` dispatches to the pure-Simple app `src/app/test_runner_new/main.spl`
(`src/compiler_rust/driver/src/main.rs:524-530`); the seed interprets that
module graph, which takes longer than 60s of CPU on a loaded box. The kill
monitor (`scripts/resource/kill_simple_monitor.shs`, `KILL_SIMPLE_MIN_AGE_SECS`
default 60) then SIGTERMs it. Confirmed in `/tmp/kill_simple_monitor.log`:
`Killing runaway process ... (cpu=99.5% age=60s>=60s: bin/simple test ...)`.
The process dies before printing even the `Simple Test Runner v...` header —
so the only output is the compile warnings, all of which go to **stderr**. A
direct shell sees exit **143** (measured); a pipeline or wrapper that launders
`$?` shows the reported **0**. Re-running with `SIMPLE_TIMEOUT_SECONDS=3600`
(read live from the victim's `/proc/<pid>/environ`) lets the run finish and a
real verdict appears. The pure-Simple runner itself is already fail-closed on
an empty selection (`classify_test_run_result` +
`test_empty_selection_is_success`, `test_runner_main.spl:1066`).

**2. A genuine latent silent green in the seed's Rust runner path.**
`TestRunResult::success()` was literally `self.total_failed == 0`
(`src/compiler_rust/driver/src/cli/test_runner/types.rs:369`). A run with zero
passed, zero failed, zero skipped, zero listed satisfied it and exited 0 with
no counts. That path is reached whenever the Rust handler runs.

## Fix

- `types.rs`: added `executed_nothing()`; `success()` now also requires the run
  to have produced at least one verdict. Unit-tested (vacuous run and
  skipped-only run).
- `test_output.rs`: text and doc summaries print
  `ERROR — nothing was checked: 0 examples executed across N file(s)`; JSON
  gains an `executed_nothing` field.
- `main.rs`: a zero-example run exits **2** (ERROR), never 0. Run-management
  subcommands, which produce no examples by design, keep their own exit path.
- `scripts/check/check-test-verdict-not-silent.shs`: new fail-closed gate,
  repo verdict convention (PASS/FAIL/ERROR as the last stdout line, ERROR on 0
  targets), fatal 4-fixture `--selftest`. It rejects "exit 0 with no verdict
  line" as a silent green and classifies a signal-killed run as ERROR — which
  is what actually catches cause 1, since a killed process runs no code.

The `types.rs`/`test_output.rs`/`main.rs` fix lands in the **Rust seed** and
only takes effect after a seed rebuild + redeploy, which is blocked (see
`.claude/rules/bootstrap.md` KNOWN BLOCKER). It is proved by
`cargo check --release --bin simple` (clean, isolated `CARGO_TARGET_DIR`) plus
the added unit tests — not by a green run of the deployed binary. The shell
guard is effective **immediately** and needs no redeploy.

## Verification

```
$ SIMPLE_TIMEOUT_SECONDS=3600 sh scripts/check/check-test-verdict-not-silent.shs \
    test/01_unit/lib/common/text_advanced_case_conversion_spec.spl \
    test/unit/lib/common/text_advanced_case_class_generalization_spec.spl
  ERROR  test/01_unit/lib/common/text_advanced_case_conversion_spec.spl
  OK  test/unit/lib/common/text_advanced_case_class_generalization_spec.spl
ERROR — nothing was checked for 1 of 2 target(s): test/01_unit/...conversion_spec.spl
rc=2
```

Neither repro spec can be read as green any more: one produces a real verdict,
the other is loudly ERROR at exit 2.

## Spec coverage, and what could not be covered

- `test/01_unit/app/test_runner/silent_green_verdict_spec.spl` — reproducing
  spec: the reported shape (warnings only, exit 0) must be rejected; a run that
  prints counts must be accepted.
- `test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl` —
  generalization over the defect class: zero-examples, loader failure with no
  summary, SIGTERM kill, honest red, zero targets.

Spec run results (`SIMPLE_TIMEOUT_SECONDS=3600 bin/simple test <spec>`):

```
SPEC FILE VERDICT: .../silent_green_verdict_spec.spl declared>=2 executed=2 passed=2 failed=0 dropped=0
Results: 2 total, 2 passed, 0 failed          EXIT=0

SPEC FILE VERDICT: .../silent_green_class_generalization_spec.spl declared>=5 executed=5 passed=5 failed=0 dropped=0
5 examples, 0 failures
Results: 37 total, 5 passed, 32 failed        EXIT=1
```

**Separate, newly-observed defect — the aggregate line over-counts.** The
generalization spec's five examples all pass (`✓` on each, per-file verdict
`failed=0`, per-describe `5 examples, 0 failures`), yet the aggregate reports
`37 total, 5 passed, 32 failed` and `error: test-runner: spec failed`. The 32
have no `✗` anywhere in the log — this is the documented harness-plumbing
signature (trailing subprocess/warning text miscounted as failed examples;
`.claude/skills/spipe.md` § "A `Results:` FAIL can be harness plumbing").
Sanitizing the guard's own verdict words out of the subprocess output did not
change the count, so the source is the runner's own trailing stream, not the
spec. This direction is fail-CLOSED (over-reporting, exit 1) and therefore not
a silent green, but it is a real defect and should be filed separately. The
authoritative line for these two specs is the per-file `SPEC FILE VERDICT`.

**Not coverable from inside a spec:** an example cannot observe the exit code
or the summary stream of the very runner process that is executing it — by the
time the summary is printed and the status chosen, every example has already
finished. Both specs therefore drive the shell guard as a subprocess with
fixture runners, which is the closest in-spec approximation; the guard's own
`--selftest` is the fail-closed backstop.
