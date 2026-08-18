# `bin/simple test <spec>` emits no pass/fail summary and exits 0 (silent green)

- **Date:** 2026-08-17
- **Status:** FIXED (seed fix pending redeploy; shell guard live; pure-Simple
  classifier fix RE-VERIFIED 2026-08-18 by independent lane — guard `--selftest`
  PASS (4 fixtures), regression spec `Results: 9 total, 9 passed, 0 failed`
  exit 0, sabotage (unverified early-return removed) reproduced
  `expected unverified, got pass` / `Results: 9 total, 4 passed, 5 failed`
  exit 1, restore byte-exact and green again)
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

### Independent confirmation of cause 1, plus why it is NONDETERMINISTIC (2026-08-17, old-bug-backlog audit)

A second lane reproduced cause 1 from scratch and initially mis-attributed it to
"seed vs self-hosted binary". That model is **wrong** and should not be
inherited: `readlink -f bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` — one 59,536,728-byte file, one
symlink. The kill monitor's matcher is also not path-sensitive
(`is_simple_run_or_test` matches `*/simple:test`, so both spellings match).

Controlled A/B, same binary, same spec, same cwd, only the env differs:

| invocation | result |
|---|---|
| `timeout 200 bin/simple test .../arch_check_spec.spl` | killed at 63s, `error: TIMEOUT: killed by kill_simple_monitor (cpu=97.2% age=63s>=60s)`, exit 143 |
| `SIMPLE_TIMEOUT_SECONDS=600 nice -n 19 bin/simple test <same>` | 2151 lines, `Results: 74 total, 74 passed, 0 failed`, exit 0 |

**The new finding: whether a given run dies is a race, not a property of the
command.** `ps` `pcpu` is a **lifetime average**, and these specs are
compile-heavy early (~100% CPU) then I/O-bound later, so the average *decays*:

| run | wall | user+sys | lifetime avg CPU | outcome |
|---|---|---|---|---|
| A | 111.3s | 83.6s | 75.1% | survived |
| B | killed at 63s | — | 97.2% (sampled) | **killed** |
| C | 114.8s | 79.5s | 69.2% | survived |

`CPU_THRESHOLD=95`, `MIN_AGE_SECS=60`. The guard fires only if the average is
still ≥95% at the first sample after t=60s. For a ~115s unit spec the average
crosses below 95% somewhere around the one-minute mark — i.e. **right where the
guard samples** — so identical commands land on either side of the threshold
depending on machine load. Two monitor instances are running concurrently from
different worktrees (pids 2015 and 929105), doubling the sampling opportunities.

Tuning defect, independent of the seed fix: **`MIN_AGE_SECS=60` is below the
normal runtime of an ordinary unit spec (~115s measured)**, so the guard's
default kills legitimate work rather than runaways. Either raise the default
above the p99 spec runtime or exempt `test` the way `native_build_*.spl` is
already exempted.

Two measurement traps this lane fell into, worth recording because both
manufacture a false "no results" reading from a run that was actually fine:

- **`| tail -6` lands past the summary.** `Results:` sits at line 2103 of 2151
  — 48 lines from EOF, because per-module warnings continue after it. Tailing
  fewer than ~50 lines shows only `[gc-warning]` and reads as "no summary".
  Use `grep -E '^Results:'`, never a small tail.
- **A killed run looks like an empty run.** It is not silent: it prints an
  explicit `error: TIMEOUT: killed by kill_simple_monitor ...` line (that is
  what `notify_victim` exists for) and exits 143. Any report of *silent* exit 0
  should first be checked against `grep kill_simple_monitor` on the capture.

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

## Third cause: the PURE-SIMPLE classifier also passed a verdict-less run (2026-08-17)

The two causes above covered the SIGTERM kill and the Rust seed's
`TestRunResult::success()`. Neither touched the pure-Simple classifier, which
`bin/simple test` actually reaches — `test` dispatches to
`src/app/test_runner_new/main.spl` (`driver/src/main.rs`, the `name: "test"`
`CommandEntry`), and the stdlib is read as SOURCE every run, so this path was
live with no rebuild.

`classify_test_run_result` (`src/lib/nogc_sync_mut/test_runner/test_runner_types.spl`)
only inspected a file result when its `error` was non-empty:

```
for file_result in result.files:
    if file_result.error != "" and file_result.failed == 0:
        return TestRunOutcome.InternalError
if result.total_failed > 0:
    return TestRunOutcome.AssertionOrChildFailure
TestRunOutcome.Pass          # <-- verdict-less run lands HERE
```

A file result with `passed=failed=skipped=pending=0` **and** `error == ""` fell
through to `Pass`, exit 0. That shape is reachable, not hypothetical: on
`TRESP_COMPLETED` the daemon lane builds the result with `error: ""` by
construction (`test_runner_main.spl:844-861` — `error` is populated only for
`TRESP_FAILED`, or `TRESP_CACHED` with failures), so a daemon child that
completed without producing a result line was classified as a pass.

Second, smaller defect in the same function: `TERMINATED:` / `TIMEOUT:` /
`NOT EXECUTED:` all matched the `error != ""` arm and were reported as
`internal_error`. Non-zero, so not a silent green, but it labels **host
interference as a code defect** — exactly the conflation that manufactures
phantom compiler bugs on a box where earlyoom is live.

### Fix

- `TestRunOutcome.Unverified` added, exit code **5** (distinct from 1 failure,
  3 internal error, 4 empty selection, 124 timeout).
- `test_file_result_is_unverified()` added: true for the `TERMINATED:` /
  `TIMEOUT:` / `NOT EXECUTED:` prefixes (frozen names, unchanged) and for the
  zero-examples-with-no-error shape. `CRASHED:` deliberately stays
  `internal_error` — a crash IS a statement about the code.
- The unverified check runs BEFORE the `error != ""` arm, so host kills can
  never be reported as failures.
- `test_runner_main.spl` names every unverified spec (`UNVERIFIED  <path>: ...`)
  and prints `ERROR — nothing was verified: ...`. An unnamed non-zero exit is
  nearly as hard to act on as a silent green.

### Ablation (both arms measured, verbatim)

Spec: `test/01_unit/app/test_runner/no_verdict_is_unverified_spec.spl`.
rc read from a variable on the line after the command, never through a pipe.

Fix applied:

```
RC=0
9 examples, 0 failures
SPEC FILE VERDICT: .../no_verdict_is_unverified_spec.spl declared>=9 executed=9 passed=9 failed=0 dropped=0
Results: 9 total, 9 passed, 0 failed
```

Fix reverted (the unverified early-return removed) — the control DOES fail, and
reproduces the defect in the classifier's own words:

```
RC=1
    assert_equal failed: expected unverified, got pass
    assert_equal failed: expected 5, got 0
    assert_equal failed: expected unverified, got internal_error   (x3)
9 examples, 5 failures
Results: 9 total, 4 passed, 5 failed
```

`expected unverified, got pass` / `expected 5, got 0` is the silent green:
a verdict-less run classified `pass` with exit code 0.

Green-preservation control — a fix that turns real passes into `unverified`
would be worse than the defect, so this was measured too:

```
$ bin/simple test test/01_unit/app/test_runner/args_spec.spl
CONTROL_RC=0
SPEC FILE VERDICT: .../args_spec.spl declared>=92 executed=92 passed=92 failed=0 dropped=0
Results: 92 total, 92 passed, 0 failed
```

92/92 still pass, exit still 0, no `UNVERIFIED` line.

### Still open — NOT fixed here, and a different code path

`exit_code == -1` remains ONE sentinel for both timeout and death-by-signal.
It originates in `app.io.process_ops.process_run_bounded` (consumed at
`test_runner_single.spl:193`; see the comment at `:148`), i.e. the
process-execution layer, not the classifier changed above. Separating those two
outcomes means giving `process_run_bounded` a signal-vs-timeout distinction —
an independent change in a different layer, deliberately not bundled into this
fix. Until then `TIMEOUT:` and a host SIGKILL are both classified `unverified`,
which is at least the correct *class* for both.

## Spec coverage, and what could not be covered

- `test/01_unit/app/test_runner/silent_green_verdict_spec.spl` — reproducing
  spec: the reported shape (warnings only, exit 0) must be rejected; a run that
  prints counts must be accepted.
- `test/01_unit/app/test_runner/silent_green_class_generalization_spec.spl` —
  generalization over the defect class: zero-examples, loader failure with no
  summary, SIGTERM kill, honest red, zero targets.

Rust unit test, with a sabotage arm proving it is not vacuous. Note the test
lives in the **lib** target, not the bin — `cargo test -p simple-driver --bin
simple test_run_result_success` reports `0 passed; 9 filtered out`, which is a
vacuous green if read as a pass. The correct invocation is `--lib`:

```
# fix in place
test cli::test_runner::types::tests::test_run_result_success ... ok
test result: ok. 1 passed; 0 failed; ... 457 filtered out

# sabotage: success() reverted to `self.total_failed == 0`
test cli::test_runner::types::tests::test_run_result_success ... FAILED
panicked at driver/src/cli/test_runner/types.rs:428:9: assertion failed: !vacuous.success()
test result: FAILED. 0 passed; 1 failed

# restored
test cli::test_runner::types::tests::test_run_result_success ... ok
test result: ok. 1 passed; 0 failed
```

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

## Independent re-verification 2026-08-18 (lane SILENTGREEN) — DOES NOT REPRODUCE

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which
prints the bootstrap-seed warning on stderr. All findings below attribute to
the **Rust seed**, and to `bin/simple test` (tree-walk interpreter), not to
`bin/simple run` (Cranelift JIT). Every exit code below was captured on the
line immediately after the command, never through a pipe. No run was killed
(no rc=143/144 observed, so no UNVERIFIED arm needed re-running).

**Arm A — the original reproducer verbatim, no env overrides:**

```
$ nice -n 15 bin/simple test test/01_unit/lib/common/text_advanced_case_conversion_spec.spl
$ echo $?
0
```
105 stdout lines + 241 stderr lines (not 1897), and stdout now carries BOTH
verdict forms:
```
SPEC FILE VERDICT: test/01_unit/lib/common/text_advanced_case_conversion_spec.spl declared>=4 executed=4 passed=4 failed=0 dropped=0
Results: 4 total, 4 passed, 0 failed
```
Exit 0 here is a *justified* green: it is accompanied by an explicit
`Results:` line, which is the property the defect denied.

**Arm B — positive proof that a failing spec is NOT laundered into exit 0.**
Fixture (scratchpad, not committed): one passing and one deliberately failing
example.
```
$ nice -n 15 bin/simple test build/test-artifacts/silentgreen_probe/deliberate_fail_spec.spl
$ echo $?
1
SPEC FILE VERDICT: .../deliberate_fail_spec.spl declared>=2 executed=2 passed=1 failed=1 dropped=0
Results: 2 total, 1 passed, 1 failed
```

**Arm C — the existing regression spec still holds:**
```
$ bin/simple test test/01_unit/app/test_runner/silent_green_verdict_spec.spl
$ echo $?
0
Results: 2 total, 2 passed, 0 failed
```

**Arm D — the fail-closed shell gate is live:**
`sh scripts/check/check-test-verdict-not-silent.shs --selftest` ->
`PASS — selftest only, 4 fixture(s) checked`, exit 0.

Conclusion: the silent-green shape (exit 0 with zero result lines) does not
reproduce on this host today, and both the shell gate and the in-tree
regression spec that would catch its return are present and green. Cause 1
(the kill-monitor SIGTERM race) remains a real, nondeterministic hazard, but
it surfaces as rc=143 — UNVERIFIED — not as a silent exit 0, and is therefore
a separate concern from this defect.
