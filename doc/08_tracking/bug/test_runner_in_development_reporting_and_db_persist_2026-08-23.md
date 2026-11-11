# In-development reporting mislabels neutralised specs, breaks total conservation, and never persists to the test DB

Date: 2026-08-23
Lane: spectriage-1
Status: FIXED (D1/D3/D4 fixed and D2 addressed by separate "In development:" summary line per 2026-11-03/2026-11-06 re-probes; header flipped 2026-11-11 runner10 lane on re-verified in-tree evidence — see addendum)
Engine: Rust seed `bin/release/x86_64-unknown-linux-gnu/simple`, 60650360 bytes, mtime 2026-08-23 04:47
(copied from `simple-main`; identical to the engine the phase-1 sweep ran on)

## Positive result first (the part that WORKS)

The policy "every spec ends PASSING or explicitly not-yet-implemented" is
expressible in this tree today. It does NOT need new machinery:

  * `@tag:in-development` (`src/lib/nogc_sync_mut/spec/in_development.spl`) is
    the established mechanism, and it is fully WIRED — `test_runner_main.spl:23,831,876`,
    `test_runner_single.spl:1264`, `src/app/stats/test_status.spl`, and a
    `simple tag-query` CLI that counts the tagged set.
  * `update_test_database` (`test_runner_helpers.spl:229`) already checks
    `file_result.in_development > 0` FIRST and writes `TestStatus.InDevelopment`,
    with an in-source comment naming the exact greenwash this bug class is about.
    **That documented trap is already fixed.** Verified by reading; NOT verified
    end-to-end, because of defect D4 below.
  * The suite summary line distinguishes all three states and conserves:
    `States: 1 passed, 1 failed, 1 in development (expected to fail)` (1+1+1 = 3 files).

## Fixture (reproduces all four defects)

Three specs, one per state — a passing one, one tagged `# @tag:in-development`
whose single example fails, and one plain failing one.
Exit status read DIRECTLY into a variable, never through a pipe (a pipeline's
`$?` is `tail`'s status and produced a false green on the first attempt here).

Explicit-path runs behave EXACTLY as `in_development.spl` documents:

    a_pass  rc=0  SPEC FILE VERDICT ... outcome=OK    executed=1 passed=1 failed=0 skipped=0 dropped=0
    b_indev rc=1  SPEC FILE VERDICT ... outcome=ERROR executed=1 passed=0 failed=1 skipped=0 dropped=0
                  IN-DEVELOPMENT EXPLICIT ... explicit-path run reports the honest verdict
    c_fail  rc=1  SPEC FILE VERDICT ... outcome=ERROR executed=1 passed=0 failed=1 skipped=0 dropped=0

The suite run over the same three files is where it goes wrong:

    PASS  triage/fix/a_pass_spec.spl (1 passed, 1741ms)
    FAIL  triage/fix/c_fail_spec.spl (0 passed, 1 failed, 1 skipped, 1550ms)
    IN-DEVELOPMENT NEUTRALISED triage/fix/b_indev_spec.spl (1 expected failure(s), verdict neutralised)
    PASS  triage/fix/b_indev_spec.spl (0 passed, 1 skipped, 566ms)
    SPEC FILE VERDICT: b_indev_spec.spl outcome=NOT_RUN declared>=0 executed=0 passed=0 failed=0 dropped=0
    Results: 2 total, 1 passed, 1 failed, 2 skipped
    States:  1 passed, 1 failed, 1 in development (expected to fail)

## Defects

**D1 — a not-yet-implemented spec prints `PASS`.** The per-file line for the
neutralised file reads `PASS triage/fix/b_indev_spec.spl (0 passed, 1 skipped)`.
It passed nothing. This is the greenwash shape the in-development module was
written to prevent, surviving in the per-file stream: the `States:` line is
right and the line a human actually scans is wrong. `(0 passed, 1 skipped)` with
a `PASS` label is also self-contradicting on its own terms.

**D2 — `Results:` total does not conserve.** Three files ran; the line says
`2 total`. `passed + failed = 2 = total`, so the in-development file is excluded
from the denominator while its skip is still counted in `2 skipped`. This is the
"a count moved between addends" failure mode: a conservation check of the form
`passed + failed + other == total` stays green while the total silently shrank.
Any pass RATE computed from this line is inflated — 1/2 = 50% instead of 1/3.

**D3 — the suite verdict line claims the file never ran.** `outcome=NOT_RUN
declared>=0 executed=0` for b_indev, on the same run whose NEUTRALISED line says
`1 expected failure(s)`, and whose explicit run proves `executed=1`. The two
lines contradict each other in the same output. This one has teeth beyond
cosmetics: `in_development.spl` states that running-and-neutralising (rather than
not running) is what buys back the unexpected-pass promotion signal, and a record
saying `executed=0 passed=0` is exactly the record from which a promotion can
never be observed. The stated purpose of the design is defeated by its reporting.

**D4 — the test DB is never persisted for a suite run, silently.**
After the suite run, `doc/08_tracking/test/test_db.sdn` was UNMODIFIED and an
untracked `doc/08_tracking/test/test_db.sdn.tmp` was left behind (154166 bytes vs
the live 152193). The temp file contains none of the three fixture paths. No
`Warning: Could not load/save test database` was printed — `update_test_database`
returns `Result` and its Err arms do warn, so this failed somewhere that reports
nothing. Consequence for anyone auditing this policy: **per-category numbers must
be taken from the console `States:` line, not from the test DB**, and the
already-correct `TestStatus.InDevelopment` write above cannot currently be
confirmed end-to-end because no row ever lands.

## Twin verdict (cross-implementation rule) — TWIN FOUND, and it DIVERGES

My first draft of this section claimed "N/A, single implementation". **That was
wrong and is corrected here rather than quietly edited away.** A second runner
exists: `src/compiler_rust/driver/src/cli/test_runner/` (9,729 lines).

Verdict: **the two runners disagree about whether `@tag:in-development` exists.**
The Rust seed runner has **zero** references to `in_development` / `in-development`
and emits no `States:` line (verified by grep over the whole `test_runner/` dir and
over `src/compiler_rust/` for the `States:` marker — the only hits are an unrelated
`.spl` docstring and two vendored Windows/ntapi files).

So a spec tagged `@tag:in-development` is:
  * neutralised and counted on its own channel by the pure-Simple runner, but
  * an ordinary RED failure to the Rust seed runner.

Severity, stated honestly rather than inflated: the Rust runner is **not the
default**. `driver/src/main.rs:163` gates it behind
`temporary_rust_test_runner_override(env SIMPLE_TEST_RUNNER_RUST)`, and the file's
own header (`main.rs:14-41`) calls it a temporary pre-port path mapped
one-for-one onto `src/app/test_runner_new/**`. `bin/simple test` used the
pure-Simple runner in every fixture run above — that is why `States:` appeared at
all. So this is an **opt-in legacy path that is in-development-blind**, not a
break in the default lane.

Consequence that still matters for this policy: any lane invoking the runner with
`SIMPLE_TEST_RUNNER_RUST` set will see every in-development spec as a plain
failure, and the "PASSING or explicitly not-yet-implemented" invariant will not
hold there. Filed as the other half: the tag must either be honoured by the Rust
runner or that runner must refuse to run a tree containing tagged specs rather
than silently reporting them red.

## Why not fixed here

The four print sites live in `test_runner_main.spl`, which the evidence bar for
this lane cannot cheaply satisfy: a fix needs a reproduce spec failing pre-fix
plus similar-shape neighbours, and the runner's own console output is not
spec-able from inside a spec run without a harness-in-harness. The pure module
(`in_development.spl`) IS easily spec-able and is NOT where the bug is — it
computes the right classification; the runner mis-renders it.
D4 is the one worth fixing first: it is where "distinguishable in the reported
numbers" actually has to live.

## Prevention shape (not yet implemented)

A gate asserting, on the three-spec fixture above, that (a) no line labelled
`PASS` names a file that also produced an `IN-DEVELOPMENT NEUTRALISED` line,
(b) `Results: <n> total` equals the number of files run, and (c) a neutralised
file's verdict line reports `executed>=1`.

## Re-probe 2026-11-03 (tr-sspec lane, bin/simple.exe test on 3-file fixture)
D1 FIXED: neutralised file prints `IN-DEVELOPMENT SKIP ...`, no `PASS` line for it.
D3 FIXED: verdict line is `outcome=OK executed=1 ... in_development=1` (test_runner_main.spl:1034-1042).
D2 PARTIAL: `Results: 2 total, 1 passed, 1 failed, 1 skipped` - total is passed+failed
(test_runner_output.spl:638-640); the in-dev file shows only as `skipped`. No `States:` line seen on
this run. D4 (test_db.sdn never persisted) NOT re-verified. Remains OPEN: next step is to add
in-development to `total` (or print it as its own addend) in test_runner_output.spl and verify D4.

## Round 8 part 2 note 2026-11-06
Seed re-probe (3-file fixture, Windows): D4 FIXED - test_db.sdn is rewritten and test_result.md shows `In Development | 1`. D2: `Results:` keeps example semantics; added a separate `In development: N file(s) expected to fail ...` line (`in_development_files_line`, test_runner_output.spl). Spec: test/01_unit/app/test_runner_new/in_development_files_line_spec.spl 2/2.

## 2026-11-11 — runner10 lane verdict: FIXED (header flip on re-verified in-tree evidence)

The 2026-11-03 re-probe fixed D1 (`IN-DEVELOPMENT SKIP` line, no `PASS`
greenwash) and D3 (verdict `outcome=OK executed=1 ... in_development=1`);
the 2026-11-06 round-8 note fixed D4 (test_db.sdn rewritten, test_result.md
shows `In Development | 1`) and addressed D2 by adding a separate
`In development: N file(s) expected to fail` summary line instead of
changing `Results:` example semantics. The header above those addenda still
said OPEN — flipped now.

Re-verified fresh at base 79d5af6723f6 (campaign no-rerun rule; prior-lane
greens not re-executed; this lane's spec run died with its session):

- `src/lib/nogc_sync_mut/test_runner/test_runner_output.spl:715-722` —
  `in_development_files_line` produces exactly the documented line
  ("In development: {n} file(s) expected to fail (neutralised; not counted
  in Results: total)"), wired into the suite printer at :665. (The 2026-11-06
  note attributed the function to `src/app/test_runner_new/test_runner_output.spl`;
  at this base it lives in the lib module the app re-exports — feature
  present as described, file attribution drifted.)
- `src/app/test_runner_new/test_runner_main.spl:1028,1048,1562` —
  `in_development_skip_line` per-file print, `in_development` count carried
  into the file result, and `print_in_development_summary` — the D1/D3 fixes
  are in-tree.
- `test/01_unit/app/test_runner_new/in_development_files_line_spec.spl` —
  the 2-example spec from the 2026-11-06 note is tracked at this base
  (imports `in_development_files_line` from `std.test_runner.test_runner_output`).

All four defects (D1 greenwash line, D2 total conservation via the separate
addend line, D3 executed=0 lie, D4 silent DB non-persist) are fixed as
documented by the 2026-11-03/2026-11-06 probes and confirmed present at this
base. The Rust opt-in runner's in-development blindness (the twin-divergence
paragraph) remains a known limitation of a non-default lane, recorded here
for a runner-owner lane; it does not affect the default pure-Simple runner.
