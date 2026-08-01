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
  two-spec invocation as verification — that evidence was void. **Corrected
  2026-08-01:** the line now records the original claim as void and cites a
  fresh per-file re-run —
  `test/01_unit/app/stats/benchmark_ledger_spec.spl` 8 examples / 0 failures and
  `test/01_unit/app/stats/inventory_classifier_spec.spl` 9 examples / 0 failures,
  each invoked with a single path. The original conclusion survives
  re-verification, but it was not supported by the evidence originally cited.

  The remaining multi-path documentation lines are **illustrative, not
  evidentiary, and need no correction**: post-fix, a multi-path or multi-glob
  invocation does exactly what those lines say it does, so they are now simply
  accurate. (Re-checked with `/usr/bin/grep`: of the lines matching a two-`.spl`
  invocation, the `doc/03_plan/gui/` hits are false positives — they are
  `simple run src/app/spipe_docgen/main.spl <spec>`, an app plus its argument,
  never a multi-path test run — and the rest sit in `doc/09_report/`,
  `doc/10_metrics/`, `doc/11_archive/` and `doc/08_tracking/`, which are
  temporal or auto-generated trees marked DO NOT refactor.)
- **4 guard specs were vacuous — now de-vacuumed** (see next section):
  `test/01_unit/app/cli_dispatch_unit_spec.spl:157`
  ("parses multiple file paths") and
  `test/01_unit/app/tooling/command_dispatch_spec.spl:501`, plus their
  `test/unit/` duplicates, asserted on a locally-constructed array and never
  invoked the runner. That is why a bug this loud survived: the spec named after
  the exact behaviour never exercised it.

## De-vacuuming the four guard specs (2026-08-01, spec lane — PROVED)

The four examples above asserted on an array literal they had just written
(`val args = ["test", "file1.spl", "file2.spl"]`, then `args[1].ends_with(".spl")`).
No parser was involved, so they passed identically against broken and fixed
code. The `test/unit/` copy of `command_dispatch_spec.spl` was worse still: its
`EDGE: flag in middle of args` example built `args` and then asserted
`val needs_rust = false; expect needs_rust == false`, never reading `args` at
all — a hardcoded tautology.

All four now drive the **shipped** parsers through their established import
seam, so a dropped path is observable:

    use std.test_runner.test_runner_args.{parse_test_args}
    use app.test_runner_new.test_runner_client.{count_positional_args}

Cases covered in each file: two spec paths retained in order; reversed order
retained (no position privileged); two positionals separated by a flag; two
directory targets; single-path parses to exactly one target (the fix must not
invent a phantom second); and `--timeout <v>` consuming its value so the parser
and the fail-closed counter agree.

**Non-vacuity proof — the RED.** The pre-fix latch was reintroduced in a scratch
tree (never landed): `test_runner_args.spl` restored to
`elif not arg.starts_with("-") and not path_explicit:` with the `paths.push(arg)`
accumulation removed, and `parse_client_run` gated with `and paths.len() == 0`.
Under that sabotage **all four specs went RED with 4 failures each**:

    ✗ parses multiple file paths
      semantic: array index out of bounds: index is 1 but length is 1

The pre-existing examples in the same `describe` blocks (`EDGE: flag in middle
of args`, `parses single file path`, `parses glob pattern`) stayed GREEN under
the identical sabotage — a direct demonstration of which assertions were load
bearing and which were not. After restoring the parsers (hash-verified against
the pristine copies) all four specs return to 0 failures:
57 / 111 / 57 / 114 examples, 0 failures.

Engine caveat: run with `simple.pre-segv-fix-20260731` via `run`. That binary
prints `WARNING: this Rust-built Simple binary is a bootstrap seed only`, so
this is **interpreter/seed evidence only**, consistent with the rest of this
report.

## Related fail-opens (same family, still open)

- `bin/simple lint` emits a file-level `PARSE001` that discards every other
  diagnostic in that file.
- ~70 of 92 `scripts/check/**` scripts are fail-open.
- `simple compile` invoked by absolute path exits 0 without compiling.
- The default JIT exits 0 while printing "whole module dropped to the
  interpreter".
- **`simple run <spec>` exits 0 even when examples FAIL** — **FIXED 2026-08-01**,
  see the section below. Minimal repro with `simple.pre-segv-fix-20260731`:

      # probe_exit_spec.spl
      describe "exit code probe":
          it "deliberately fails":
              expect 1 == 2

      $ simple run probe_exit_spec.spl   # output written to a file, not piped
      1 example, 1 failure
      exit 0

  The failure is visible in the report but not in the status, so any caller that
  gates on the exit code of `run` reads GREEN. This is why the RED above is
  evidenced by **failure counts parsed out of the report**, never by exit code.
  Note this is `run`, not `test`; the `test` path exits non-zero correctly.

## `simple run <spec>` exit-code fail-open — root cause and fix (2026-08-01)

**Status:** fixed. **Engine:** reproduced with `bin/simple_seed` (rebuilt today
from origin tip `f93c9b2623`) and with a debug build of the driver at origin tip
`0d2b5ff20`. Both self-identify as `WARNING: this Rust-built Simple binary is a
bootstrap seed only` — so this is **interpreter evidence only**. No spec on this
path reaches the JIT or native lanes.

### Root cause (PROVED)

Shape: *the run path reports results but never propagates a failure count into
the process exit.* Not an unconditional-success aggregator, and not a count
computed after the exit decision — the count was simply never read.

`cli/basic.rs::run_file_with_args` returned the interpreted module's own exit
code (`Ok(code) => code`). A spec file has no explicit `main`, so the module
returns 0 and the BDD failure state never reached the process status. The
counters existed and had no production consumer:

- `runtime/src/value/bdd_sffi.rs::rt_bdd_format_results()` returns the failure
  total and its doc comment literally says *"Returns the total number of failures
  (for exit code)"*. Zero production callers — only its own unit test.
- `rt_bdd_has_failure()` is registered as a runtime symbol in
  `runtime_sffi.rs` and `runtime_symbols.rs`. Also zero production callers.

There is a second trap that makes the naive fix a *fresh* fail-open: the
`(passed, failed)` pair behind the printed `"N examples, M failures"` line is
`interpreter_call/bdd.rs::BDD_COUNTS`, and it is **reset to `(0, 0)` at the end of
every top-level describe block**. Reading it after the run always yields zero.
The correct source is `BDD_TEST_RESULTS`, which accumulates per-example records
across the whole file — and is already what `simple test` trusts, via
`simple_compiler::interpreter::get_test_results()`
(`cli/test_runner/execution.rs:610`).

This also shows the printed summary itself under-reports: a two-describe spec
with one failure in the second block prints `1 example, 1 failure` (last block
only) while the accumulated record correctly gives `1 of 2 example(s) failed`.

### Fix

`src/compiler_rust/driver/src/cli/basic.rs` — `bdd_example_counts()` +
`bdd_failure_exit_code()`, consuming `get_test_results()`. Fail-closed rules:
no examples ran -> module status untouched (non-spec programs share this path);
any example failed -> exit 1; a non-zero module status is always preserved so a
real error is never masked or downgraded. Skipped examples count as neither.
The failure *mode* is distinguishable via a `spec failure: M of N example(s)
failed (exit 1)` diagnostic on stderr; exit 1 was chosen over a novel code so
`run` and `test` agree and ordinary `if ! simple run x` checks behave.

This composes with `1cfed202c53` (the `count_positional_args()` fail-closed guard
for multi-path `simple test`) rather than duplicating it: that guard is in client
argument parsing, this is in the `run` exit path. **All `simple test` rows of the
matrix below are byte-identical before and after.**

### Invocation x outcome x exit-code matrix (PROVED)

OLD = `bin/simple_seed` at origin tip; NEW = debug driver build with the fix.

| invocation | outcome | OLD | NEW |
|---|---|---|---|
| `run <spec>` | all examples pass | 0 | 0 |
| `run <spec>` | assertion failure (`expect 1 == 2`) | **0** | **1** |
| `run <spec>` | semantic error inside an example | **0** | **1** |
| `run <spec>` | parse error | 1 | 1 |
| `run <spec>` | no examples (plain program) | 0 | 0 |
| `run <spec>` | failure in 2nd of 2 describe blocks | **0** | **1** |
| `test <spec>` | all examples pass | 0 | 0 |
| `test <spec>` | assertion failure | 1 | 1 |
| `test <spec>` | semantic error | 1 | 1 |
| `test <spec>` | parse error | 1 | 1 |
| `test a.spl b.spl` | 2nd path fails | 1 | 1 |

### Newly-visible pre-existing failures — NOT caused by this fix

Sample of the first 60 specs under `test/01_unit`, run via `simple run`,
old binary vs new:

| transition | count |
|---|---|
| `0 -> 0` (still green) | 30 |
| `0 -> 1` (newly RED) | 27 |
| `1 -> 1` (already red: parse errors) | 2 |
| `0 -> 124` (timeout) | 1 |

All 27 newly-RED specs carry the `spec failure:` marker, meaning the **old binary
already printed failures for them and exited 0 anyway**. Spot-checked directly:

    $ simple_seed run test/01_unit/.../branch_coverage_10_spec.spl
    6 examples, 2 failures
    rc=0

So roughly **45% of sampled specs were already failing and `simple run` was
hiding it**. These are pre-existing failures made newly visible, not regressions
introduced here. The single `0 -> 124` case
(`test/01_unit/app/cli/cli_os_spec.spl`) is a 60s timeout under an unoptimised
**debug** build versus a release seed, unrelated to exit-code accounting.

Cost of full enforcement: if the whole spec tree behaves like this sample,
on the order of ~45% of specs would newly report non-zero under `simple run`.
Nothing was weakened to keep them green, and no spec was skipped or retimed.

### Regression coverage, proved RED-before-GREEN

- `cli/basic.rs` unit tests: `bdd_exit_code_is_non_zero_when_any_example_failed`,
  `bdd_exit_code_tracks_failures_across_multiple_describe_blocks`,
  `bdd_exit_code_stays_zero_for_clean_specs`,
  `bdd_exit_code_ignores_programs_with_no_examples`,
  `bdd_exit_code_treats_skipped_examples_as_neither_pass_nor_fail`,
  `bdd_exit_code_never_masks_a_real_error_status`.
- End-to-end: `driver/tests/interpreter_bdd.rs`. Three assertions there read
  `.success()` on specs whose own stdout said `1 example, 1 failure` — they had
  **encoded the fail-open**. Tightened to `.code(1)`:
  `bdd_matcher_pass_after_failure_keeps_example_failed`,
  `bdd_bare_falsy_call_without_matcher_still_fails`, and
  `mutual_recursion_diagnoses_cleanly_instead_of_crashing` (which was using
  `.success()` as a proxy for "not killed by a signal").

Non-vacuity, matching the standard used earlier in this report: sabotaging the
**implementation** (forcing `bdd_failure_exit_code` to always return the module
status) took the 2 new failure-detecting assertions RED while all **7
pre-existing assertions in the same block stayed GREEN**. Restored and
hash-verified; suites then GREEN — `cli::basic` 13/13, `interpreter_bdd` 6/6,
`runner_tests` 51/51.

### Adjacent defect found — root-caused and FIXED 2026-08-01 (matcher-word lane)

`expect <a> to_equal <b>` — the **matcher-word form** — was a silent no-op under
`simple run`. `expect 1 to_equal 2` reported `✓` and `1 example, 0 failures`,
where the operator form `expect 1 == 2` and `raise` both correctly report a
failure. The same spec under `simple test` correctly reports 1 failed, so this is
specific to the `run` path, not to the exit code. It is a second, independent
fail-open of the same family: an exit-code fix cannot rescue an example that was
never scored as failing. Root cause, fix and blast radius are in the section
below.

## `expect <a> to_equal <b>` matcher-word form never scored a failure on `run` (2026-08-01)

**Status:** fixed. **Engine:** debug driver build from origin tip `002015e0f31`.
Every binary on this path self-identifies as `WARNING: this Rust-built Simple
binary is a bootstrap seed only`, so **every result below is interpreter
evidence only** — no spec here reaches the JIT or native lanes. The deployed
pure-Simple `bin/simple` has neither `run` nor `test` (`error: unknown command
'run'`, PROVED), so the seed is the only exercisable spec path today.

### Root cause — the FIRST of the three possible bug classes (PROVED)

It is **not** "parses but never evaluates" and **not** "evaluates but never
records into `BDD_TEST_RESULTS`". The matcher expression **never parsed into an
assertion at all**.

`expect 1 to_equal 2` parsed into **two unrelated top-level statements**, proved
by dumping the AST straight out of `simple_parser::Parser::parse()`:

    Expression(Call { callee: Identifier("expect"), args: [Integer(1)] })
    Expression(Call { callee: Identifier("to_equal"), args: [Integer(2)] })

Statement 1 is a bare `expect(1)` over a truthy literal — passes. Statement 2 is
an orphan call that `interpreter_call/bdd.rs:1439` answers by building a
`Value::Matcher(Exact(2))` and throwing it away. Subject and matcher were never
connected, so nothing was registered and the example could not fail.

`parse_with_no_paren_calls` (`parser/src/expressions/no_paren.rs`) stops the
no-paren argument list after the subject; the statement parser then starts a
fresh statement at the matcher word. The `expect` handler in `bdd.rs:800` only
ever inspects `args[0]`, so even a second argument would have been dropped.

Two corollaries, both confirmed by probe:

- `expect truthy() to_equal 99` **passed** — the matcher is never applied.
- `expect false to_equal true` **passed** — even a literal-false subject passes.
- The failure it *did* sometimes produce was for the wrong reason: a falsy
  *call* subject tripped the unrelated hollow-call heuristic
  (`expected call result to be truthy, got 0`), so `expect xs.len() to_equal 0`
  was a **false RED** while `expect tree.theme to_equal "dark"` was a false
  GREEN. The form was wrong in both directions.
- `expect a to_not_equal b` "failed" only because statement 2 was
  `semantic: function to_not_equal not found` — a loud error, not a scored
  assertion.

### Why `simple test` scored these and `simple run` did not (PROVED)

`simple test` applies a **textual** pre-pass before compiling —
`rewrite_infix_expect_line` (`driver/src/cli/test_runner/execution.rs:954`)
rewrites `expect a to_equal b` into `expect(a).to_equal(b)`, and
`rewrite_method_expect_line` then folds that into `expect (a) == b`. `simple run`
never runs that pre-pass; the raw source goes straight to the parser. The
divergence was a source-text rewrite that only one of the two entry points
performed.

### Fix

- `src/compiler_rust/parser/src/expressions/no_paren.rs` —
  `parse_matcher_word_suffix()` folds `expect <subject> <matcher> <expected>`
  into `expect(<subject>).<matcher>(<expected>)` at the AST level, so both
  entry points now produce the identical tree and the existing (already
  correct) `.to_*()` matcher chain in `interpreter_method/mod.rs` records the
  result. Only the 22 matcher words that chain already knows are folded; any
  other identifier keeps its current meaning and keeps erroring loudly, so
  nothing is silently reinterpreted into a passing assertion.
- `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` —
  `try_lower_bdd_matcher_statement()` lowers the method/matcher form into the
  same `rt_bdd_expect_eq_rv` / `rt_bdd_expect_truthy_rv` builtins the operator
  form uses. Without it the folded form would have emitted **no** BDD assertion
  in compiled mode; this arm also covers the pre-existing
  `expect(a).to_equal(b)` form, which had no BDD lowering at all before.

No matcher table was duplicated: the parser's list is the same list
`interpreter_method/mod.rs` dispatches on, and the HIR mapping mirrors
`rewrite_method_expect_line`.

### Matcher word x `run` outcome matrix (PROVED)

OLD and NEW are both debug driver builds from `002015e0f31`, differing only by
this fix. Exit codes read from a file, never a pipe.

| probe | OLD exit / failures | NEW exit / failures |
|---|---|---|
| `expect 1 == 2` | 1 / 1 failure | 1 / 1 failure |
| `expect 1 == 1` | 0 / 0 | 0 / 0 |
| `expect(1).to_equal(2)` | 1 / 1 failure | 1 / 1 failure |
| `expect(1).to_equal(1)` | 0 / 0 | 0 / 0 |
| `raise "boom"` | 1 / 1 failure | 1 / 1 failure |
| `expect 1 to_equal 2` | **0 / 0 failures** | **1 / 1 failure** |
| `expect 1 to_equal 1` | 0 / 0 | 0 / 0 |
| `expect 1 to_be 2` | **0 / 0 failures** | **1 / 1 failure** |
| `expect "abc" to_contain "zz"` | **0 / 0 failures** | **1 / 1 failure** |
| `expect 1 to_be_greater_than 5` | **0 / 0 failures** | **1 / 1 failure** |
| `expect 5 to_be_less_than 1` | **0 / 0 failures** | **1 / 1 failure** |
| `expect 1 to_not_equal 1` | 1 / `function to_not_equal not found` | 1 / `expected 1 to not equal 1` |
| `expect 1 not_to_equal 1` | 1 / `function not_to_equal not found` | unchanged (not a matcher word) |

Six matcher words were silently unscored; the seventh failed for the wrong
reason. `simple test` rows are unaffected by construction — the fix touches the
parser and HIR, not the test runner's textual pre-pass — and the `test` column
measured before the change was `1` for every failing probe and `0` for every
passing one.

### Regression coverage, proved RED-before-GREEN

`src/compiler_rust/parser/tests/expect_matcher_word.rs` — 4 tests covering the
fold across 10 matcher words, the zero-argument matcher (`to_be_nil`), the
untouched operator and method forms, and the deliberately-unfolded
`not_to_equal`.

Non-vacuity: sabotaging the **implementation** (gating the matcher-word match
arm off inside `parse_matcher_word_suffix`) took the **2 folding tests RED**
while the 2 non-folding tests in the same file and **all 254 + 201 + ... = every
pre-existing test in the other 13 parser test binaries stayed GREEN** (0 failed
in each). Restored from a pristine copy; the suite is green again.

### Blast radius (repo-wide, `/usr/bin/grep` + a Python scan, not ugrep)

Scan of all 35,136 owned `.spl` files (vendor trees excluded) at
origin tip `002015e0f31`:

| measure | count |
|---|---|
| matcher-word assertion lines (`expect <a> <matcher> <b>`) | **4,628** |
| files containing at least one | **157** (all `*_spec.spl`) |
| spec files whose **only** assertions are matcher-word form | **137** |
| `expect(` lines (method/paren form) | 327,572 |
| bare/comparison `expect` lines with no matcher word | 26,352 |

The premise that the matcher-word form is the dominant idiom does **not** hold
at this tip: it is ~1.4% of assertion lines. What is true is that **137 spec
files consist entirely of it and therefore could never fail on the `run`
path** — their green was structural, not earned.
