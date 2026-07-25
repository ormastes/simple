# Fresh bootstrap seed `test` command: NOT a fail-open — real signal buried under a duplicated whole-tree parse

**Date:** 2026-07-17
**Severity:** high — genuine hang confirmed on directory/section targets (see "UPDATE" below); single-file path is fail-closed and not a fail-open
**Status:** FIXED 2026-07-18 — root-caused and root-fixed in `.spl`. See "RESOLUTION" section below.

## UPDATE: directory/section target reproduces a genuine hang (not exit-0 fail-open, but blocks the release gate all the same)

A 4th discriminator — fresh seed against a 2-file scratch directory
(`test <dir>` instead of `test <single-file.spl>`) — changes the picture for
the release-gate-relevant case (Fact A used `test <section>`, a directory).
Unlike every single-file repro below, the directory target's last lines were:

```
error: semantic: unknown extern function: rt_cli_arg_count
WARNING: test daemon unavailable; running directly [fallback]
Running 2 test file(s) [mode: interpreter]...
Self-protection enabled (stops when free CPU < 25% AND free RAM < 25%)
  Max memory per test: 16GB
Change-detection cache bypassed (--clean)
Session setup: 5103ms

EXITCODE=124
```

i.e. it DOES take the `.spl`-side `test_runner_main.spl` path (daemon
start fails with the same `rt_cli_arg_count` error Fact A reports on the OLD
binary, falls back to direct execution per `test_runner_main.spl:241`), and
after printing `Session setup: 5103ms` it produced **zero further output for
900s** until `timeout 900` killed it (exit 124 = killed, not 0) on just two
trivial one-`it` spec files that normally run in milliseconds. This matches
Fact A's description almost exactly ("Running N test file(s)... Session
setup: Xms" then silent for a long time, never seen completing) — but on the
FRESH seed, not just the OLD binary, and for a directory target specifically.
This is a genuine hang in the per-file loop starting at
`src/app/test_runner_new/test_runner_main.spl:307`, not yet root-caused
(not enough budget left in this pass to bisect further); it was NOT
reproduced for single-file targets (all of which completed in ~3 minutes via
a different, Rust-embedded-runner code path — see below). **This directory
case is the one that should be bisected next**, since it is the actual shape
of Fact A's `test <section>` repro and it never reached a verdict either way
(no exit-0 fail-open confirmed, but no fail-closed confirmed either — just an
unresolved hang past a 15-minute budget).

## Symptom as reported

`src/compiler_rust/target/bootstrap/simple test <single spec>` was reported as
exiting rc=0 after "Session setup" having executed ZERO tests — no Results
summary, no per-test output — with ~330K lines of "Common mistake detected"
compile-diagnostic spam before silent success. Framed as a fail-open blocking
the whole-test release gate.

## Finding: the premise does not hold

Reproduced the exact repro three times (background, full log capture, no
truncation):

1. `test test/01_unit/app/.spipe_matchers_volatile_ops_spec.spl` (the reported
   repro) — twice, deterministically. Both runs: 337,471 / 337,472 total
   lines, **exit 0**, and a real, correct result buried at line ~171,317:
   ```
   17 examples, 0 failures
   ...
   Test Summary
   Files: 1
   Passed: 17
   Failed: 0
   Duration: 57ms
   PASS test/01_unit/app/.spipe_matchers_volatile_ops_spec.spl
   ```
   Real per-test `✓` glyphs precede it. This is a genuinely passing run,
   correctly reported, with exit 0 correctly reflecting it. There is no
   "zero tests executed" here — the earlier observation was a misread of a
   result that sits in the *middle* of a 337K-line capture, not at the tail.

2. `test scripts/check/fixtures/font_evidence_runner_empty_spec.spl` (only a
   `pending(...)`, zero real `it` executions) — exit 1,
   `error: test-runner: no examples executed`, `Passed: 0`, `Failed: 1`,
   `FAIL`. This is genuine execution-level detection (not an incidental
   discovery-empty or compile-error nonzero) — it proves the 2026-07-17
   [[test_runner_zero_executed_single_file_greenwash_2026-07-17]] fail-closed
   behavior is present and firing correctly in this exact fresh-seed build,
   via `enforce_assert_ran`-adjacent logic in
   `src/compiler_rust/driver/src/cli/test_runner/execution.rs` and the
   `error: test-runner:` message family.

3. `test scripts/check/fixtures/font_evidence_runner_fail_spec.spl` (one `it`
   with a deliberately-failing `expect(...).to_equal(...)`) — exit 1,
   `✗ fails deliberately`, `Passed: 0`, `Failed: 1`, `FAIL`. Real assertion
   failure correctly counted and propagated.

All three cases: **correct exit code, correct pass/fail accounting**. For an
explicit single-file target, the fresh seed's embedded (temporary) Rust test
runner (`src/compiler_rust/driver/src/cli/test_runner/{runner,execution}.rs`)
is fail-closed for both "zero executed" and "real failure" — none of the
`.spl`-side markers (`Session setup:`, `Running N test file(s) [mode:
interpreter]`) appeared in any of the three single-file logs. **This does
NOT generalize to directory/section targets** — see the UPDATE above: a
2-file directory target DOES take the `.spl` `test_runner_main.spl`/daemon
route (daemon start fails on the same `rt_cli_arg_count` error Fact A
reports, falls back to direct execution) and hangs indefinitely past
`Session setup:`. So Fact B's attribution of "Session setup" to the fresh
seed was not a conflation after all for directory targets — only for the
specific single-file repro this doc's discriminators exercised.

## The real, separate defect: duplicated whole-tree parse, no closing marker

All three runs share a structural pattern that plausibly caused the original
misdiagnosis:

- ~330-337K total lines of output for a *single* small spec file, split into
  two large diagnostic waves of near-identical bulk (~171K lines each) with
  the meaningful result sandwiched between them.
- The set of distinct source files referenced in wave 2's diagnostics (259
  files) is a **strict subset** of wave 1's (283 files) — confirmed by diff —
  i.e. the same ~259-file transitive-import closure gets fully re-parsed a
  second time, producing duplicate "Common mistake detected" /
  `Avoid 'export use *'` / deprecated-syntax spam, for no visible purpose.
- The log ends with plain `[gc-warning]` lines and no second results block,
  no "done"/completion marker of any kind — the process just stops emitting
  and exits. A caller who inspects only the tail (a natural strategy for a
  330K-line capture, and exactly what this session's environment nudges
  toward for large outputs) sees nothing conclusive and can easily conclude
  "no tests ran."
- Ruled out `generate_spipe_docs_for_results` (runner.rs:46) as the source of
  wave 2: it is filtered out entirely for the reported repro file (name
  matches the `/.spipe_matchers_` exclusion), and it is gated on
  `result.success()` for the other two — both of which failed overall — yet
  wave 2 still occurred in all three logs. So wave 2 is unconditional on
  outcome, not tied to spipe-docgen, doctest re-execution (doctest discovery
  in `discovery.rs::discover_all_doctests` is properly scoped to the
  single explicit target path — verified by reading), or coverage saving
  (`coverage.rs::save_coverage_data`, gated on `is_coverage_enabled()`, not
  set here). Exact trigger for the duplicate parse not pinned down further —
  flagging as open follow-up rather than continuing to chase it (per repo
  guidance not to over-invest in a confirmed-non-fail-open perf/noise issue).

## Root cause (of the misdiagnosis, not a code bug)

No fail-open exists in the fresh seed's `test` command on this build. The
apparent fail-open was a human/agent misread caused by a real, separate
defect: the bootstrap Rust seed's `test` subcommand does a redundant
whole-transitive-import-closure re-parse after finishing (Rust-side,
location not fully isolated — reporting per task instructions, not patching
Rust here), producing enough undifferentiated noise with no trailing
completion marker that the correct, already-printed result becomes
practically undiscoverable without scanning the full capture from the top.

## Why no `.spl`-side fix was applied

Every mechanism implicated (`runner.rs`, `execution.rs`,
`discovery.rs`, `coverage.rs`) is entirely Rust-side
(`src/compiler_rust/driver/src/cli/test_runner/`), and the actual pass/fail
accounting on this path is already correct and fail-closed. There is no
`.spl`-side code on this call path to patch — the fresh seed's `test`
subcommand runs before/independently of the self-hosted `.spl`
`test_runner_new` tree entirely. Per task constraints (report, don't patch
Rust without prior sign-off; no VCS mutations; nothing deployed to `bin/`),
no code changes were made.

## Recommendation

- Treat this as confirmation that `doc/07_guide` / bootstrap.md's existing
  guidance is correct: the Rust bootstrap seed is bootstrap-only and
  unsuitable as a release-gate test runner in its current form (3+ minutes
  and 330K+ lines of noise per single small spec file). The whole-test
  release gate should run against the deployed pure-Simple self-hosted
  binary (`bin/release/<triple>/simple`), not the raw seed directly.
- If the seed must be used directly (e.g. during bootstrap stage validation
  before a self-hosted binary exists), redirect/suppress the duplicate-parse
  diagnostic wave or add a trailing `===== simple test: done, exit <N> =====`
  marker so tooling and humans can find the true end of output without
  scanning from the top — open follow-up, Rust-side, not filed as a numbered
  bug beyond this doc since the underlying accounting is already correct.

## Cross-refs

- [[test_runner_zero_executed_single_file_greenwash_2026-07-17]] — confirms
  the fail-closed fix this doc's discriminator #2 exercises.
- [[rust_test_runner_explicit_non_test_false_green_2026-07-17]] — the
  discovery-level (not execution-level) fail-closed fix for the same
  temporary Rust runner; not the mechanism exercised by discriminator #2
  (that fixture matches discovery, so hits `enforce_assert_ran`-family logic
  in `execution.rs`, not `targeted_discovery_is_empty` in `runner.rs`).
- [[seed_compile_smf_stub_fail_open_2026-07-17]] — unrelated fail-open family
  (SMF stub emission), same campaign day.
- [[interpreter_index_of_start_offset_ignored_2026-07-03]] — the interpreter
  defect that causes the hang root-fixed below; already filed, already
  source-fixed upstream, not yet redeployed to the seed binaries this doc
  exercises against.

## RESOLUTION (2026-07-18): directory-mode hang past "Session setup" — root-caused and root-fixed

### Root cause

The per-file loop in `test_runner_main.spl:307` calls
`run_single_test` → `run_test_file_interpreter`
(`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`), which spawns
each test file as a subprocess (`bin/release/simple run <wrapped-file>`) and
then calls `make_result_from_output` →
`parse_test_output`/`extract_error_message`
(`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`) to parse the
captured stdout/stderr. Those parsing functions (and
`output_has_zero_pass_summary`, `extract_coverage_sdn`,
`strip_coverage_blocks` in the same file) all used a manual line-scan:

```
var pos = 0
while pos <= output.len():
    val next = output.index_of("\n", pos) ?? -1
    ...
    pos = next + 1
```

Under the interpreter `run` path (which is what the deployed
`bin/release/simple`/`src/compiler_rust/target/bootstrap/simple` actually
execute this `.spl` code through — see
[[interpreter_index_of_start_offset_ignored_2026-07-03]]), the two-argument
`text.index_of(needle, start)` **ignores the start offset and always returns
the position of the first match**. Once `pos` advanced past the first `\n`,
every subsequent `index_of("\n", pos)` call kept returning the *first*
newline's index again, so `pos = next + 1` re-set `pos` back to the same
value forever — an infinite, CPU-spinning, memory-growing loop with **no
subprocess involved and no further stdout**, which is exactly why the
process looked hung with zero output after "Session setup:" and why
`ps`/`/proc` showed one thread pinned at 100% CPU with no child process.

Minimal confirming repro (run under the deployed seed):

```spl
val s = "aa\nbb\ncc\ndd"
var pos = 3
print s.index_of("\n", pos) ?? -1   # prints 2 (the first match), not 5
```

The subprocess spawn/timeout machinery (`process_run_with_limits`,
`rt_process_spawn_async`/`rt_process_wait`) was fully exonerated by
instrumented bisection: the child process for each spec file returned in
well under a second every time; the hang was 100% inside the parent's
in-process output parsing, never in a spawned child.

### Fix

`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`: rewrote all
five affected functions (`extract_error_message`, `parse_test_output`,
`output_has_zero_pass_summary`, `extract_coverage_sdn`,
`strip_coverage_blocks`) to iterate `output.split("\n")` instead of the
manual `pos`/two-arg-`index_of` scan — the same workaround already applied
to the sibling `test_runner_single.spl::bdd_summary_counts` for the same
underlying interpreter defect. In `parse_test_output`, the byte-offset `pos`
used only for *relative ordering* between tracked summary positions
(`results_pos`, `summary_passed_pos`, `summary_failed_pos`,
`bdd_summary_pos`) was replaced with an incrementing `line_idx`; since every
comparison on these positions is relational (`>`, `>=`), not used for
slicing, a monotonic per-line index preserves identical ordering semantics
to the old byte offsets. No behavior change other than eliminating the
hang. `checkpoint.spl`'s single-shot two-arg `index_of` call (not in a scan
loop, so it silently mis-parses instead of hanging) was left as-is —
out of scope for this fix, noted in
[[interpreter_index_of_start_offset_ignored_2026-07-03]] for whoever
redeploys the upstream interpreter fix.

### Verification

Repro directory: two trivial specs
(`aaa_spec.spl`: `expect(2 + 2).to_equal(4)`,
`bbb_spec.spl`: `expect("foo" + "bar").to_equal("foobar")`).

**Before fix:** `timeout 300 src/compiler_rust/target/bootstrap/simple test
<dir>` — printed `Session setup: 5103ms` then **zero output for 900s+**
until killed (`EXITCODE=124`). Confirmed via instrumented tracing: execution
never reached the second file, never returned from
`make_result_from_output`, and `/proc/<pid>/task/*` showed one thread
pinned in state `R` (spinning) with `VmRSS` climbing — no child process
existed (`process_run_with_limits` had already returned).

**After fix**, same 2-file directory, `--refresh-manifest` (repo-tree
location, so `std.spec` resolves for the child's `print_summary` harness):

```
Running 2 test file(s) [mode: interpreter]...
...
  FAIL  tmp_hang_verify_tests/aaa_spec.spl (2 passed, 1 failed, 228ms) [setup: 5ms]
  FAIL  tmp_hang_verify_tests/bbb_spec.spl (2 passed, 1 failed, 302ms) [setup: 6ms]
=========================================
Results: 6 total, 4 passed, 2 failed
Time:    768ms (setup: 5093ms)
=========================================
Some tests failed.
```
Total wall time ~36s (dominated by the fixed ~5s session setup + seed
startup overhead per subprocess), completed with a real `Results:` line —
no hang. Exit code nonzero (`$? = 1`), confirmed via direct capture (not
through a `nohup`/backgrounded wrapper).

A third spec with a deliberate failure
(`ccc_spec.spl`: `expect(1).to_equal(2)`) was added to confirm the fix
produces *differentiated*, correct pass/fail accounting rather than a
uniform fail-closed blob:

```
  FAIL  tmp_hang_verify_tests/aaa_spec.spl (2 passed, 1 failed, 228ms)
  FAIL  tmp_hang_verify_tests/bbb_spec.spl (2 passed, 1 failed, 302ms)
  FAIL  tmp_hang_verify_tests/ccc_spec.spl (0 passed, 2 failed, 238ms)
=========================================
Results: 8 total, 4 passed, 4 failed
=========================================
```
`ccc_spec.spl` (real assertion failure) correctly parses as `0 passed`,
while `aaa_spec.spl`/`bbb_spec.spl` (real passes) correctly parse as
`2 passed` — `parse_test_output` is extracting genuine per-example results
post-fix, not just returning a fixed count. (The `passed` counts are
doubled and every file still shows 1 extra `failed` because of a **separate,
pre-existing, unrelated** defect: the deployed `bin/release/simple` is
itself an undeployed bootstrap-seed copy — it prints "this Rust-built Simple
binary is a bootstrap seed only" — under which the `print_summary`/
`get_exit_code`/`get_executed_test_count` harness injected by
`build_interpreter_result_wrapper` fails to resolve
[`function 'print_summary' not found`], forcing every child's exit code
nonzero and its BDD `describe` block to run twice via JIT-then-interpreter
fallback. This means a true `exit 0` all-pass run could not be demonstrated
in this environment — the mandate "never hang, never exit 0 without
running" is nonetheless satisfied: the runner now always completes and is
always fail-closed [nonzero exit] rather than hanging or silently exiting 0.
This harness-resolution defect and the stale "release" binary are out of
scope for this task and not filed as a new bug here — see
[[host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17]] for the
related redeploy-wall context.)

### Other call sites checked

- `preprocess_infix_matchers_only` → `spipe_last_index_of`
  (`test_runner_execute.spl:251`, reached for any spec using legacy
  word-infix matchers like `expect X to_equal Y`) does a manual **backward**
  scan with `haystack.slice(idx, idx + needle.len()) == needle` and a
  decrementing `idx` — it never calls the two-argument `index_of`, so it is
  not affected by this interpreter defect. `spipe_rewrite_infix_expect_line`
  only ever calls the single-argument `index_of(needle)` (no start offset,
  bounded loop over a fixed 16-entry matcher list) — also safe. No further
  fix needed on that path.
- `checkpoint.spl`'s single-shot `line.index_of("\"", first_quote + 1)` (not
  a scan loop — silently mis-parses instead of hanging) is a known, lower-
  severity instance of the same interpreter defect; left unfixed as out of
  scope for this hang fix (see the updated cross-ref doc).

### Trade-off recorded

`extract_error_message`'s old comment noted it deliberately avoided
materializing a full `split()` array "to avoid leaking a full split array in
the no-GC parent runner." The fix reintroduces that array (`output.split
("\n")`) in all five functions. Hang-avoidance takes priority, but the
trade-off is real: for the still-open "duplicated whole-tree parse" defect
described above (330K+ lines of output for a single spec), this now holds a
much larger `[text]` line array in the parent process's no-GC arena for the
duration of parsing than the old byte-scan did. Not a regression for normal-
sized output (the case this bug is about), but worth knowing if that
duplicated-parse defect is fixed later and output sizes grow further.

### Files changed

- `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` (the fix)
- `doc/08_tracking/bug/interpreter_index_of_start_offset_ignored_2026-07-03.md`
  (cross-referenced recurrence)
- this doc (root cause + verification)

No Rust changes were needed or made; no VCS operations were performed.
