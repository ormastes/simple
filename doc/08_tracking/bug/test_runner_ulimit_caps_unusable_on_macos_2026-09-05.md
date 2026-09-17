## 2026-09-16 re-verification (macOS sweep)

**Command:** `bin/simple test test/01_unit/app/office/sheets/` on macOS aarch64 (M4).
`bin/simple` resolves to `src/compiler_rust/target/bootstrap/simple` (Rust seed,
rebuilt 2026-09-14; reports `Simple Language v1.0.1-beta.1`) — the expected
toolchain. Run to completion in the background (~12.8 min wall clock, loaded
host); not killed early.

**Outcome (verbatim tail):**
```
Files:   79 discovered, 79 executed
Results: 1176 total, 778 passed, 398 failed, 397 skipped, 1 timed out (unverified)
Time:    768362ms (setup: 13151ms)
Some tests failed.
EXIT_CODE=124
```

**Exit code: 124 (oracle requires 0 → RED). Status: OPEN.**

**Blocker status this run.** None of the three recorded blockers reproduced:
(1) no `ulimit: virtual memory: ... Invalid argument` — only the advisory
`[resource-scope] address-space cap ... NOT enforced: RLIMIT_AS ...` line per
bounded spawn; (2) no `timeout: fork system call failed: Resource temporarily
unavailable` — the per-UID `ulimit -u 64` cap did not bite on this host today;
(3) no `spipe_empty_examples` lint false positive — specs compiled/ran and
produced real assertion output (files that cannot compile to standalone SMF
degraded to the interpreter lane via the documented mcdc-fallback). The runner
is therefore usable on macOS now; the reds below are GENUINE spec failures
(missing formula functions/methods), not runner infrastructure.

**Failing specs (verbatim `FAIL` lines, 47 files, plus 1 timeout):**
```
  FAIL  test/01_unit/app/office/sheets/formula_avariants_spec.spl (11 passed, 13 failed, 13 skipped, 6605ms)
        Error: ✗ AVERAGEA averages {10,0,1,20} = 7.75 (text is 0, TRUE is 1) -- expected #ERR: Unknown function: AVERAGEA to equal 7.75
  FAIL  test/01_unit/app/office/sheets/data_ops_spec.spl (15 passed, 5 failed, 5 skipped, 4716ms)
        Error: semantic: function `sheet_autofilter` not found; semantic: function `sheet_autofilter` not found; semantic: function `sheet_autofilter` not found
  FAIL  test/01_unit/app/office/sheets/formula_eng2_spec.spl (5 passed, 9 failed, 9 skipped, 5496ms)
        Error: ✗ aliases ERF.PRECISE / ERFC.PRECISE to ERF / ERFC -- expected false to equal true
  FAIL  test/01_unit/app/office/sheets/formula_lambda_helpers_spec.spl (7 passed, 8 failed, 8 skipped, 6619ms)
        Error: ✗ MAP(1:3, LAMBDA(x, x*2)) with A1:A3=[1,2,3] spills to C1:C3 -- expected 0 to equal 6
  FAIL  test/01_unit/app/office/sheets/formula_matrix_spec.spl (14 passed, 6 failed, 6 skipped, 6291ms)
        Error: ✗ MDETERM of a 2x2 matrix -- expected #ERR: Unknown function: MDETERM to equal -14
  FAIL  test/01_unit/app/office/sheets/chart_spec.spl (11 passed, 4 failed, 4 skipped, 6118ms)
        Error: semantic: function `_stacked_sheet` not found; semantic: function `_stacked_sheet` not found; semantic: function `_stacked_sheet` not found
  FAIL  test/01_unit/app/office/sheets/formula_db_spec.spl (1 passed, 2 failed, 2 skipped, 5038ms)
        Error: ✗ aggregates rows matching the criteria range -- expected #ERR: Unknown function: DMIN to equal 50
  FAIL  test/01_unit/app/office/sheets/formula_xlookup_arrays_spec.spl (16 passed, 4 failed, 4 skipped, 7932ms)
        Error: ✗ XLOOKUP finds an exact needle and returns the aligned value -- expected #ERR: Unknown function: XLOOKUP to equal 20
  FAIL  test/01_unit/app/office/sheets/formula_text_spec.spl (0 passed, 5 failed, 5 skipped, 7142ms)
        Error: ✗ CONCAT joins refs and string literals -- expected #ERR: Unknown function: CONCAT to equal hello World
  FAIL  test/01_unit/app/office/sheets/formula_ref2_spec.spl (10 passed, 17 failed, 17 skipped, 13274ms)
        Error: ✗ shifts down one row: OFFSET(A1,1,0) = 20 -- expected #ERR: Unknown function: OFFSET to equal 20
  FAIL  test/01_unit/app/office/sheets/formula_subtotal_fin_spec.spl (19 passed, 24 failed, 24 skipped, 9474ms)
        Error: semantic: method `hide_row` not found on type `Sheet`; semantic: method `hide_row` not found on type `Sheet`; semantic: method `hide_row` not found on type `Sheet`
  FAIL  test/01_unit/app/office/sheets/number_format_spec.spl (35 passed, 18 failed, 18 skipped, 9285ms)
        Error: semantic: function `format_text_with_code` not found; semantic: function `format_text_with_code` not found; semantic: function `format_text_with_code` not found
  FAIL  test/01_unit/app/office/sheets/fill_series_spec.spl (9 passed, 4 failed, 4 skipped, 3386ms)
        Error: ✗ detects a step of 2 from 1,3
  FAIL  test/01_unit/app/office/sheets/validation_spec.spl (18 passed, 1 failed, 1 skipped, 5051ms)
        Error: semantic: undefined field: unknown property or method 'ok' on Tuple
  FAIL  test/01_unit/app/office/sheets/formula_compat_alias_spec.spl (1 passed, 10 failed, 10 skipped, 9549ms)
        Error: ✗ range-based statistical aliases match their legacy base -- expected #ERR: Unknown: MODE to equal 20
  FAIL  test/01_unit/app/office/sheets/query_spec.spl (13 passed, 6 failed, 6 skipped, 6799ms)
        Error: semantic: function `cell_matches_criteria` not found; semantic: function `cell_matches_criteria` not found; semantic: function `compare_cells_for_sort` not found
  FAIL  test/01_unit/app/office/sheets/sheet_visibility_spec.spl (0 passed, 12 failed, 12 skipped, 2569ms)
        Error: semantic: method `hide_row` not found on type `Sheet`; semantic: method `hide_row` not found on type `Sheet`; semantic: method `hide_row` not found on type `Sheet`
  FAIL  test/01_unit/app/office/sheets/sheet_merge_spec.spl (20 passed, 1 failed, 1 skipped, 6084ms)
        Error: semantic: method `hide_row` not found on type `Sheet`
  FAIL  test/01_unit/app/office/sheets/sheets_app_hidden_row_nav_spec.spl (0 passed, 6 failed, 6 skipped, 7001ms)
        Error: semantic: method `hide_row` not found on type `Sheet`; semantic: method `hide_row` not found on type `Sheet`; semantic: method `hide_row` not found on type `Sheet`
  FAIL  test/01_unit/app/office/sheets/formula_eng_date_spec.spl (15 passed, 5 failed, 5 skipped, 7909ms)
        Error: ✗ DEC2BIN / DEC2OCT / DEC2HEX render integers in the target radix -- expected #ERR: Unknown function: DEC2BIN to equal 0
  FAIL  test/01_unit/app/office/sheets/formula_let_probe_spec.spl (1 passed, 3 failed, 3 skipped, 6346ms)
        Error: ✗ later values can use earlier bindings -- expected #ERR: Unknown function: LET to equal 2
  FAIL  test/01_unit/app/office/sheets/formula_circular_recalc_spec.spl (2 passed, 4 failed, 4 skipped, 7043ms)
        Error: ✗ a mutually-circular pair reports #CIRC! on both cells, not a number -- expected 33 to equal #CIRC!
  FAIL  test/01_unit/app/office/sheets/sync_spec.spl (14 passed, 4 failed, 4 skipped, 8923ms)
        Error: semantic: method `hide_row` not found on type `Sheet`; semantic: method `hide_row` not found on type `Sheet`; semantic: method `hide_row` not found on type `Sheet`
  FAIL  test/01_unit/app/office/sheets/formula_text_logic_spec.spl (0 passed, 16 failed, 16 skipped, 11764ms)
        Error: ✗ SUBSTITUTE replaces all or a chosen instance -- expected #ERR: Unknown function: SUBSTITUTE to equal abcxbc
  FAIL  test/01_unit/app/office/sheets/math_bridge_extended_spec.spl (18 passed, 5 failed, 5 skipped, 5094ms)
        Error: ✗ ROUND handles negative numbers
  FAIL  test/01_unit/app/office/sheets/cond_format_spec.spl (21 passed, 8 failed, 8 skipped, 11240ms)
        Error: ✗ data_bar computes proportional bar percentage over the range -- expected  to contain 33%
  FAIL  test/01_unit/app/office/sheets/formula_datetime2_spec.spl (42 passed, 14 failed, 14 skipped, 14209ms)
        Error: ✗ parses the Excel docs example 2:24 AM as 0.1 -- expected false to equal true
  FAIL  test/01_unit/app/office/sheets/formula_locale_text_spec.spl (4 passed, 32 failed, 32 skipped, 13573ms)
        Error: ✗ should convert full-width ASCII characters -- expected #ERR: Unknown function: ASC to equal ABC
  FAIL  test/01_unit/app/office/sheets/formula_let_spec.spl (7 passed, 13 failed, 13 skipped, 11598ms)
        Error: ✗ LET(x, 5, x*2) = 10 -- expected #ERR: Unknown function: LET to equal 10
  FAIL  test/01_unit/app/office/sheets/math_bridge_significance_sign_class_spec.spl (1 passed, 5 failed, 5 skipped, 4163ms)
        Error: ✗ FLOOR is invariant under negating the significance
  FAIL  test/01_unit/app/office/sheets/formula_ifs_stats_spec.spl (7 passed, 5 failed, 5 skipped, 12197ms)
        Error: ✗ SUMIFS sums the value range where all criteria match (value range first) -- expected #ERR: Unknown function: SUMIFS to equal 15
  FAIL  test/01_unit/app/office/sheets/math_bridge_comprehensive_spec.spl (28 passed, 2 failed, 2 skipped, 7417ms)
        Error: ✗ EVEN rounds up to even integer
  FAIL  test/01_unit/app/office/sheets/formula_lookup_spec.spl (1 passed, 2 failed, 2 skipped, 10303ms)
        Error: ✗ VLOOKUP finds by first column and returns the indexed column -- expected #ERR: Unknown function: VLOOKUP to equal 20
  FAIL  test/01_unit/app/office/sheets/formula_forecast_pivot_spec.spl (6 passed, 20 failed, 20 skipped, 21164ms)
        Error: ✓ errors on field/item not found
  FAIL  test/01_unit/app/office/sheets/formula_isomitted_spec.spl (0 passed, 2 failed, 2 skipped, 8860ms)
        Error: ✗ LAMBDA(x, y, IF(ISOMITTED(y), x, x+y))(5) = 5 -- expected #ERR: Unknown function: LAMBDA to equal 5
  FAIL  test/01_unit/app/office/sheets/formula_dist2_spec.spl (3 passed, 11 failed, 11 skipped, 10684ms)
        Error: ✗ I_x(a,b) hits hand-computed points through BETADIST/BETA.DIST -- expected #ERR: Unknown: BETA to start with 0.6875
  FAIL  test/01_unit/app/office/sheets/formula_spill_origin_spec.spl (2 passed, 4 failed, 4 skipped, 9736ms)
        Error: ✗ SUM over a SEQUENCE(2,2) spill totals 10 (origin contributes 1, not 0) -- expected 9 to equal 10
  FAIL  test/01_unit/app/office/sheets/formula_dist_spec.spl (3 passed, 1 failed, 1 skipped, 8918ms)
        Error: ✗ parses ISO and US date text to the DATE serial -- expected #ERR: Unknown function: DATEVALUE to equal 46206
  FAIL  test/01_unit/app/office/sheets/formula_complex_spec.spl (2 passed, 2 failed, 2 skipped, 10202ms)
        Error: ✗ formats and parses Excel-style complex text -- expected #ERR: Unknown function: IMAGINARY to equal -5
  FAIL  test/01_unit/app/office/sheets/formula_criteria_spec.spl (0 passed, 3 failed, 3 skipped, 8857ms)
        Error: ✗ COUNTIF counts text equality and numeric comparisons -- expected #ERR: Unknown function: COUNTIF to equal 1
  FAIL  test/01_unit/app/office/sheets/formula_textinfo2_spec.spl (4 passed, 19 failed, 19 skipped, 10644ms)
        Error: ✗ formats with default 2 decimals and thousands grouping -- expected #ERR: Unknown function: DOLLAR to equal $1,234.57
  FAIL  test/01_unit/app/office/sheets/data_ops2_spec.spl (0 passed, 15 failed, 15 skipped, 8543ms)
        Error: semantic: function `sheet_remove_duplicates` not found; semantic: function `sheet_remove_duplicates` not found; semantic: function `sheet_remove_duplicates` not found
  FAIL  test/01_unit/app/office/sheets/formula_text_fmt_spec.spl (0 passed, 3 failed, 3 skipped, 10097ms)
        Error: ✗ rounds decimals and groups thousands like Excel -- expected #ERR: Unknown function: TEXT to equal -1,235
  FAIL  test/01_unit/app/office/sheets/formula_text2_spec.spl (8 passed, 28 failed, 28 skipped, 14479ms)
        Error: ✗ TEXTBEFORE returns the text before the first delimiter -- expected #ERR: Unknown function: TEXTBEFORE to equal red
  FAIL  test/01_unit/app/office/sheets/formula_calc_basics_spec.spl (0 passed, 1 failed, 1 skipped, 9819ms)
        Error: ✗ recalculates multiplication and both average spellings in a real sheet -- expected #ERR: Unknown function: AVG to equal 7
  FAIL  test/01_unit/app/office/sheets/formula_chain_order_spec.spl (3 passed, 3 failed, 3 skipped, 20042ms)
        Error: ✗ a chain PAST the old recursion bound no longer caps at 33 -- expected 33 to equal 60
  FAIL  test/01_unit/app/office/sheets/formula_card14_spec.spl (7 passed, 12 failed, 12 skipped, 12785ms)
        Error: ✗ matches the Excel documentation worked example to 6 digits -- expected false to equal true
```
Timed out (counted in the summary's "1 timed out (unverified)", not in `failed`):
```
SPEC FILE VERDICT: test/01_unit/app/office/sheets/access_controller_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0 timeout=1 reason=aggregate-lane-timeout budget_ms=124868
```

Follow-up note: the failure classes above (missing `LET`/`XLOOKUP`/`SUBSTITUTE`/`VLOOKUP`/
`SUMIFS`/etc. formula functions, missing `Sheet.hide_row` / `format_text_with_code` /
`sheet_autofilter` / `sheet_remove_duplicates` / `cell_matches_criteria` /
`compare_cells_for_sort` / `_stacked_sheet`, and the one lane timeout) are sheets-feature
and lane-budget gaps, not test-runner cap defects. They belong to the sheets/formula lane
(and possibly a runner lane-budget review for `access_controller_spec.spl`); this record
stays OPEN solely because the stated oracle (`exit 0`) is unmet.

---

# Test runner's ulimit caps make `simple test <dir>` unusable on macOS (2026-09-05)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN (unverified 2026-09-12; re-verified RED 2026-09-16 — see top section)

## Status
PARTIALLY FIXED. Blocker (1) below is fixed in this working tree; blocker (2)
is OPEN and still fails every spec. Blocks the acceptance checkbox
`All formula tests pass (100% coverage)` in BOTH
`test/03_system/plan_acceptance/excel_to_math_lib_migration_spec.spl` and
`..._synthesis_spec.spl` (REQ-EXCEL-MATH-LIB-001 / REQ-EXCEL-MATH-SYN-002),
whose oracle is `<binary> test test/01_unit/app/office/sheets/` exiting 0.

## Measured symptom
```
$ SIMPLE_BINARY=<abs debug seed> <abs debug seed> test test/01_unit/app/office/sheets/
Results: 79 total, 0 passed, 79 failed
```
Every one of the 79 files reports `outcome=ERROR ... executed=1 passed=0
failed=1`. Yet each spec passes when run directly:
```
$ src/compiler_rust/target/debug/simple run test/01_unit/app/office/sheets/math_bridge_spec.spl
15 examples, 0 failures
```
So the 79 reds are the RUNNER, not the specs.

## Blocker 1 (FIXED here): `ulimit -v` is unimplemented on Darwin
`src/lib/nogc_sync_mut/io/resource_scope.spl` built the child's limit prefix as
`ulimit -v <kb> || exit 125; ...`. Darwin's kernel has no RLIMIT_AS, so every
shell rejects it -- verified on this host for both:
```
$ /bin/bash -c 'ulimit -v 1048576 && echo VOK'
/bin/bash: line 0: ulimit: virtual memory: cannot modify limit: Invalid argument
$ /bin/sh -c 'ulimit -v 1048576 && echo VOK'
/bin/sh: line 0: ulimit: virtual memory: cannot modify limit: Invalid argument
```
so `|| exit 125` killed EVERY bounded child with an infrastructure failure,
surfacing as `Error: Compilation failed: /bin/bash: line 0: ulimit: virtual
memory: cannot modify limit: Invalid argument`.

Fix landed: `_rlimit_as_enforceable()` (a single `file_exists` stat on
`/System/Library/CoreServices/SystemVersion.plist`, not a `uname` subprocess,
because this runs once per bounded child spawn) omits ONLY the `-v` clause on
Darwin and emits a loud stderr line naming the unenforceable cap. It does not
fail open silently, and `-t` / `-u` / `-n` keep their fail-closed
`|| exit 125`. Unlike `ulimit -u`, no substitute shell exists for this: it is a
kernel gap, not a shell gap, so a `_limit_shell`-style fallback is impossible.

Verified: the `Invalid argument` failures are gone and the advisory line
appears instead.

## Blocker 2 (OPEN): `ulimit -u 64` is a per-UID cap, not a per-test cap
With blocker 1 fixed the suite still reports 79/79, now with EMPTY stderr
(`Error: Compilation failed: `). Reproducing the runner's own compile step
byte-for-byte shows why:
```
$ /bin/sh -c "ulimit -u 64 2>/dev/null || true; exec timeout --kill-after=5s 65s \
    '<abs debug seed>' 'compile' 'test/01_unit/app/office/sheets/math_bridge_spec.spl' '-o' '/tmp/mb.smf'"
timeout: fork system call failed: Resource temporarily unavailable
rc=125
```
RLIMIT_NPROC is per-UID and counts every process the user ALREADY has, so
capping it at 64 on an interactive workstation (this host's soft limit is 4000,
with hundreds of processes live) makes the very next `fork` fail. The runner
never sees a useful error because `process_ops.spl` writes the ulimit with
`2>/dev/null || true` -- correctly, since the ulimit itself succeeds; the
failure lands later, in `timeout`'s fork, with its stderr classified as an
empty compile failure.

Default: `src/app/test_runner_new/test_runner_args.spl:95` `var max_procs = 64`
(and a hardcoded twin at `test_runner_execute.spl:682`). 64 is only safe inside
a container with a dedicated UID. There is no `--max-procs` flag; the only
escape is `--no-limits`, which drops every cap at once.

### Why this was NOT fixed here
Any repair is a policy change to shared test infrastructure: either raise the
default (which weakens the fork-bomb bound the cap exists for), or make the cap
RELATIVE (current UID process count + budget), which is the semantically
correct fix but needs a process-count probe on the spawn path. Both belong to
the test-runner owner, not to a formula-migration lane. Deliberately left open
rather than papered over.

## Blocker 3 (OPEN, and the DOMINANT one): `spipe_empty_examples` does not
## recognise `assert_*` as a real assertion
With `--no-limits` (every cap dropped, so blockers 1 and 2 are both out of the
way) the suite is STILL `Results: 79 total, 0 passed, 79 failed`, again with
`Error: Compilation failed: ` and empty stderr. `simple test` uses
`run_test_file_native` -- compile-first -- and the compile is what fails:

```
$ src/compiler_rust/target/debug/simple compile test/01_unit/app/office/sheets/math_bridge_spec.spl -o /tmp/mb2.smf
error: compile failed (...): lint: error: SPipe example has no real assertion
       or sanctioned skip [spipe_empty_examples]  --> line 25, column 1
  ... (repeated for every example in the file)
```

The sheets specs assert with `assert_true(...)` / `assert_equal(...)`.
`SPipeChecker::is_assertion_like` (`src/compiler_rust/compiler/src/lint/
checker_spipe.rs:600-615`) recognises only `expect(` / `expect_not(` / the
`to_*(` matchers / bare `expect <subject>`. `assert_*` is absent, so every
example in every one of the 79 files is judged assertion-free and the
deny-level lint fails the compile.

This is a lint FALSE POSITIVE, not a defect in the 79 specs: `assert_true` is
enforcing. Proof --
```
describe "assert_true is a real assertion":
    it "fails on a false condition":
        step("assert a deliberately false condition")
        assert_true(1 == 2)
```
runs to `✗ fails on a false condition`. And the specs themselves are green on
the interpreter path, which does not lint: `simple run
test/01_unit/app/office/sheets/math_bridge_spec.spl` -> `15 examples, 0
failures`.

### Why this was NOT fixed here
`is_assertion_like` lives in the RUST SEED. Repo policy is to fix behaviour in
pure Simple, and a seed edit additionally requires rebuilding
`src/compiler_rust/target/debug/simple` -- the exact binary other concurrent
sessions are using as their verification lane. Adding the `assert_*` family to
the allowlist is the right fix and is a few lines, but it belongs to a
seed/lint lane that can rebuild and re-deploy safely.

## Fix order
Blockers 3, then 2, then (already done) 1. Fixing 1 alone does not move the
`Results:` line; it only replaces one failure mode with the next.

## Related
Matches the previously recorded "Memory limit 16GB lie" class -- a per-UID
`ulimit` misfire being reported as a memory/compilation problem.

