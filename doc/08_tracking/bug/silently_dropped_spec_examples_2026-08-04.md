# Silently dropped spec examples report green, and `tail -1` misreports the file

**Date:** 2026-08-04
**Status:** FIXED on both the `simple run` and `simple test` paths
**Severity:** Critical — this is a false-green mechanism, not a cosmetic one

## Summary

Two independent defects on the `simple run <spec>` path combined to turn broken
specs into passing ones:

1. **Silent example drop.** When a statement inside a `describe` body aborts at
   registration time, the rest of that group *and every later top-level
   `describe`* are never registered. The run prints an all-green report and
   exits 0. Nothing says examples vanished.
2. **Per-`describe` summary lines.** The `N examples, M failures` line is printed
   once **per top-level `describe`**, and the file-level `spec failure:` line was
   printed **only on failure** and **only to stderr**. So `tail -1` of a spec log
   yielded the *last group's* count, never the file's.

Together: a spec shrinks silently, reports green, and its disappearance is
invisible to every summary-line-based check in the repo.

## Reproduction 1 — silent drop, exit 0 (verbatim)

Fixture: five unconditionally-declared examples, a bare `return` opening the
second `describe` body.

```
describe "alpha":
    it "a1": expect(1).to_equal(1)
    it "a2": expect(2).to_equal(2)
describe "beta":
    return
    it "b1": expect(3).to_equal(3)
    it "b2": expect(4).to_equal(4)
describe "gamma":
    it "g1": expect(5).to_equal(5)
```

Before the fix:

```
$ simple run fix/d_ret.spl ; echo "exit=$?"
alpha
  ✓ a1
  ✓ a2

2 examples, 0 failures
beta

0 examples, 0 failures
gamma
  ✓ g1

1 example, 0 failures
exit=0
```

Five examples declared, **three executed**, `beta` reports `0 examples,
0 failures` **in green**, stderr is empty, exit 0.

## Reproduction 2 — `tail -1` misreports the file (verbatim)

`test/01_unit/app/desugar/trait_scanner_spec.spl`, un-stubbed to its real nine
examples, all of which pass:

```
$ simple run fix/ts_full_spec.spl > log 2>&1 ; echo "exit=$?"
exit=0
$ tail -1 log
3 examples, 0 failures
```

The file ran **9** examples. `tail -1` says **3** — the size of the last
`describe`. This is precisely the "trait_scanner went from 9 examples to 3"
report: the count did not shrink, the *verdict line* was never the file's.

The failure case is no better. On a five-example file where the first group
fails, `tail -1` of stdout is `3 examples, 0 failures` (the passing group) while
the real verdict, `spec failure: 2 of 5 example(s) failed`, went to **stderr**.

Note also that `test/01_unit/app/desugar/trait_scanner_spec.spl` as committed is
a **stub**: its nine real examples are commented out and replaced by a single
vacuous `it "skipped"` asserting that a pending-reason string is non-empty. That
is a separate finding, tracked in its own right.

## Fix

### `parser/src/test_analyzer.rs` — `unconditional_example_floor`

A **strict lower bound** on the examples a file is obliged to execute. It walks
module-level statements and `describe`/`context` bodies **only** — never an
`if`, `for`, `while`, `match`, lambda, or function body.

Deliberately **not** `extract_file_test_meta(..).total_tests`: that descends into
conditionals, so comparing it against the executed count would fire on every
legitimate `if cfg: describe ...` (declared 2, executed 0 — fine) and undercount
loop-generated examples. Skip/pending/ignore forms and `it_behaves_like` (which
expands at runtime to an unknown count) contribute **zero**.

Every example in the floor *must* run on every execution, so `executed < floor`
is arithmetic proof of a drop, not a heuristic.

### `driver/src/cli/basic.rs` — `report_spec_file_verdict`

* Emits **one authoritative line per FILE**, always, on **stdout**, **last**:

  ```
  SPEC FILE VERDICT: <path> declared>=9 executed=9 passed=9 failed=0 dropped=0
  ```

* When `executed < floor`, emits a `DROPPED:` diagnostic to stderr and returns
  exit 1 (never masking a pre-existing non-zero status).

**Contract preservation.** The verdict line deliberately contains neither
`examples, ` nor `failures`. `src/app/test_runner_new/test_runner_single.spl`
*sums* every per-`describe` `N examples, M failures` line it sees, so a
file-level line in that shape would double every count in the repo. The existing
per-`describe` lines, the `spec failure:` line, and `simple test`'s
`Results: N total, M passed, K failed` contract are all untouched.

## Sabotage proof, both directions

```
=== A: unresolvable module path ===
exit=1
error: runtime: Module "app.desugar" does not export 'trait_scanner_BROKEN'
        (already failed closed before this change)

=== B: registration abort — the silent-green case ===
exit=1
SPEC FILE VERDICT: fix/sabB_spec.spl declared>=9 executed=6 passed=6 failed=0 dropped=3
DROPPED: 3 of 9 unconditionally-declared example(s) in fix/sabB_spec.spl never
executed. A describe/it block was skipped — typically a module-load or
registration failure inside a describe body. The examples that did run are NOT a
verdict for this file.

=== RESTORE: pristine file, full count, green ===
exit=0
SPEC FILE VERDICT: fix/ts_full_spec.spl declared>=9 executed=9 passed=9 failed=0 dropped=0
```

Sabotage B is the `trait_scanner` shape exactly, and it is now impossible to
miss: the count is on stdout's last line and the reason is on stderr.

### `driver/src/cli/test_runner/execution.rs` — `enforce_no_dropped_examples`

The same floor applied to the `simple test` path, which is the one the repo's
tooling actually consumes. A file that executed fewer examples than it declares
becomes a **failed file** carrying the `DROPPED:` reason, rather than getting a
new output line — so `Results: N total, M passed, K failed` is unchanged in shape
and a dropping spec simply counts as failed, which is what it is. It runs before
`enforce_assert_ran` so a truncated file cannot satisfy the assert-ran guard with
its survivors.

Verified end to end:

```
$ simple test fix/d_ret.spl        -> exit 1
Results: 8 total, 3 passed, 5 failed
DROPPED: 2 of 5 unconditionally-declared example(s) ... never executed.

$ simple test fix/ok_spec.spl      -> exit 0   Results: 5 total, 5 passed, 0 failed
$ simple test fix/ts_full_spec.spl -> exit 0   Results: 9 total, 9 passed, 0 failed
$ simple test fix/sabB_spec.spl    -> exit 1   DROPPED: 3 of 9 ...
```

## Blast radius

**921 spec files** under `test/01_unit` were run individually with the fixed
binary and produced a verdict line. **Zero** were dropping examples.

Honest scope, because the raw number invites a fabrication: the census walk
attempted 5,776 files, but **4,781 of those returned exit 127 — the binary was
deleted out from under the run by a parallel session's `cargo` invocation**, and
those files were never measured. Only 993 files actually ran (921 verdicts, 34
hard errors, 38 timeouts at 45s). Reporting "5,776 files scanned, 0 drops" would
have been exactly the kind of false green this document exists to close.

So: the drop mechanism is **rare in the committed corpus** — it is not silently
eating examples across the board today. Its danger is that it is *undetectable*
when it does happen, and the repo has a documented history of specs shrinking
without anyone noticing. The guard is cheap insurance, not a mass cleanup.

A separate and much larger finding surfaced while measuring: the committed
`trait_scanner_spec.spl` is a **stub** — nine real examples commented out,
replaced by one vacuous `it "skipped"` that asserts a pending-reason string is
non-empty. That pattern is invisible to the drop guard by construction (a stub
declares one example and runs one example) and needs its own census.

## What was deliberately NOT made to fail

A runner that cries wolf gets worked around, leaving us worse off than before.
None of the following are reported as drops:

* **Conditional generation** — `if cfg:` / `for x in xs:` around a `describe` or
  `it`. Contributes zero to the floor.
* **Runtime expansion** — `it_behaves_like` / `include_examples`. `executed >
  floor` is never a failure.
* **Skipped / pending / ignored examples.** They are recorded as results, so they
  count as executed; and they are excluded from the floor anyway.
* **Non-spec programs.** Floor 0 and no results means no verdict line and the
  program's own exit status is preserved untouched.
* **Files that cannot be read or parsed.** A measurement we could not take is
  never turned into a drop report — the run itself would have failed anyway.

## Adjacent defects observed while measuring (not fixed here)

* `use mod (a, b)` with a symbol removed from the list is a **no-op**: importing
  one symbol registers the whole module, so `scan_traits` stayed callable after
  being deleted from the import list. Import-list narrowing is therefore not
  enforced, and a symbol-removal sabotage cannot fail.
* A `use` of a module that resolves but whose own body has a bad `use` is
  **silently ignored** — no warning at all, exit 0.
* A JIT fallback re-runs the already-executed groups, so a failing spec can print
  its early `describe` blocks **twice**.

## Tests

* `parser/src/test_analyzer.rs` — 6 tests covering the floor: multi-group
  counting, nested `context`, conditional exclusion (asserting `total_tests` = 2
  while the floor = 1), skip/ignore exclusion, `it_behaves_like` exclusion, and
  zero for a non-spec file.
* `driver/src/cli/basic.rs` — 8 tests covering the drop check on the measured
  five-example fixture: floor = 5, drop → exit 1, complete run → 0, all-skipped →
  0, over-execution → 0, non-spec status preserved, real error outranks a drop,
  unmeasurable file invents nothing.
* `driver/src/cli/test_runner/execution.rs` — 8 tests mirroring those on the
  `simple test` path, plus: zero recorded examples is left to `--assert-ran`, and
  an existing failure is not relabelled as a drop.
