# Bug: legacy word-infix `expect X to_equal Y` not preprocessed on some test paths

**Date:** 2026-06-29
**Severity:** High — produces BOTH false-reds and (worse) silent false-greens.
**Status:** FIXED on the pure-Simple interpreter path (commit: test-runner
preprocess) — `test_runner_execute.run_test_file_interpreter` and the daemon
child `test_runner_single` now rewrite word-infix → method form into a sibling
temp before `simple run`, then delete it. Verified: privilege group/principal/
id_path pass under `bin/simple test` (were false-red); encoding/math_repr/
persistent_map unchanged. NOTE: now-evaluated assertions may expose previously
false-GREEN specs as real failures — re-measure with `bin/simple test`.

**Component:** Rust seed test harness — matcher preprocessing
(`src/compiler_rust/driver/src/cli/test_runner/execution.rs`
`preprocess_matchers_only` / `rewrite_infix_expect_line`) + the dispatch that
`bin/simple test <single-file>` actually takes (NOT `run_test_file`, which DOES
preprocess at lines 534 & 801 — single-file `test` reaches neither).

## What

`expect <expr> to_equal <expr>` (and `to_be`/`to_contain`/…) is **legacy infix
matcher syntax** that only works when the harness rewrites it to method form
`expect(X).to_equal(Y)` via `preprocess_matchers_only`. testing.md steers
authors to method-form or `assert_*` instead, but **4251 occurrences across 155
spec files** still use the word-infix form.

Two execution paths do NOT preprocess and run the raw line:
- `bin/simple run <spec>` (never preprocesses — `run` is not the test harness).
- `bin/simple test <single-file>` (in-process; empirically does NOT regenerate
  `.spipe_matchers_<name>.spl`, so it runs the unrewritten line).

On those paths the parser consumes `expect(X)` and **drops the `to_equal Y`**,
so the assertion degrades to a bare `expect(X)` hollow check.

## Two failure modes (the second is worse)

1. **False-RED** — subject is a falsy-returning call:
   `expect group_has_member(g, eve) to_equal false` where the fn correctly
   returns `false` → reported `expected call result to be truthy, got false`.
   The library is correct; the test is mis-evaluated. (privilege/group,
   privilege/principal, privilege/id_path, and others.)
2. **False-GREEN (silent)** — subject is anything non-falsy:
   `expect truthy_call() to_equal 999` parses to `expect(truthy_call())`, drops
   `to_equal 999`, and **passes vacuously — nothing is compared**. Demonstrated:
   `expect false to_equal false` passes, but so would `expect false to_equal true`.
   **PASS counts on non-preprocessing paths are therefore inflated by hollow
   passes.**

## Repro

```simple
# NOTE: file must be named *_spec.spl for preprocess to even be attempted
use std.spipe.*
fn ret_false() -> bool: false
describe "infix":
    it "infix call to_equal false": expect ret_false() to_equal false   # FALSE-RED
    it "method form":               expect(ret_false()).to_equal(false) # passes (correct)
```
`bin/simple run` and `bin/simple test` both ✗ the infix it-block; the
preprocessed temp (`.spipe_matchers_*`) passes 3/3 under both run and test.

## Precise root cause (dispatch, 2026-06-30)

`bin/simple test <file>.spl` does NOT reach the Rust `run_test_file`
(which preprocesses at execution.rs:534/801). `main.rs` routing:
`test_should_use_light_daemon_client(args)` returns true when any arg
`!starts_with('-') && ends_with(".spl")` (main.rs:206-210), so a single-file
`test` dispatches to **`src/app/test_runner_new/test_runner_client.spl`** →
light daemon → spawns `bin/simple run <spec>` via `process_run` (no preprocess;
`run` is the seed and never rewrites infix). The pure-Simple rewriter
`spipe_rewrite_infix_expect_line` DOES exist (`test_runner_execute.spl:228`) but
is not applied on the client/daemon spawn path. So the fix is **pure-Simple**
(no seed rebuild): preprocess each spec (apply `spipe_rewrite_infix_expect_line`
to a temp) before the `bin/simple run <spec>` spawn in the client/daemon runner,
mirroring the Rust `preprocess_matchers_only`.

## Fix (highest-leverage, deferred — scope-expanding)

Wire `preprocess_matchers_only` into the dispatch `bin/simple test <single-file>`
actually uses (the right code already exists in `run_test_file`; it is simply
not on this path). **Caution:** turning preprocessing on will make currently
**vacuous (false-green) assertions actually execute** — some will newly FAIL.
So the root fix can *increase* the measured failure count; apply it deliberately
and RE-MEASURE with `bin/simple test` (a `run`-based sweep structurally cannot
validate word-infix). Do NOT "fix" the libraries (they are correct) and do NOT
normalize 155 files of tests to a harness defect.

## Measurement caveat (for the test-suite sweep)

The 2026-06-29 full-suite sweep used `bin/simple run` per file → over-reports
word-infix falsy-subject specs as failures AND under-reports word-infix
non-falsy specs (hollow greens). Real pass/fail must be measured with the
preprocessing `test` path.
