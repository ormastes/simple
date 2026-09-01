# Test runner false-fails specs with 10–99 examples (downstream of the `i64?` payload-3 collision)

**Date:** 2026-07-24
**Status:** Test-runner symptom FIXED (pure-Simple, `find_raw`); root cause is a
separate DEFERRED architectural limitation — see below.

## Root cause (already documented — NOT re-filing)

This is a **downstream symptom** of the deferred seed-JIT flat-`i64?` payload-3 ==
nil collision, fully root-caused with a senior deferral decision in
**`interp_index_of_digit_leading_literal_2026-07-22.md`**. Summary: primitive
`T?` lowers to `HirType::Pointer{inner:T}` (a flat, non-boxed nullable lane) whose
in-band None sentinel is bit pattern `3` (`rt_core_nil()`), so a present `i64`
value of exactly `3` is indistinguishable from `nil` in the seed-JIT `run` path
(the interpreter is correct). A full retag (7 site-groups / 6+ files, hot
bootstrap-only paths, inherits the 61-bit BoxInt truncation caveat) was designed
and **deliberately deferred**; a boundary-boxing spot-patch was **proven wrong**
(`??` does not unshift). Do NOT re-attempt the spot-patch.

Independently re-confirmed 2026-07-24 on the deployed binary: only `val b:i64?=3`
reads as nil (−2…12 sweep); `SIMPLE_EXECUTION_MODE=interpreter` is clean; both the
Jul-24 `bin/release` binary and the Jul-22 seed reproduce identically.

## The new downstream finding: `simple test` false-negatives

`test_executor_parsing.spl` parses each child spec's `"N examples, M failures"`
summary via `extract_number_before`/`extract_number_after_colon`, which called
`text.index_of(keyword)` — an `i64?`-returning API. In `"10 examples…"` …
`"99 examples…"`, `"example"` sits at byte **offset 3**, so `index_of` returned
`Some(3)` → read as `None` → count unparseable → `make_result_from_output` emits
*"no parseable pass/fail summary in test output; refusing synthetic pass"* →
**every genuinely-green spec with 10–99 examples is falsely marked FAILED.**

- Boundary swept & confirmed: n=9 PASS, n=10 FAIL … n=99 FAIL, n=100 PASS again
  (offset returns to 4). Real victims: `loader_shared_core_spec` (20 ex),
  `spec_constants_contract_spec`, `utf8_validation_spec` — all print
  `N examples, 0 failures` under `simple run`.
- **Red herrings ruled out** (don't chase them): the `self.field` "self is
  implicit" Info hint and the `[gc-warning]` layer-family line are both harmless
  (specs with 2/20/50 `self.field` uses all pass); the sole discriminator is
  example count ≥ 10.

## Fix (this doc) — sanctioned `>=0` critical-path mitigation

Per the senior guidance in the root-cause doc ("prefer `>= 0` sentinel-style APIs
… in critical paths until [retagged]"), `test_executor_parsing.spl` now uses a
local `find_raw(s, keyword) -> i64` (a plain raw-`i64` substring scan, never
`i64?`) in place of `s.index_of(keyword)` inside `extract_number_before` and
`extract_number_after_colon`. A raw `i64` of value 3 is a real 3, so offset-3
matches survive.

Verified at the algorithm level under the current (still-buggy) deployed binary:
`extract_number_before` now returns the correct count for `9/10/20/99/100`
examples. Takes effect end-to-end once the test runner is recompiled into the
binary by the next bootstrap (the runner is precompiled; the env var does not
rescue it at runtime). The broad `??`/`index_of` blast radius across production
`.spl` (429–1609 sites per the root-cause doc) remains the deferred architectural
item — this fix only closes the test-runner critical path.

## Supersedes

Retracts `named_arg_self_field_value_parse_regression_2026-07-24.md` (the
`self.field` parse-regression theory was wrong — a red herring).
