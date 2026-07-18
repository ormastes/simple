# SSpec: `expect(<call returning 0/false/"">).to_equal(...)` false-REDs

**Status:** FIXED in seed source; pending seed rebuild + deploy to default `bin/simple`
**Found:** 2026-06-29 (noise sweep — riscv64 target spec failures led here)
**Area:** test framework / BDD matchers (Rust seed)

## Symptom

A spec assertion on a **function/method call that returns a falsy value**
(`0`, `false`, `""`) fails even when the matcher should pass:

```simple
fn ret_zero() -> i32: 0
describe "x":
    it "zero call equals zero":
        expect(ret_zero()).to_equal(0)   # FAILS: "expected call result to be truthy, got 0"
```

A literal (`expect(0).to_equal(0)`) passes, and a call returning a truthy value
passes — only a *call expression* whose result is falsy is affected. This
false-REDs any test asserting a function returns 0 / false / "".

Observed in `src/lib/nogc_sync_mut/debug/formats/test/target_riscv64_spec.spl`
("resolves register indices by name" — `register_index("zero")` returns 0). The
target definition itself is correct (verified via `bin/simple run`).

## Root cause

Regression from the 2026-06-28 "matcher pass must not clear a prior failure" fix
(`sspec_matcher_success_clears_prior_failure`). The `expect` handler eagerly
flags a *hollow call* — `expect(<call>)` whose result is falsy — by setting
`BDD_EXPECT_FAILED` (to catch `expect(always_fails())` with no matcher). After
the 2026-06-28 change, a following `.to_equal(0)` that *passes* no longer clears
that pre-set failure, so the example stays red.

## Fix

Separate the hollow-call signal from real matcher failures
(`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`,
`src/compiler_rust/compiler/src/interpreter_method/mod.rs`):

- New `BDD_EXPECT_PROVISIONAL` thread-local. The eager hollow-call check sets it
  (not `BDD_EXPECT_FAILED`).
- Applying any `.to_*()` matcher clears `BDD_EXPECT_PROVISIONAL` (the call IS
  being checked) before recording the matcher's own result.
- Example end fails if `BDD_EXPECT_FAILED || BDD_EXPECT_PROVISIONAL`.

Net: `expect(falsy_call()).to_equal(<falsy>)` passes; bare `expect(falsy_call())`
still fails; `expect(fail).to_equal(x)` then a later passing matcher still fails
(2026-06-28 behavior preserved).

## Verification

Regression tests in `src/compiler_rust/driver/tests/interpreter_bdd.rs`:
`bdd_matcher_passes_on_falsy_call_result`,
`bdd_bare_falsy_call_without_matcher_still_fails`
(plus the existing `bdd_matcher_pass_after_failure_keeps_example_failed`).

## Deploy gate

Seed-side fix; takes effect for `bin/simple test` after a seed rebuild
(`cargo build` + deploy). The default `bin/simple` is currently the seed, so the
rebuilt seed binary must replace it to clear the false-REDs.
