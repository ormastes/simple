# Nested `fn` cannot mutate an enclosing `it`-block `var`; compound assignment fails "variable not found"

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

Inside an `it` block, a nested `fn` that assigns to a `var` declared in the
enclosing block does not update it. With a compound assignment the nested `fn`
cannot even resolve the name.

Repro — `nested_spec.spl`:

```simple
describe "nested fn mutating enclosing var":
    it "sees the write":
        var called = false

        fn marker():
            called = true

        marker()
        expect(called).to_equal(true)

    it "counter increments":
        var n = 0

        fn bump():
            n = n + 1

        bump()
        bump()
        expect(n).to_equal(2)
```

Command:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check nested_spec.spl
```

Actual — `Results: 2 total, 0 passed, 2 failed`:

- `sees the write` → `expected false to equal true` (the write is silently lost)
- `counter increments` → `semantic: variable `n` not found`

Expected: both pass.

The second case is the more serious half. The standing limitation recorded in
`.claude/rules/language.md` is "Nested closure capture — can READ outer vars,
CANNOT MODIFY". Here the **read** itself fails: `n = n + 1` reports `variable
n not found`, so the documented "can READ" guarantee does not hold for a
compound assignment in a nested `fn`.

## Root cause

Same layer as `spec_it_block_reads_stale_module_var_2026-08-04.md`: the spec
runner's registration-and-replay of `it` bodies. `test_result_wrapper.spl:449-453`
pushes the whole `describe`/`it` tree into a generated `fn main():`
(`test_result_wrapper.spl:333`), so an `it` body is a nested closure and a `fn`
declared inside it is nested one level deeper. The enclosing block's `var` is
captured by value rather than shared by reference
(`src/compiler_rust/compiler/src/interpreter/expr/control.rs:49-50`: "For move
closures, we capture by value (clone the environment); For regular closures, we
share the environment reference") — so the assignment lands on a clone
(case 1), and the name is absent from the nested `fn`'s own scope chain when the
assignment also needs to read it (case 2).

**Not pinned:** which of the two capture paths the `it`-body closure actually
takes, and why the plain-assignment case loses the write while the compound
case loses the binding entirely.

## Impact

This is the cause of the largest failure cluster in the largest directory in
`test/03_system/feature`. `usage` measures **4457 total, 145 failed**, and the
top cluster is AOP:

- `test/03_system/feature/usage/aop_pointcut_spec.spl` — **12 of 12 failing**,
  every one shaped `var called = false` + `fn marker(): called = true`, then
  `expect called == true` (`expected false to equal true`), or a counter var
  (`expected 0 to equal 2`).
- `test/03_system/feature/usage/aop_spec.spl` — 10 failing, same shape.

Because the recorder var never updates, these specs cannot distinguish "AOP
advice never fired" from "the counter is unwritable" — so they currently give
**no signal about AOP at all**, in either direction. Whether the pointcut weaver
itself works is UNKNOWN and still needs its own measurement once this is fixed.

Other `usage` clusters likely sharing this cause (unverified, same recorder
shape): `context_managers_spec.spl` (7), `decorators_spec.spl` (5),
`effect_system_spec.spl` (4).

## Why not fixed now

Fix belongs in the Rust bootstrap seed's closure/environment handling for spec
bodies, not in `.spl` product source; repo rules direct fixes to pure-Simple
source and discourage a seed rebuild unless essential
(`feedback_fix_spl_not_rust`, `feedback_no_bootstrap_unless_essential`). It also
changes capture semantics for every spec in the repo, so it needs its own lane
with a full regression pass — and the exact capture path is still unpinned.

Rewriting the affected specs to avoid nested-`fn` recorders was NOT done: it
would be a workaround that hides a real language/runtime defect, and for the AOP
specs the recorder *is* the observation mechanism, so removing it would make the
specs vacuous.
