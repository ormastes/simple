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

## 2026-08-31 re-measurement and design ruling needed (round-3 R1)

Re-measured on origin/main (`1d4aafe3914`, Rust seed). STOPPED without a code
fix per the bugfix recipe: correcting this requires a language-design ruling,
not a mechanical repair.

### Measurements (supersede the round-3 R1 wording)

- The round-3 literal repro `var f = false; fn s(): f = true; s()` at module
  top level **PASSES** (`f=true`). Module-global write-back through
  `sync_owned_captured_globals` works.
- The loss is confined to enclosing **function-local** `var`s: the same shape
  inside `fn outer():` prints `f=false`, and a two-call counter stays `0`.
  `it`-block vars hit it only because the spec runner wraps the tree into a
  generated `fn main():`, turning them into function locals.
- A write in a lambda body is not even parseable: `val lam = \: g = true`
  fails `expected expression, found Assign` — assignment is not expressible
  in a lambda, consistent with limitation-by-design.

### Why this is a design question, not a bug fix

Evidence that by-value / read-only capture is the *specified* semantics:

- `.claude/rules/language.md:22` — "Nested closure capture — can READ outer
  vars, CANNOT MODIFY (module closures work fine)".
- `doc/06_spec/feature/language/functions_spec.md:38` — "Lambdas and closures
  (capture by value)".
- MIR lowering implements a bind-time by-value snapshot
  (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3930`,
  "matching the oracle's by-value capture"), and
  `doc/06_spec/01_unit/compiler/mir/native_capturing_lambda_closure_conversion_spec.md`
  pins **by-value capture with interpreter parity** as an oracle. Flipping the
  interpreter alone breaks that green oracle and manufactures interpreter/JIT
  divergence (the R2 defect class).
- ~8 product files are deliberately coded around the limitation
  (`src/os/crypto/mgf1.spl:73`, `src/os/kernel/acpi/rsdt.spl:100`,
  `src/app/desugar/context_params.spl:7`, `src/app/play/wm_daemon.spl:216`,
  `src/lib/nogc_sync_mut/concurrent/thread.spl:10`, etc.).

Evidence of internal contradiction (why a ruling is required):

- `interpreter/expr/control.rs:49-50` claims regular closures "share the
  environment reference", yet the call path clones (`control.rs:146`;
  `captured_env_with_live_globals` clones at
  `interpreter_call/core/function_exec.rs:174ff`, and
  `sync_owned_captured_globals` skips overlay entries where
  `local_env.is_local(name)` — there is NO local write-back channel at all,
  regardless of whether the empty-env (`function_exec.rs:945/1557`,
  `interpreter_method/special/execution.rs:206/341`) or real-captured-env
  (`function_exec.rs:1014`) site is taken).
- `doc/06_spec/feature/usage/metaprogramming_spec.md:984` claims by-reference
  default with `move` opting into by-value — contradicting functions_spec.
- Large spec clusters (aop_pointcut, aop_spec, hook counters) are written
  assuming write-through and currently give no signal either way.

### The fork to rule on

(a) Keep by-value capture and make the silent loss **loud** — diagnose an
assignment to a captured non-global inside a nested fn/lambda (same
philosophy as the implicit-self-field guard, R6); update metaprogramming_spec
and the aop/hook specs to use module globals or returned state. Or
(b) adopt by-reference (cell) capture for `var` — a coordinated change across
interpreter, MIR by-value snapshot machinery, native closure conversion, the
parity oracle spec, functions_spec, and language.md, done together to avoid
lane divergence.

Until ruled, any one-sided interpreter change is wrong.

### Relation to after_all global-write-loss (round-3 R5)

Different root cause. R5
(`after_all_hook_module_global_write_lost_after_in_group_mutation_2026-08-31.md`)
concerns a **module global**, and module-global write-back demonstrably works
(first measurement above); its defect is in the global sync/publish path, and
is fixable within by-value semantics. Note `Env` writes clear the
`refreshed_globals` mark (`value.rs:621-624, 770-781`), so a
"refreshed-entry-not-published" theory is insufficient as stated. Also, on
origin/main `1d4aafe3914` the R5 repros do not fire the hook at all (no
`HOOK RAN`, final len=1 in both variants) — R5 is only observable atop the
unlanded after_all drain fix referenced in its record.
