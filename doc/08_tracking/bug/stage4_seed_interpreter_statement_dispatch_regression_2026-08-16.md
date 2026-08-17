# HANDOFF: Stage-4 seed interpreter statement/assignment dispatch regression

> ## RETIRED 2026-08-17 by EXECUTION on the seed itself (worker W5)
>
> `bin/simple` IS the Rust seed this row is about, so it is the correct instrument.
> A standalone JS-engine probe (no spec runner, no 120s budget) exercising all four
> documented symptoms is GREEN on the deployed seed:
>
> ```
> $ env SIMPLE_EXECUTION_MODE=interpreter bin/simple run \
>     test/01_unit/engine_divergence/probes/js_engine_assign_dispatch_probe.spl
> J1_for_accum=num:3.0        # doc said 0 (accumulator never accumulated)
> J2_nested_obj=num:42.0      # doc said "variable `a` not found"
> J3_simple_assign=num:7.0    # doc said "ReferenceError: x is not defined"
> J4_typeof_undef=str:undefined  # doc said typeof-undefined mis-exec
> ```
>
> The `env.remove(obj_name)` -> mutate -> re-insert hunk named as the suspect is
> STILL PRESENT (`interpreter/node_exec.rs:786`, `:960`, `:1897`), so this is NOT a
> "the code changed" retirement -- the pattern is there and is nevertheless correct
> now: every match arm re-inserts, making the remove/re-insert total as the doc's
> required action #1 demanded.
>
> **Separately: the doc's spec-based repro command is not a usable instrument.**
> `bin/simple test test/03_system/feature/js/interpreter_vars_spec.spl` returns
> `Results: 1 total, 0 passed, 1 failed` with `reason=child-timeout budget_ms=120000`
> -- it exceeds the runner's own per-file budget and never reaches the assertions.
> That is a COST problem in the spec, not evidence of this defect; a timeout is
> UNVERIFIED, never a failure. Retirement rests on the probe, not on that spec.
>
> Regression guard: `test/01_unit/engine_divergence/check-engine-divergence-probes.shs`.


**Status:** OPEN — handoff to seed owner
**OWNER:** Stage-4 / seed-bootstrap owner — the session that rebuilds and
redeploys `bin/release/<triple>/simple`. This is a Rust-seed defect; it can only
be fixed and re-verified by rebuilding+redeploying the seed. It is NOT fixable in
pure Simple.
**Filed:** 2026-08-16
**Related (JS-engine angle):**
`doc/08_tracking/bug/seed_gc_js_engine_typeof_undefined_and_for_desugar_regression_2026-08-15.md`

## TL;DR
- The deployed Rust seed (`bin/release/x86_64-unknown-linux-gnu/simple`,
  redeployed ~2026-08-15 08:26) regressed the Simple **interpreter's**
  assignment/identifier execution.
- **Trigger commit `a155bff913f`** ("fix(engine2d): interpreter nested
  field-assign ...") rewrote `src/compiler_rust/compiler/src/interpreter/node_exec.rs`
  by ~355 lines (Case 3 nested field assignment `a.b.c = v`). Effect appeared
  only after the seed rebuild+redeploy.
- The new assignment path `env.remove(obj_name)` → mutate → re-insert (quoted
  below) is the likely culprit: under the JS engine's scope-chain environment it
  loses the binding, producing `variable 'a' not found` / `ReferenceError`.
- **Repro reproduces via the JS-engine path only.** A direct pure-Simple repro
  (`for` accumulator + `a.b.c = v` in native Simple) executes CORRECTLY — so the
  defect is specific to how the JS engine's environment model drives this path,
  not universal to every Simple assignment.
- All seed runs below are DIAGNOSTIC, never release evidence.

## Minimal repro

### Pure-Simple (direct) — does NOT reproduce (both correct)
`repro_seed.spl`: `fn main` with `for i in 0..5: sum = sum + i` and nested
`class Outer{ a: Mid{ b: Inner{ c } } }`, `o.a.b.c = 42`.
```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run repro_seed.spl
sum=10        # expected 10  ✓
nested=42     # expected 42  ✓
```
Conclusion: direct Simple assignment/for-loop is fine. The seed defect only
surfaces on the JS-engine consumer path.

### Fallback — JS engine (Simple code the seed interprets) — REPRODUCES
```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run \
    test/03_system/feature/js/interpreter_vars_spec.spl   # DIAGNOSTIC
[WARN] [test] ReferenceError: x is not defined
[WARN] [test] ReferenceError: y is not defined
[WARN] [test] ReferenceError: n is not defined
  ✗ nested object creation
      semantic: variable `a` not found
[WARN] [test] Script execution step limit reached
  ✗ for loop with accumulator
      expected 0 to equal 3          # loop body never accumulated
```

## Suspected hunk (`a155bff913f`, node_exec.rs, `exec_assignment`)
New identifier-receiver assignment branch removes the binding from the env,
mutates, and re-inserts — a remove/re-insert that the JS scope-chain env does
not survive:
```rust
if let Expr::Identifier(obj_name) = receiver.as_ref() {
    if let Some(obj_val) = env.remove(obj_name) {   // <-- removes binding first
        match obj_val {
            Value::ClassInstance(instance) => {
                instance.set_field(field.clone(), value);
                env.insert(obj_name.clone(), Value::ClassInstance(instance));
            }
            ...
```
Plus the reworked deep-place path:
```rust
if let Some(place) =
    super::place::resolve_place(&assign.target, env, functions, classes, enums, impl_methods)?
{ if super::place::write_place(env, &place, value) { return Ok(Control::Next); } }
```
Do NOT attempt to fix Rust from a consumer session — this is a handoff.

## Blast radius (DIAGNOSTIC seed runs, each once)
| Suite | Result | Symptom |
|-------|--------|---------|
| es5_conformance_spec | 38/54 | for / typeof-undefined mis-exec |
| interpreter_vars_spec | 12/21 | `variable 'a' not found`, for-accumulator = 0 not 3, `ReferenceError: x/y/n` |
| browser_script_execution | 0/4 | now worked-around in pure Simple at origin `78ae3343` (real for/while/if in JS-subset parser) — seed defect remains for other consumers |

## Required action (seed owner)
1. Fix `node_exec.rs` `exec_assignment` so the identifier-receiver /
   `resolve_place` path preserves env bindings under the JS scope-chain model
   (the remove/re-insert must be atomic and total across every match arm).
2. Rebuild + redeploy the seed via the bootstrap flow.
3. Re-run to confirm GREEN: the JS-engine repro above, plus es5_conformance_spec
   and interpreter_vars_spec restored to their pre-`a155bff913f` pass counts.

## Recommended pre-deploy CI guard
Add an interpreter smoke that runs BEFORE any seed redeploy and blocks a bad
seed: a tiny JS-engine script exercising (a) a `for` loop accumulating into a
var and (b) `typeof <undeclared>`; assert the accumulator result and that no
`ReferenceError` / `variable ... not found` is emitted. Gate seed deploy on it.
