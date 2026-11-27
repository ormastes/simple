# `?` on a Result inside a one-line wrapper yields a value matching neither Ok nor Err (interpreter)

Status: SUPERSEDED. Found 2026-09-01 while landing the strict HWIR ECC offload equivalence spec.

## Symptom

`src/compiler/50.mir/hwir/host_evaluator.spl:281`

```
pub fn evaluate_strict_comb_hwir(module: HwModuleDef,
    inputs: [HwHostInput]) -> Result<HwHostEvaluation, text>:
    prepare_strict_comb_hwir(module)?.evaluate(inputs)
```

Under the spec-lane tree-walk interpreter (`bin/simple test`) a caller that
matches the returned value gets NEITHER arm:

```
match evaluate_strict_comb_hwir(module, inputs):
    case Ok(evaluation): ...    # not taken
    case Err(message): ...      # not taken
```

Execution falls through to the function tail. Measured on the 8-bit `sub`
module: the two-step path `prepare_strict_comb_hwir(module)` +
`prepared.evaluate(inputs)` + `value_of("result_out")` returns **253**
(correct), while the one-shot wrapper above falls through both arms.

A related shape reports `method \`value_of\` not found on type \`enum\`
(receiver value: Result::Ok(HwHostEvaluation(...)))` — i.e. `?` handed back the
still-wrapped `Result` instead of its payload.

## Blast radius (measured, pristine HEAD 626250fd936)

`bin/simple test test/01_unit/compiler/50.mir/hwir_host_evaluator_spec.spl`
=> `Results: 9 total, 5 passed, 4 failed`, all four failures being
`method \`value_of\` not found on type \`enum\``. This is PRE-EXISTING: the same
4 failures occur with and without the ECC offload change.

## Workaround in use

`test/01_unit/compiler/50.mir/hwir_ecc_offload_equivalence_spec.spl` calls
`prepare_strict_comb_hwir` and `evaluate` separately and never touches the
one-shot wrapper.

## Unblock condition

The interpreter's `?` must unwrap `Ok` and early-return `Err` when the result
of `?` is immediately method-called and returned as the function's tail
expression. Once fixed, `hwir_host_evaluator_spec` should return 9/9 with no
spec edit.


## 2026-11-09 — DOCUMENTED + pinned (work/p3-subj4-seed-20261109)

Root cause is lexical, not a `?`-lowering defect: `f()?.m()` lexes as the
SAFE-NAVIGATION operator `?.` (Err/None -> nil), so a Result-returning
one-line wrapper written that way returns nil, which matches neither Ok nor
Err at the caller. The try-then-call form is `(f()?).m()`: Ok unwraps and
Err early-returns through the method receiver.

Pinned by `test/01_unit/compiler/95.interp/interpreter/result_try_receiver_prevention_spec.spl`
(commit a0486f1b7e8, in release/1.0.0). Verified on the deployed seed under
`SIMPLE_EXECUTION_MODE=interpreter`: 4/4 GREEN. Manually re-verified both
shapes: unparenthesised `prep(h)?.get()` returns nil and falls through both
match arms; parenthesised `(prep(h)?).get()` returns the payload. Status
open -> documented.

## 2026-11-10 triage — SUPERSEDED/documented (seed-smoke, lane p3-interp4 row 21)

Documented as lexical (not a `?`-lowering defect) by bdcbec5bd33d (in branch):
`f()?.m()` lexes as safe-navigation; `(f()?).m()` is the try-then-call form.
Pinned by test/01_unit/compiler/95.interp/interpreter/result_try_receiver_prevention_spec.spl
— re-verified this lane: 4 total, 4 passed, 0 failed on the worktree seed
under SIMPLE_EXECUTION_MODE=interpreter. No code change.
