# Seed interpreter: list comprehension eval order and loop-var shadowing

- **Date:** 2026-11-06
- **Status:** fixed in source 2026-11-06 (awaits seed redeploy)
- **Severity:** P3 (wrong value / ordering)
- **Area:** `src/compiler_rust/compiler/src/interpreter/expr/collections.rs` (`comprehension_iterate`)

## Defects

1. The seed interpreter evaluates every filter before any element expression. A side-effecting
   comprehension logs `f1,f2,f3,f4,g2,g4`; pure-Simple and the JIT desugar
   (a58339ff58b) give `f1,f2,g2,f3,f4,g4`.
2. At top level, `val x = 99; [x * 2 for x in [1, 2, 3]]` gives `[198,198,198]`: the loop
   variable does not shadow the outer `x` in the interpreter.

Fix: iterate per element (bind, filter, evaluate element) in a child env.

## Fix (2026-11-06)

`interpreter_helpers/utilities.rs`: `comprehension_iterate` (collect all envs, then evaluate) was replaced by
`comprehension_for_each`, which binds, filters and runs the element body per item in a child env, and calls
`mark_local` on the pattern names. The shadow bug was in the identifier read (`interpreter/expr/literals.rs`
~L318): a non-local name prefers `MODULE_GLOBALS`, so the un-marked loop var read the top-level `x`.

Evidence: RED on the unmodified seed 0/5, GREEN 5/5 for `test/01_unit/language/comprehension_eval_order_and_shadow_spec.spl`.
Order now `f1,f2,g2,f3,f4,g4`; shadow `[2,4,6] 99`. 1M-element comprehension: 1.03s/1.70GB -> 0.83s/223MB.
