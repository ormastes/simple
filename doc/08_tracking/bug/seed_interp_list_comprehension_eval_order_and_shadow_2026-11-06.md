# Seed interpreter: list comprehension eval order and loop-var shadowing

- **Date:** 2026-11-06
- **Status:** open
- **Severity:** P3 (wrong value / ordering)
- **Area:** `src/compiler_rust/compiler/src/interpreter/expr/collections.rs` (`comprehension_iterate`)

## Defects

1. The seed interpreter evaluates every filter before any element expression. A side-effecting
   comprehension logs `f1,f2,f3,f4,g2,g4`; pure-Simple and the JIT desugar
   (a58339ff58b) give `f1,f2,g2,f3,f4,g4`.
2. At top level, `val x = 99; [x * 2 for x in [1, 2, 3]]` gives `[198,198,198]`: the loop
   variable does not shadow the outer `x` in the interpreter.

Fix: iterate per element (bind, filter, evaluate element) in a child env.
