# Interpreter logical operators eagerly evaluate the right operand

- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- severity: high (unexpected effects and errors)
- component: core tree-walking interpreter

## Symptom

`eval_binary` evaluated both operands before dispatching `and` or `or`.
Consequently `false and effect()` and `true or effect()` still ran `effect`.

## Resolution

After evaluating the left operand, the shared evaluator now returns false for
a false `and` and true for a true `or` without evaluating the right operand.
Focused tests use division by zero on the skipped side and also cover both
paths where the right operand remains required.


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. The claimed file `src/compiler/10.frontend/core/interpreter/ops.spl` contains NO and/or handling at all -- it is a binary-op helper over ALREADY-EVALUATED values, so it could never have been the short-circuit site. The real site is `src/compiler/10.frontend/core/interpreter/eval.spl:540-549` (`eval_binary`), which short-circuits BEFORE touching the right operand: it evaluates `left`, then `if op == 55 and val_is_truthy(left) == false: return val_make_bool(false)` / `if op == 56 and val_is_truthy(left): return val_make_bool(true)`, and only afterwards evaluates `right`. The original grep looked in the wrong file.
