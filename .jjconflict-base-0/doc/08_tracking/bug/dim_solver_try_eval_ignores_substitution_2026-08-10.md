# DimSolver.try_eval ignores the substitution, so a bound dimension variable never evaluates

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Product code**: `src/compiler/30.types/dim_constraints.spl:184-210` (`try_eval`)
- **Spec**: `test/unit/compiler/type_infer/type_infer_correctness_spec.spl`
  → `Dimension constraint solving` → `binds a dimension variable through unification`
  (and the duplicate leg `test/01_unit/...`)
- **Found**: 2026-08-10.

## Symptom

```
semantic: called unwrap on None
```

## Reproduction

```
var solver = DimSolver.new()
val d = solver.fresh_var(sp())
solver.unify(d, DimExpr(kind: DimExprKind.Literal(value: 16), span: sp()))  # Ok

solver.try_eval(solver.apply_substitution(d)).unwrap()   # 16  -- binding landed
solver.try_eval(d)                                       # nil -- should be Some(16)
```

## Cause

`try_eval` matches on `expr.kind` directly and has no `Var(id)` arm, so a
dimension variable falls through to `case _: nil` — even when the substitution
already binds it to a literal. Every other traversal in the same impl
(`unify` line 67, `occurs_in`, `solve_constraint`) normalises through
`apply_substitution` first; `try_eval` alone does not.

`try_eval` currently has no callers outside `dim_constraints.spl`, so the gap is
latent rather than actively breaking a lane — but it is a trap for the first
caller, since the function's docstring ("try to evaluate a dimension expression
to a constant") is exactly what a solved variable is.

## Unblock condition

Have `try_eval` resolve through the substitution before matching (e.g. match on
`self.apply_substitution(expr).kind`, or add a `case Var(id)` arm that looks the
binding up and recurses). Re-run the spec; the example must go green.
