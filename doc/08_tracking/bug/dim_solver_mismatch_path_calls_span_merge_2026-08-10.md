# DimSolver dimension-mismatch error path aborts: `Span` has no `merge`

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Product code**: `src/compiler/30.types/dim_constraints.spl:75,104,111,140,142,144`
- **Spec**: `test/unit/compiler/type_infer/type_infer_correctness_spec.spl`
  → `Dimension constraint solving` → `accepts matching dimensions and rejects a mismatch`
  (and the duplicate leg `test/01_unit/...`)
- **Found**: 2026-08-10, while rewriting the spec off its `HmInferContext` shadow.

## Symptom

```
semantic: class `Span` has no field named `end`
```

## Reproduction

```
bin/simple test test/unit/compiler/type_infer/type_infer_correctness_spec.spl
```

Minimal form:

```
var bad = DimSolver.new()
bad.add_equal(DimExpr(kind: DimExprKind.Literal(value: 4), span: lex_span_empty()),
              DimExpr(kind: DimExprKind.Literal(value: 8), span: lex_span_empty()),
              lex_span_empty())
bad.solve()      # aborts instead of returning Err
```

The matching case (`4` vs `4`, `solve()` → `Ok`) passes, so the solver itself
runs; only the **error** path is broken.

## Cause

`DimExpr.span` is the lexer `Span` (`src/compiler/10.frontend/core/lexer_types.spl:12`),
whose end field is named `end_pos` and which has **no** `impl Span` and therefore
no `merge` method. There is a second, unrelated `Span`
(`src/compiler/00.common/diagnostics/span.spl:9`) that does have `merge` and a
field named `end`. `e1.span.merge(e2.span)` resolves to that foreign method by
name and then reads `.end` off a lexer `Span`, which has no such field.

This is the cross-module member-resolution-by-name hazard: the call type-checks
and only fails when actually executed — which is why six occurrences survived.

## Impact

Every dimension-mismatch diagnostic in tensor/layer type checking aborts instead
of producing a `DimError`. Static shape-mismatch reporting — the stated purpose
of the dimension solver — cannot report.

## Unblock condition

Replace the six `e1.span.merge(e2.span)` calls with the lexer module's free
function `span_merge(e1.span, e2.span)` (`lexer_types.spl:20`), then re-run the
spec; the example must go green with `solve()` returning `Err`.
