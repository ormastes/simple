# Bug: AST collection-desugar rewrites `x = x + n` to `x.merge(n)` on scalar (non-collection) targets

- **Date:** 2026-07-29
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** MEDIUM — silently changes program shape (Assign -> MethodCall) for a
  extremely common idiom (`total = total + item`, `x = x + 1`); found as a side
  discovery while implementing E1047 (param-mutability-semantic, lane G2), not yet
  confirmed to cause a *runtime* miscompile, but the AST-level rewrite fires with no
  type gate at all.
- **Found by:** lane G2 (param-mutability-semantic)

## Symptom

`src/compiler/10.frontend/desugar/collection_desugar.spl`'s `try_rewrite_assign`
(Pattern B, lines ~168-174) rewrites any `target = target + rhs` into
`target.merge(rhs)` as soon as the shape matches `Assign(target, Binary(+, lhs, rhs))`
with `exprs_refer_same(target, lhs)`. This runs as an **AST-level pass before
type-checking**, so it has no way to check that `target` is actually a collection
(`[T]`) — the rewrite fires unconditionally, including on plain scalars:

```
fn bump(x: i64) -> i64:
    x = x + 1     # AST-rewritten to `x.merge(1)` before HIR lowering ever runs
    x
```

Confirmed via HIR dump (SafetyChecker debug trace, lane G2): the statement lowers to
`HirExprKind::MethodCall(receiver: NamedVar(x), method: "merge", args: [IntLit(1)])`
inside a `HirStmtKind::Expr` wrapper — **not** `HirStmtKind::Assign` — for a plain
`i64` parameter. The same rewrite also fires on struct/class field assignment
(`c.n = c.n + 1` -> `c.n.merge(1)`, confirmed in the same trace).

The comment block at the top of the file documents the intended patterns as
array-specific (`x = x + other_arr -> x.merge(other_arr)`), but the implementation
(`try_rewrite_assign`, `try_rewrite_compound_assign`) never checks the operand type —
only the AST *shape* (`Assign`/`CompoundAssign` wrapping `Binary(+, ...)` with the
same LHS on both sides).

## Impact

- Confirmed harmless SO FAR wherever it's been observed: `i64.merge(i64)` and
  `i64.merge(field)` calls appear to resolve to something that doesn't crash and
  doesn't corrupt the value in the two traced cases (a `bin/simple test` run over the
  affected function completed and returned the expected final value in both
  `x = 42` sibling tests used as a workaround). Whether `merge` on a scalar receiver
  is a genuine no-op UFCS dispatch, an error swallowed somewhere, or something more
  subtle was NOT fully characterized here — out of scope for lane G2.
- Definitely breaks semantic analysis that pattern-matches on `HirStmtKind::Assign`
  for a source-level `x = x + n` idiom: this is exactly what caused lane G2's E1047
  checker to need a second detection path (`HirExprKind::Assign` wrapped in
  `HirStmtKind::Expr`) plus a documented test workaround (avoid `x = x + n` shaped
  reassignment in E1047 specs; see
  `test/01_unit/compiler/semantics/param_mutability_semantic_spec.spl`'s first `it`
  block for the exact note). Any other future HIR/MIR pass that expects `x = x + n`
  to lower as `Assign` will hit the same surprise.
- `total = total + item` (running-sum accumulation) is an extremely common idiom;
  this rewrite silently changes its AST shape on every occurrence, gated only by
  whatever `merge` resolves to at the value's actual type at codegen/interp time.

## Suggested fix

Gate `try_rewrite_assign`'s Pattern B (and the equivalent branch in
`try_rewrite_compound_assign`) on the target actually being (or being inferable as) a
collection type before rewriting to `.merge(...)`, or move the rewrite to run after
type inference where the type is known. Until fixed, any code path (lint, semantic
checker, HIR/MIR pass) that pattern-matches source-shaped `x = x + n` on a
non-collection variable should be aware it may already be an `x.merge(n)` MethodCall
by the time it reaches HIR.

## Repro

```
fn bump(x: i64) -> i64:
    x = x + 1
    x
```
Parse with `parse_full_frontend`, lower with `HirLowering`, inspect the resulting
`HirStmtKind` for `bump`'s body: it is `Expr(MethodCall(NamedVar(x), "merge", [IntLit(1)]))`,
not `Assign(NamedVar(x), Add, IntLit(1))`.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STILL-OPEN (narrowed, by the source own admission)

A guard now exists — `fn is_definite_scalar_addend(e: i64) -> bool` at
`src/compiler/10.frontend/desugar/collection_desugar.spl:138` — but the comment
immediately above it states the residual case is deliberately not covered:

```
# depends on the rewrite firing there. That ambiguity is a pre-existing,
# separate, out-of-scope concern -- this gate only removes the *provably*
# wrong cases.
```

Pattern B (`x = x + other` -> `x.merge(other)`) is still documented as live at
`collection_desugar.spl:10`. Cited line 220 is stale; use :10 and :138.
