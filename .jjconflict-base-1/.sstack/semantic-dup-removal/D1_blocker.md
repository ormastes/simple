# D1 Blocker — Spec Test References Non-Existent HIR Fields

**Date:** 2026-04-28
**Status:** BLOCKED — source refactor complete, spec test cannot compile

---

## D1 Refactor Status: COMPLETE

The helper and all 7 call-site rewrites were applied successfully:

- `helpers.rs`: `lower_call_args` added with required docstring; `lower_builtin_call` delegates to it.
- `calls.rs`: 4 sites rewritten (enum-ctor :47, struct-init known :70, struct-init lenient :89, regular call :194).
- `mod.rs`: 2 sites rewritten (lower_method_call generic :272, lower_builtin_method_call :386).
- `simd.rs`: 1 site rewritten (lower_static_method_call :240).

`cargo build` of `simple-compiler` succeeds clean. Existing HIR tests (`bitfield_hir_lowering`, `domain_block_hir_lowering`) pass.

Grep confirmation (post-edit):
- `helpers.rs`: 2 occurrences (def + call in lower_builtin_call)
- `calls.rs`: 4 occurrences (one per site)
- `mod.rs`: 2 occurrences (one per site)
- `simd.rs`: 1 occurrence

**NOTE:** Parallel jj reconcile clobbered edits once during the session (per memory
`feedback_jj_uncommitted_clobbered_by_parallel`). Edits were re-applied before the build.

---

## Blocker: `tests/hir_lower_call_args.rs` Cannot Compile

The pre-written spec test (`src/compiler_rust/compiler/tests/hir_lower_call_args.rs`) references
HIR field names and visibility that do not exist in the current codebase. These are not typos —
they assume a structurally different HIR API.

### Error 1: `func.return_expr` (3 sites in spec test)

The spec uses `func.return_expr` as if it were `Option<HirExpr>`. Actual `HirFunction` (defined in
`src/compiler_rust/compiler/src/hir/types/functions.rs`) has:

```
pub return_type: TypeId,   // NOT an Option<HirExpr>
```

There is no `return_expr` field. Even substituting `return_type` would fail because it is a `TypeId`
(not an `Option<_>` and not iterable/unwrappable as an expression).

### Error 2: `stmt.kind` (3 sites in spec test)

The spec uses `stmt.kind` expecting `HirExprKind`. Actual `HirStmt` (defined in
`src/compiler_rust/compiler/src/hir/types/statements.rs`) has:

```
pub expr: HirExpr,         // NOT a `kind` field
```

The correct access path to `HirExprKind` is `stmt.expr.kind`, not `stmt.kind`.

### Error 3: `simple_compiler::hir::lower::lowerer::Lowerer` is private (E0603)

The spec imports `use simple_compiler::hir::lower::lowerer::Lowerer;`. The `Lowerer` struct is not
re-exported from the `hir` public API. This import fails with E0603.

---

## Resolution Options

**Option A (preferred): Spec-author rewrites the test against actual HIR API**

Replace:
- `stmt.kind` → `stmt.expr.kind`
- `func.return_expr` references → remove (HIR has no return-expression slot; the function
  body's last statement carries the implicit return value, or use `func.body.last()`)
- Drop the `use simple_compiler::hir::lower::lowerer::Lowerer;` import (unused after removing
  the trivial `d1_lower_call_args_method_exists_on_lowerer` test, or make `Lowerer` pub)

**Option B: Broaden D1 scope to include HIR type changes**

Add `return_expr: Option<HirExpr>` to `HirFunction` and add a `kind` field or re-export to
`HirStmt`. This is out of D1 scope as defined (touches `src/compiler_rust/compiler/src/hir/types/`),
has larger blast radius, and requires explicit sign-off.

---

## Commit Recommendation

The D1 source refactor (helpers.rs + calls.rs + mod.rs + simd.rs) is correct and should be committed
with an explicit note that the spec test gate is deferred pending spec-author fix.

Commit scope: `src/compiler_rust/compiler/src/hir/lower/expr/` only (4 files).

Do NOT commit `tests/hir_lower_call_args.rs` — it is the spec author's file and the errors are
entirely within that file, not caused by D1.
