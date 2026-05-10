# Research D: HIR Lower Expr — Duplication Map
**Scope:** `src/compiler_rust/compiler/src/hir/lower/expr/`
**Date:** 2026-04-28
**Phase:** 2-research (read-only)

---

## Anti-over-engineering filter decisions (rejected candidates)

### REJECTED: `Box::new(self.lower_expr(…)?)` wrapping
18+ sites across all files. Each feeds a structurally different `HirExprKind` field
(`Await`, `ContractOld`, `PointerNew`, `Binary.left`, `Binary.right`, `If.cond`, etc.).
This is idiomatic Rust for heap-boxing a recursive HIR node — not duplication. A
helper would only save one call per site while obscuring which HIR variant is being
built. **Dropped.**

### REJECTED: `lower_expr` match-arm dispatcher (mod.rs)
The dispatch table in `lower_expr` is one match arm per AST variant. Parallel shape
across arms is the consistent idiom of a total-coverage visitor. Each arm delegates to
a distinct `lower_*` method with different semantics. Adding a new AST variant would
be *harder* if arms were collapsed. **Dropped as parallel-arm desugar idiom.**

### REJECTED: i18n trio (literals.rs)
`lower_i18n_string` (line 106), `lower_i18n_ref` (line 170), and the inline lookup
inside `lower_i18n_template` (line 129) all call `crate::i18n::lookup`, but their
fallback invariants diverge: `unwrap_or_else(|| default_text.to_string())` vs
`lookup_or_placeholder(name)` vs build-from-parts. Fewer than 3 sites share the same
invariant. **Dropped.**

### BORDERLINE (do not merge, AC-5): `for e in exprs { hir_exprs.push(self.lower_expr(e, ctx)?); }` in collections.rs
Pure form appears at:
- `collections.rs:64-76` (`lower_array`)
- `collections.rs:138-150` (`lower_vec_literal`)
- The `Some(n)` branch of `lower_array_repeat` (via `std::iter::repeat_n`)

The other two collection loops (`lower_tuple`, `lower_labeled_tuple`) do additional
in-loop work (push to a `types`/`hir_fields` vec simultaneously) and cannot use a
shared helper without a closure or tuple return. With only 3 pure sites and CLAUDE.md's
"three similar lines is better than a premature abstraction" rule, this does **not**
meet the merge bar. Reported as evidence the filter was applied; **do not merge.**

---

## Cluster 1: Argument list lowering (`&[ast::Argument]` → `Vec<HirExpr>`)

- **Call sites** (7 confirmed):
  - `calls.rs:47-55` — enum constructor path (`Some`/`Ok`/`Err`/`None`)
  - `calls.rs:70-78` — struct-init from known type (named `fields_hir`)
  - `calls.rs:89-97` — struct-init lenient mode (named `fields_hir`)
  - `calls.rs:194-199` — generic `lower_call` fallthrough
  - `mod.rs:272-275` — `lower_builtin_method_call` (args pre-lowered before method dispatch)
  - `mod.rs:386-389` — `lower_method_call` generic user-defined path
  - `simd.rs:240-244` — `lower_static_method_call`
  - (`helpers.rs:17-20` in `lower_builtin_call` is already an extraction of this pattern, proving the abstraction is wanted — but it is not reused by the 7 sites above)

- **Shared invariant:** Lower each argument's `.value` field via `self.lower_expr(&arg.value, ctx)?`, collect results in order, discard `arg.name`. The name-discard is deliberate: all these sites are preceded by dispatch logic that reads `arg.name` to branch *before* the loop (e.g., `calls.rs` checks `args.iter().any(|a| a.name.is_some())` to detect struct vs positional call). Inside the loop, `arg.name` is never read. A shared helper correctly captures this invariant.

- **Proposed unification:** Add `lower_call_args` to `helpers.rs` (already owns `lower_builtin_call` which does the same thing internally):
  ```rust
  pub(in crate::hir::lower) fn lower_call_args(
      &mut self,
      args: &[ast::Argument],
      ctx: &mut FunctionContext,
  ) -> LowerResult<Vec<HirExpr>> {
      let mut out = Vec::with_capacity(args.len());
      for arg in args {
          out.push(self.lower_expr(&arg.value, ctx)?);
      }
      Ok(out)
  }
  ```
  `lower_builtin_call` in helpers.rs becomes a 3-liner delegating to `lower_call_args`.
  The 7 call sites replace their inline loops with `let args_hir = self.lower_call_args(args, ctx)?;`.

  The struct-init sites (calls.rs:70-78 and 89-97) use `fields_hir` as the local name
  — no semantic difference, same helper applies.

  `lower_call_args` does NOT exist anywhere else in `src/compiler_rust/compiler/src/hir/`
  (verified by grep before proposing). No generic/trait bounds needed — `Lowerer` is a
  concrete struct.

- **Risk:**
  - **Name-drop preservation:** Any future call site that needs to preserve `arg.name`
    (e.g., named-arg dispatch at the HIR level) must not use this helper — it
    intentionally drops names. The function docstring must state this.
  - **Struct-init coupling:** The two struct-init sites use the lowered args as
    positional field initializers in `HirExprKind::StructInit`. If field-order
    semantics change (e.g., named args reordered at HIR level), those sites must
    switch back to a name-aware loop. Low current risk; note in helper doc.
  - **Error-path parity:** All 7 sites propagate the first lowering error via `?` in
    order. The helper preserves this — no divergence.
  - **Span tracking:** `ast::Argument` carries no span at this level (span is on
    `Expr`, not `Argument`). No span fidelity is lost.

- **Test surface:**
  - Existing coverage: `src/compiler_rust/compiler/tests/` covers function calls,
    method calls, struct init, and SIMD static calls.
  - Intensive test to prove merge safety (interpreter mode per `compile_mode_false_greens`):
    1. Call with zero args → empty `Vec` returned, no panic.
    2. Call with positional args → args lowered in order, values correct.
    3. Call site that previously checked `arg.name` before the loop (enum constructor
       path) still dispatches correctly after refactor.
    4. Struct-init path: `Point(x: 1, y: 2)` — names discarded, positional fields
       correct in HIR output.
    5. SIMD static method call with multiple args — values lowered, type preserved.
    6. Error propagation: one arg fails lowering → entire `lower_call_args` returns
       `Err`, no partial Vec emitted.
  - Run in `--mode=interpreter` (not `--mode=native`/`--mode=smf`) to avoid stub
    no-ops per `compile_mode_false_greens`.

---

## Summary

One actionable cluster found. Zero false-positive merges recommended. The
`lower_call_args` abstraction is already implicit in `helpers.rs::lower_builtin_call`
but is not reused by the 7 other sites that inline the identical 4-line loop. The
unification is low-risk, has a clear test surface, and passes all AC-5 filters.
