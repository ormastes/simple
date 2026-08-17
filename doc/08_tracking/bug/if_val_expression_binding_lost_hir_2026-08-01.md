# `if val PAT = e:` in expression position loses its binding in HIR lowering

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Severity:** High — silent wrong answers under JIT/native, hard build abort under LLVM
- **Found by:** stage4 bootstrap, first blocker after the statement-arena fix `ec75d8c6090`
- **Related:** `if_val_expression_form_binding_lost_2026-07-20.md` (the *interpreter*
  half of the identical defect, fixed separately — this is the sibling that was
  left behind)

## Symptom

Stage4 reached LLVM codegen and aborted with:

```
error: codegen: semantic: llvm global load referenced undeclared symbol `interp_list`
    -> src/compiler/20.hir/hir_lowering/module_surface.spl
```

`interp_list` is not a global. It is the binding introduced at
`module_surface.spl:290`:

```
case ExprKind.StringLit(_, interps):
    # An interpolated literal carries sub-expressions -- not a leaf.
    if val interp_list = interps: interp_list.len() == 0 else: true
```

## Root cause

`Expr::If` carries a `let_pattern: Option<Pattern>` field
(`src/compiler_rust/parser/src/ast/nodes/statements.rs:84`), which the parser
populates for the `if val` form
(`src/compiler_rust/parser/src/expressions/helpers.rs:158`).

The HIR expression dispatcher discarded it:

```rust
Expr::If { condition, then_branch, else_branch, .. }   // <-- `..` drops let_pattern
    => self.lower_if(condition, then_branch, else_branch.as_deref(), ctx),
```

`lower_if` therefore never registered the bound name as a local. Resolution then
fell through `Lowerer::lower_identifier`, and because bootstrap builds run with
`lenient_types`, the unresolved name was silently rewritten to a global
(`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:308-313`):

```rust
if self.lenient_types {
    // In lenient mode, treat unknown variables as globals with type ANY
    Ok(HirExpr { kind: HirExprKind::Global(name.to_string()), ty: TypeId::ANY })
}
```

That becomes `MirInst::GlobalLoad`
(`mir/lower/lowering_expr_ident.rs:67`) and finally hits the hard error in
`codegen/llvm/functions.rs:3035`.

The **statement** form was always correct — `stmt_lowering.rs` (`Node::If` with a
`let_pattern`) does the full subject-store / pattern-condition / binding-register
/ payload-extract sequence. Only the value/expression position was broken, which
is why this survived so long.

## The wrong-answer half (worse than the build break)

Under LLVM the build at least *stopped*. Under the JIT there was no diagnostic at
all — the non-existent global read back garbage and **every arm collapsed to the
same value**. Measured on the same source with unpatched vs patched seed:

| expression | unpatched | patched (correct) |
|---|---|---|
| `pick([1,2,3])` | `-93` | `307` |
| `pick(nil)` | `-93` | `-42` |
| `is_leaf(nil)` | `false` | `true` |
| `is_leaf([])` | `false` | `true` |
| `is_leaf([1,2])` | `false` | `false` |

The `is_leaf` row is the real compiler predicate: the unpatched compiler
mis-classified every plain string constant as *not* a constant leaf.

## Fix

`src/compiler_rust/compiler/src/hir/lower/expr/`:

- `mod.rs` — stop discarding `let_pattern`; pass it to `lower_if`.
- `control.rs` — `lower_if` dispatches to a new `lower_if_let_expr`, which mirrors
  the statement path but yields a value: subject stored into a `$if_let_subject`
  local, pattern condition via `if_let_pattern_condition`, bindings registered
  *before* the then-arm is lowered, payload-extraction statements wrapped with the
  then-arm in a `HirExprKind::Block` (the same shape `lower_match_arms` already
  used), bindings restored afterwards.
- `stmt_lowering.rs` — `if_let_pattern_condition` widened to `pub(crate)` so the
  expression path can reuse it rather than fork the logic.

One `Expr::ExistsCheck` layer is unwrapped from the subject, matching the
statement path, so `if val v = expr.?:` binds the unwrapped value rather than the
bool presence check.

## Evidence

- Minimal reproducer, same build config, only the 3 files differing:
  - unpatched: `error: codegen: semantic: llvm global load referenced undeclared symbol \`v\``, no artifact.
  - patched: exit 0, native artifact produced.
- Real construct copied from `module_surface.spl` reproduces the literal symbol
  name `interp_list` unpatched, compiles clean patched.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  advances past codegen to the link stage.
- Rust unit tests `hir:: mir::` — 736 passed / 59 failed **identically** before
  and after (set-inclusion compared, not counts); those 59 are pre-existing at
  `62ccb545718`.

## Regression test

`test/01_unit/compiler/hir/if_val_expression_binding_spec.spl` — every assertion
in it was verified to FAIL on the unpatched seed and PASS on the patched one.

## Follow-up (not done here)

The `lenient_types` fallback at `hir/lower/expr/mod.rs:308` converts *any*
unresolved name into a global with no diagnostic. That turned a one-line scope
bug into a symbol-name-only error thousands of lines from the source, and it
equally hides genuine typos (see
`web_renderer_compose_retained_missing_animation_time_param_2026-08-01.md`, found
in the same stage4 run). It should emit a level-gated warning naming the symbol
and the enclosing function before rewriting the node.
