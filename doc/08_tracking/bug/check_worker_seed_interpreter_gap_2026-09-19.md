# Stale-seed interpreter gaps block the `simple check` worker tree

Date: 2026-09-19
Lane: suite-2026-09-18 (Windows, seed binary at `bin/simple.exe`, built 2026-09-17)

## Symptom

`bin/simple.exe check <file>` (and any spec that spawns the CLI as a child
process, e.g. `test/01_unit/app/cli/check_clean_file_passes_spec.spl`) exits 1
with no usable diagnostic even for a trivial valid file:

```
[jit-fallback] MIR lowering error: Unsupported HIR construct: unknown variant
or method 'Integer' on enum TokenKind ... [in src/app/check/main.spl]:
whole module dropped to the interpreter
...
error[semantic]: unsupported expression kind: HirExprKind::NamedVar((SymbolId(id: 2), print))
```

## Chain of causes (verified 2026-09-19)

1. The seed cannot JIT `src/app/check/main.spl` (TokenKind::Integer gap) and
   falls back to the tree-walk interpreter.
2. In the interpreted worker closure, two genuine tree bugs fired first and
   were FIXED in commit 4fdc9897b8e on suite-2026-09-18:
   - `TypeInferError(message: ..., span: ...)` bare enum construction in
     inference_control.spl (x2), inference_expr.spl, inference_expr_ops.spl
     (E1002 "function TypeInferError not found").
   - `create_trait_solver_for_resolution()` named abandoned arena-indexed
     fields (impl_arena, impl_trait_head/tail, impl_type_head/tail,
     impl_next_by_trait/type) that do not exist on class TraitSolver
     ("class TraitSolver has no field named impl_arena"). The pinned fix
     keeps impls/impls_by_type/assoc_resolver unset: the quiet typed mode
     (resolve_methods_quiet_typed_spec) depends on the nil-receiver bail.
3. Remaining blocker: under the seed interpreter, the type-inference match in
   `synthesize_expr` mis-dispatches on `HirExprKind` variants (same seed gap
   family as TokenKind::Integer) and falls into the catch-all
   `TypeInferError.Other("unsupported expression kind: ...")` for an
   ordinary `print("hello")` call. This is a SEED capability gap, not a tree
   bug: the pure-Simple compiler is the reference implementation and the
   suite's app/cli child-process specs are designed to run against it.

## Impact

- All `test/01_unit/app/cli/*` specs that exec `bin/simple.exe <subcommand>`
  as a child are red on Windows until either (a) the pure-Simple binary is
  deployable (blocked by the documented HIR-tail memory accumulation), or
  (b) the seed interpreter's enum-variant match dispatch is fixed.
- `resolve_methods_quiet_typed_spec.spl` quiet examples (2 of 4) remain red
  on main independently of the seed (checked against pristine HEAD: 4/4 red;
  commit 4fdc9897b8e improves to 2/4).

## Related

- doc/08_tracking/bug/jit_co_compiled_definition_ambiguity_debt_2026-09-15.md
  (dispatch-by-import-path debt; same wide-closure sensitivity seen here)
