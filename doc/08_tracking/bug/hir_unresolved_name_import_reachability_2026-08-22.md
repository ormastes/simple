# HIR `unresolved name`: symbols reachable only through re-export edges that do not carry them

- Date: 2026-08-22
- Lane: run13 stage1 HIR error census, class `unresolved name` (60 occurrences, 24 pairs)
- Log: `stage1_build13.log` (worktree `stage1-clean15` @ `7f9a3e1c050`)
- Status: FIXED for the 42 compiler-internal occurrences; 18 std/builtin occurrences deferred (see Scope)

## Symptom

Stage1 HIR lowering emitted `unresolved name: <sym>` and marked the module
`[hir-poisoned]`. Top offenders: `parser_type_kind_named_name` x10 and
`parser_type_kind_array_element_name` x10 (both from
`20.hir/hir_lowering/module_surface_declarations.spl`), `expr_kind` x3 /
`stmt_kind` x2 (`10.frontend/desugar/suspension_analysis.spl`).

## Root cause — one class, four surface forms

Every affected symbol **is defined in the tree**. The caller could only reach it
through a re-export edge that does not actually carry it:

1. **A plain `use X.*` is not a re-export.** `10.frontend/parser_types.spl` does
   `use compiler.frontend.parser_types_expr.*` for its own benefit; nothing
   downstream of `parser_types` sees `parser_types_expr`'s names.
   `module_surface_declarations.spl` and `suspension_analysis.spl` imported only
   `parser_types.*` and so could not see `parser_type_kind_named_name`,
   `parser_type_kind_array_element_name`, `expr_kind`, `stmt_kind`.
2. **A barrel's explicit `export use Y.{...}` brace list omitted the symbol.**
   `20.hir/hir_lowering/module_surface.spl` re-exported five names from
   `module_surface_types` and one from `module_surface_registry_index`, but not
   `module_surface_export_origin_index_lookup` /
   `module_surfaces_frozen_alignment`, which its consumers call.
3. **A caller's own named-import list omitted the symbol.**
   `10.frontend/core/_Ast/module_state.spl` imported
   `compiler.core.ast_types.{CoreExpr, CoreStmt, CoreDecl}` but called
   `make_core_decl`, which is defined in that same module and simply was not named.
4. **A package `__init__` stood in for the defining module.**
   `module_declarations_bootstrap.spl` took `STMT_*` from `compiler.core.{...}`;
   its sibling files (`lowering_helpers.spl`, `trait_impl_lowering.spl`) take the
   same constants from `compiler.core.ast_stmt.{...}` and resolve fine.

**Why it went unseen:** the Rust seed resolves all four forms leniently — a
3-module transitive-glob fixture runs correctly under the seed — so the tree
accumulated these edges invisibly. Pure-Simple HIR lowering enforces them.

**The diagnosis is pinned by a controlled comparison, not inference.**
`parser_type_kind_named_name` is called from 8 files. Seven carry a direct
`use compiler.frontend.parser_types_expr.*` and resolve. The single file that
errors, `module_surface_declarations.spl`, is the only one lacking it. The same
comparison holds for every other pair. Visibility is *not* the mechanism: all 12
functions in `parser_types_expr.spl` are bare `fn`, and bare `const STMT_RETURN`
is imported by name across modules successfully.

## Fix

Repair the import edges at their root — add the symbol to the barrel that is
supposed to carry it, or give the caller the direct import its siblings already
have. **No resolver change**, and no diagnostic suppressed.

| file | change |
|---|---|
| `20.hir/hir_lowering/module_surface.spl` | barrel re-exports `module_surface_export_origin_index_lookup`, `module_surfaces_frozen_alignment` |
| `20.hir/hir_lowering/module_surface_declarations.spl` | direct import of both `parser_type_kind_*` accessors |
| `10.frontend/desugar/suspension_analysis.spl` | direct import of `expr_kind`, `stmt_kind` |
| `10.frontend/core/_Ast/module_state.spl` | `make_core_decl` added to the `ast_types` list |
| `20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl` | `STMT_*` from `compiler.core.ast_stmt`, matching siblings |
| `50.mir/_MirLoweringExpr/switch_operators_calls.spl` | direct import of `bootstrap_mir_logical_module_name` |
| `70.backend/backend/cranelift_codegen_adapter.spl` | direct import of `mir_operand_const_int` |

Precedent: `switch_operators_calls.spl` already carries a comment on the adjacent
line — *"Explicit import, not an ambient builtin: the Rust seed resolves `eprint`…"* —
i.e. an earlier lane repaired this same class the same way.

## Reproduce spec

`test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl` —
static import-edge guard, one `it` per sub-cause.
Measured: **pre-fix 0 passed / 6 failed; post-fix 6 passed / 0 failed.**

## Verification

Seed `compile` of all 7 edited files produces byte-identical diagnostics before
and after the change (the residual `cannot compile to standalone SMF` /
`runtime_file_rename` errors are pre-existing and unrelated), so no regression
was introduced.

## Scope / deferred

18 of the 60 occurrences name std or builtin symbols whose defining module is
ambiguous in this tree (`exit`, `char_code`, `file_lock`/`file_unlock`,
`is_windows` — each with 4+ candidate definitions across `src/lib`) or are types
that overlap the sibling `unresolved type` lane (`JitInstantiator`,
`JitInstantiatorConfig`, `TargetOS`), plus `raise` in generated
`hir/generated/hir_visitor.spl`. These were deliberately NOT guessed at; they
need per-symbol provenance decisions and are left open.

## Overlap actually observed with the sibling lane

While this lane was in flight the sibling `unresolved type` lane landed
`1aa81cac8c6`, which independently and **identically** repaired two of the seven
files — the direct `parser_types_expr` imports in `module_surface_declarations.spl`
and `suspension_analysis.spl` (25 of the 60 occurrences: `parser_type_kind_named_name`
x10, `parser_type_kind_array_element_name` x10, `expr_kind` x3, `stmt_kind` x2).
Two lanes reaching the same edit from opposite error classes is independent
confirmation of the diagnosis. Those two files were dropped from this change in
favour of the landed version; the remaining five repairs (the `module_surface`
barrel, `make_core_decl`, the `STMT_*` package-`__init__` route, and the two MIR
imports) were verified still absent at `1aa81cac8c6` and are carried here.

## Relationship to the sibling `unresolved type` lane

The `unresolved type` class (worktree `hir-unres-1`) is very likely the SAME
root cause applied to types reached through the same barrel/glob edges. This
lane deliberately landed the **narrower half**: source-level import edges only,
touching no resolver function, so the two lanes cannot collide. If that lane
concludes the correct fix is to make re-export traversal transitive in the
resolver, these import edges remain correct and harmless.
