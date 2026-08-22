# HIR `unresolved name`: symbols reachable only through re-export edges that do not carry them

- Date: 2026-08-22
- Lane: run13 stage1 HIR error census, class `unresolved name` (60 occurrences, 24 pairs)
- Log: `stage1_build13.log` (worktree `stage1-clean15` @ `7f9a3e1c050`)
- Status: FIXED. Iteration 1 cleared 42 compiler-internal occurrences; iteration 2 (below) clears the 18 deferred std/builtin/generated ones. Class B is empty.

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


---

# Iteration 2 (2026-08-22) — the 18 deferred occurrences

Iteration 1 deferred `exit`, `char_code`, `file_lock`, `file_unlock`,
`is_windows`, `TargetOS`, `JitInstantiator`, `JitInstantiatorConfig` and `raise`
because each names a symbol with 4+ candidate definitions in `src/lib` and the
lane refused to guess. Per-symbol provenance is now settled. They are the same
class as iteration 1 — a caller reaching a symbol through an edge that does not
carry it — in **four further surface forms**, none of which needed a resolver
change or a widened glob.

## 5. A `use` nested INSIDE a function body

`70.backend/linker/link.spl` carried `use std.platform.{is_windows, is_unix}`,
`use std.common.target.TargetOS` and a second `use std.platform.is_windows`
*inside* function bodies; `70.backend/codegen.spl` carried
`use compiler.loader.jit_instantiator.{JitInstantiator, JitInstantiatorConfig}`
inside a method body. The Rust seed honours a body-local `use`; stage1 HIR
lowering does not, and reports `unresolved name` at the enclosing declaration.
Fix: hoist all four to module level. The module paths were already correct —
only their position was wrong — so this is a pure relocation, and the
`jit_instantiator` names merge into the module-level `{JitStats}` import that
was already there.

## 6. No import at all, relying on an ambient builtin

- `exit` in `20.hir/hir_codec_support.spl` (`exit(1)` in `hc_bad_tag`). Owner is
  `std.nogc_sync_mut.io_runtime` (`pub fn exit`, `io_runtime.spl:315`); a second
  `fn exit` in `io/signal_handlers.spl` is why the barrel is not usable, so the
  direct module path is required. Precedent: `00.common/transition/check_main.spl`
  already imports `exit` by name.
- `char_code` in `10.frontend/core/parser_decls_use.spl`. Owner is
  `std.string_core` (`src/lib/common/string_core.spl:396`) — the same import the
  sibling `80.driver/driver_source_pipeline_parsing.spl` already carries and
  which does not error, which is the controlled comparison that pins it.

## 7. A barrel name that COLLIDES (not one that omits)

`use std.io.{file_lock, file_unlock, file_exists, file_write}` in
`80.driver/driver_source_pipeline_parsing.spl` and `80.driver/driver_hir_cache.spl`
failed on exactly the two lock names while the other two resolved. The barrel is
not missing them — `io/__init__.spl:107` exports them on a line adjacent to the
one exporting `file_exists`/`file_write` (`:104`). The discriminator is that
`file_lock` and `file_unlock` are each defined **twice** in modules that
`io/__init__.spl` re-exports from: `io/file_ops.spl:128,134` and
`sffi/io.spl:158,162` (identical signatures). `file_exists` is defined once.
So this is a re-export *ambiguity*, and it is the mirror image of forms 1-4.
Fix: import from the canonical owner directly —
`use std.io.file_ops.{file_lock, file_unlock}` — which the barrel itself names
as authoritative ("File mutation stays owned by file_ops", `io/__init__.spl:116`).
The std barrel is left untouched: deduplicating it is a separate, wider change.

## 8. GENERATED code calling `raise`

`raise` is **not a keyword** (no token, no lexer entry) and has **no definition
anywhere in `src/lib`** — `/usr/bin/grep -rn "fn raise" src/` finds only
`raise_to_top`, `raise_error` and vendored Rust. The Rust seed itself says so:
pre-fix, `simple compile src/compiler/20.hir/generated/hir_visit.spl` reports
`Undefined("undefined identifier: raise")`. Three generated files emitted it:
`20.hir/generated/hir_visitor.spl`, `20.hir/generated/hir_visit.spl`,
`10.frontend/generated/ast_visitor.spl`.

Fixed at the **generator**, not the output: `src/app/compiler_schema/fold_gen.spl`
and `src/app/compiler_schema/visitor_gen.spl` now emit
`use std.nogc_sync_mut.io_runtime.{exit}` in the generated header and replace
`raise "MSG"` with `exit(1)` followed by `"MSG"` as the declared `-> text` tail.
Loudness is preserved exactly: the adjacent `print` of the same diagnostic is
untouched, and the abort is now real rather than a call into nothing.

**Generator trap found while doing this:** the emitted literal must be written
`io_runtime.{{exit}}`. Written singly, `{exit}` is string INTERPOLATION and the
first regeneration emitted `use std.nogc_sync_mut.io_runtime.<closure@0x...>`.
The same trap applies to the spec below, whose brace literals are escaped.
After the fix, `bin/simple run src/app/compiler_schema/main.spl visitors`
reproduces all three files byte-identically to the committed content.

## Verification

- Seed `compile` of all 9 touched files, before vs after, is diagnostically
  identical **except** that the three `undefined identifier: raise` errors are
  gone, replaced by the pre-existing, unrelated `runtime_file_rename` residual
  that every other file in the set already shows. No new error anywhere.
- Generator round-trip: regeneration is byte-identical (see above).
- Spec `test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl`
  extended with 7 new `it` blocks, one per sub-cause. Measured on this tree:
  **pre-fix 6 passed / 7 failed; post-fix 13 passed / 0 failed.**

## Coverage of class B

Iteration 1 (42) + the sibling `1aa81cac8c6` (25, overlapping) + iteration 2 (18)
account for all 85 `unresolved name` occurrences in the run13 census. Nothing in
class B is left open.

## Pre-push gate record (iteration 2 landing)

`check-test-tree-divergence-delta.shs 5d888bd349d <tip>` verdict:
**PASS — 1 pre-existing offender(s), 0 introduced by this range**
(base verdict: `FAIL — 855 diverged vs 854 baselined (1 new, 0
fixed-but-still-baselined); 1 mirror-only`). The pre-existing offender list is
recorded at `/mnt/data/tmp/test_tree_divergence_preexisting.txt`; this change
touches no file under `test/` other than the single spec named above, and that
spec has no mirror-tree counterpart, so it introduces zero divergence.

Other gates on this range: `check-no-conflict-tree-push` PASS (1 commit),
`check-no-conflict-markers-push` PASS (13 files), `check-tree-size-push` PASS
(base 118047 files, 0 structural faults), `check-runtime-api-regression-push`
PASS (2813 symbols, 0 removed).

**Blocked gate, recorded not stepped over silently:** `check-push-must-pass.shs`
FAILs for every `src/`-touching push on this tree, independently of this change —
`doc/08_tracking/check/must_check_db.sdn` carries
`source_fingerprint: "unrecorded"` and every bootstrap row is `todo`, so the
fingerprint comparison can never match. Refreshing it requires a full
`bootstrap-from-scratch --full-bootstrap --deploy` receipt, which this lane does
not own.
