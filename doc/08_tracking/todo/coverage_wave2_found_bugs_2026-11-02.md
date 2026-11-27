# Coverage-wave-2 found bugs (deferred, TODO 432-436)

Source: `doc/09_report/generics_coverage_baseline.md` (Wave 2). Not fixed in the coverage lane; 50.mir was owned by phase-3 work.
Each has a fail-fast spec tagged `@tag:in-development`; no implementation yet.

| TODO | Location | Bug | Spec |
|---|---|---|---|
| 432 | `src/compiler/50.mir/mir/ghost_erasure.spl:79` | `for func in module.functions` iterates a `Dict<SymbolId, MirFunction>` and yields `(key, value)` tuples; `erase_ghost_from_function` fails with "unknown property or method 'locals' on Tuple" for any non-empty module | `test/01_unit/compiler/50.mir/ghost_erasure_dict_iteration_todo_spec.spl` |
| 433 | `src/compiler/50.mir/_MirLowering/function_lowering.spl:1212` | returns `MirType.i64()` for every `Any` before the `HirTypeKind.Any` arm, so the profile-gated `E-MIR-TYPE-Any` (fatal under `critical`) never fires | `test/01_unit/compiler/50.mir/function_lowering_any_early_return_todo_spec.spl` |
| 434 | `src/compiler/20.hir/hir_function_selection_v1.spl:55` | `hir_prune_published_templates_v1` returns a nil module from non-optional `-> HirModule`; the runtime rejects the return so the nil guard cannot work | `test/01_unit/compiler/20.hir/hir_function_selection_nil_guard_todo_spec.spl` |
| 435 | `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:411,415` | the flat-AST bridge drops `@repr` / `@align` / `@packed` (builds structs and classes with `attributes: []`), drops trait type params and associated types, and sets `has_bits` / `@preserve_order` unconditionally on bitfields | `test/01_unit/compiler/20.hir/flat_ast_bridge_attributes_todo_spec.spl` |
| 436 | `src/compiler/50.mir/_MirLowering/function_lowering.spl:1534-1540` | `[mir-lower-stmt-probe]` with `SIMPLE_COMPILER_TRACE=1` aborts on the seed with "type mismatch: cannot convert tuple to int" (suspected `_sffi_hir_type_discriminant(stmt.kind)` on a `HirStmtKind`); trace-only | `test/01_unit/compiler/50.mir/function_lowering_stmt_probe_trace_todo_spec.spl` |
