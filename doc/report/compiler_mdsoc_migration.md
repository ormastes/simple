# Compiler MDSoC Migration Status

**Last Updated:** 2026-03-02
**Overall Status:** Architecture code complete under `src/compiler/85.mdsoc/`. Tests degraded.

## Summary

All MDSOC code lives under `src/compiler/85.mdsoc/` as layer 85 in the numbered compiler layer system. The `85.mdsoc/` prefix is stripped by the module resolver, so imports use `compiler.mdsoc.*`.

| Component | Status | Files | Location |
|-----------|--------|-------|----------|
| Core engine (types, config, checkers) | Code complete | 7 | `85.mdsoc/mdsoc/` |
| D_feature (pipeline stage ports) | Code complete | 24 | `85.mdsoc/feature/` |
| D_transform (stage boundary views) | Code complete | 19 | `85.mdsoc/transform/` |
| D_construct (language construct capsules) | Code complete | 12 | `85.mdsoc/construct/` |
| Adapters (in/out) | Code complete | 5 | `85.mdsoc/adapters/` |
| Weaving (AOP types) | Code complete | 1 | `85.mdsoc/weaving/` |
| D_entity (IR type extraction) | NOT DONE | 0 | Planned: `src/compiler_core/entity/` |
| Port-based pipeline integration | NOT DONE | 0 | Ports defined but not wired |
| Tests | Degraded | 14 files | 21/289 passing |

## What Was Implemented

### Core Engine (`85.mdsoc/mdsoc/`)

- `types.spl` (18K) - All MDSOC type definitions
- `config.spl` (18K) - SDN manifest parser
- `layer_checker.spl` (25K) - Layer enforcement + cycle detection + bypass audit
- `construct_types.spl` (7.6K) - Construct dimension types
- `construct_checker.spl` (6.6K) - Construct tier checker
- `cross_query.spl` (5.7K) - Cross-dimension queries
- `layer_doc_checker.spl` (9.3K) - Public export documentation checker
- `mod.spl` - Module re-exports

### D_feature: Pipeline Stage Ports (`85.mdsoc/feature/`)

12 pipeline stages, each with `__init__.spl` + `app/ports.spl`:
lexing, parsing, desugaring, type_checking, hir_lowering, mir_lowering,
monomorphization, optimization, codegen, linking, module_loading, events

Plus: `codegen/backends/interpreter/backend.spl`

### D_transform: Stage Boundary Views (`85.mdsoc/transform/`)

9 transform boundaries, each with `__init__.spl` + `entity_view/*.spl`:
lexing_to_parsing, parsing_to_desugaring, desugaring_to_typing,
typing_to_hir, hir_to_mir, mir_to_backend, mir_to_optimizer,
backend_to_linker, loading_to_parsing

### D_construct: Language Construct Capsules (`85.mdsoc/construct/`)

12 construct capsules (one per `ConstructKind`):
func, class_struct, enum, trait, variable, control, match, expr, async, block, module, asm

### Adapters (`85.mdsoc/adapters/`)

- Inbound: `language_server_adapter.spl`, `profiler_adapter.spl`
- Outbound: `file_module_storage.spl`, `memory_module_storage.spl`

### Compiler Integration Points

- `src/compiler/80.driver/build/doc_warnings.spl` - Uses MDSOC for `--warn-docs`
- `src/compiler/00.common/compiler_services.spl` - Typed pipeline ports
- `src/compiler/00.common/dependency/visibility.spl` - `extract_layer_number()`
- `src/app/cli/arch_check.spl` - `check-arch` command

## What Was NOT Implemented

### D_entity: IR Type Extraction

The original plan called for extracting stable IR types into `src/compiler_core/entity/` with subdirectories for token, ast, hir, mir, types, and span. This extraction was **never performed**. The entity types remain in their original numbered compiler layers:

- Token types: `src/compiler/10.frontend/`
- AST types: `src/compiler/10.frontend/`
- HIR types: `src/compiler/20.hir/`
- MIR types: `src/compiler/50.mir/`
- Type system: `src/compiler/30.types/`

### Port-Based Pipeline Driver

Port structs are defined in `85.mdsoc/feature/*/app/ports.spl` but the actual compiler pipeline in `80.driver/` still uses direct stage-to-stage function calls. The ports are architectural specifications, not wired into the real compilation flow.

## Test Status (2026-03-02)

14 test files in `test/unit/compiler/mdsoc/`:

| File | Result | Issue |
|------|--------|-------|
| types_spec.spl | FAIL (90 failures) | Multi-struct import: `dict` type |
| config_spec.spl | FAIL (33 failures) | `parse_mdsoc_sdn` not found |
| layer_checker_spec.spl | FAIL | Multi-struct import issues |
| feature_ports_spec.spl | FAIL | Multi-struct import issues |
| transform_adapters_spec.spl | FAIL | Multi-struct import issues |
| construct_types_spec.spl | PASS | |
| construct_checker_spec.spl | PASS | |
| cross_query_spec.spl | PASS | |
| config_multi_dim_spec.spl | PASS | |
| doc_validation_spec.spl | PASS | |
| layer_enforcement_spec.spl | PASS | |
| vc_static_spec.spl | PASS | |
| aop_proceed_spec.spl | SKIP | Pre-existing |
| vc_import_spec.spl | SKIP | Pre-existing |

Root cause: Runtime multi-struct import limitation. Only the first struct in an imported module gets proper method dispatch; subsequent structs become bare `dict` objects.

## Dependency Rules (from arch configs)

```
85.mdsoc/mdsoc/**           - Core engine, no feature/transform imports
85.mdsoc/feature/**         - Pipeline stages, imports via transform or own entity types
85.mdsoc/transform/**       - Imports entity types only, no feature imports
85.mdsoc/adapters/**        - Implements feature ports, no cross-adapter imports
85.mdsoc/construct/**       - Construct capsule definitions
85.mdsoc/weaving/**         - AOP types
```

## References

- Theory: `doc/research/mdsoc_design.md`
- Compiler design: `doc/research/compiler_mdsoc_design.md`
- User guide: `doc/guide/mdsoc_guide.md`
- Implementation plan: `doc/report/compiler_mdsoc_impl_plan.md`
- Phase 3f report: `doc/report/mdsoc_phase3f_feature_ports_2026-02-17.md`
