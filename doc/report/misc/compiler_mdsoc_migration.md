# Compiler MDSoC Migration Status

**Last Updated:** 2026-03-12
**Overall Status:** Architecture code complete. All 288 tests passing. L0 layer violations fixed (Span unification, HIR-dep files moved to L35).

## Summary

All MDSOC code lives under `src/compiler/85.mdsoc/` as layer 85 in the numbered compiler layer system (17 layers total: 00.common, 10.frontend, 15.blocks, 20.hir, 25.traits, 30.types, 35.semantics, 40.mono, 50.mir, 55.borrow, 60.mir_opt, 70.backend, 80.driver, 85.mdsoc, 90.tools, 95.interp, 99.loader). The `85.mdsoc/` prefix is stripped by the module resolver, so imports use `compiler.mdsoc.*`. A symlink `src/compiler/mdsoc` -> `85.mdsoc` works around a numbered-directory resolution bug in the runtime interpreter. Old unnumbered dirs (`core/`, `linker/`) have been deleted or emptied; their contents migrated to numbered layers.

| Component | Status | Files | Location |
|-----------|--------|-------|----------|
| Core types (one-struct-per-file) | Complete | 14 | `85.mdsoc/types/` |
| Checker types | Complete | 4 | `85.mdsoc/checker_types/` |
| Construct types | Complete | 6 | `85.mdsoc/construct_types/` |
| Config parser | Complete | 1 | `85.mdsoc/config.spl` |
| Layer checker | Complete | 1 | `85.mdsoc/layer_checker.spl` |
| Layer doc checker | Complete | 1 | `85.mdsoc/layer_doc_checker.spl` |
| Construct checker | Complete | 1 | `85.mdsoc/construct_checker.spl` |
| Cross-dimension queries | Complete | 1 | `85.mdsoc/cross_query.spl` |
| D_feature (pipeline stage ports) | Complete | 46 | `85.mdsoc/feature/` |
| D_transform (stage boundary views) | Complete | 21 | `85.mdsoc/transform/` |
| D_construct (capsule data) | Deleted | 0 | Dead boilerplate removed |
| Adapters (in/out) | Complete | 5 | `85.mdsoc/adapters/` |
| Weaving (AOP types) | Complete | 8 | `85.mdsoc/weaving/` |
| Hub re-exports | Complete | 3 | `85.mdsoc/{types,construct_types,mod}.spl` |
| D_entity (IR type extraction) | NOT DONE | 0 | Planned: `src/compiler_core/entity/` |
| Port-based pipeline integration | NOT DONE | 0 | Ports defined but not wired |
| Tests | **Passing** | 13 files | **288/288 passing** |

## One-Struct-Per-File Refactor (2026-03-02)

### Root Cause

The runtime interpreter only registers the first `struct` per imported module in the `struct_table`. All subsequent structs are created as bare `dict` objects without methods, causing 268/289 test failures with errors like `method 'name' not found on type 'dict'`.

### Solution

Split all multi-struct files into one struct per file:

| Original File | Split Into | Location |
|--------------|-----------|----------|
| `types.spl` (580 lines, 14 types) | 14 individual files | `types/` |
| `layer_checker.spl` types (4 structs) | 4 files | `checker_types/` |
| 11 `ports.spl` files (2-3 structs each) | ~26 individual port files | `feature/*/app/` |
| `construct_types.spl` (6 types) | 6 files | `construct_types/` |
| `weaving/types.spl` (7 types) | 7 files | `weaving/` |
| `transform/*/entity_view/MirView.spl` | 2 files (MirProgram + MirDebugInfo) | `transform/feature/mir_to_backend/entity_view/` |

Hub re-export files (`types.spl`, `construct_types.spl`) provide backward-compatible `use compiler.mdsoc.types.*` imports.

### Directory Flattening

Before: `85.mdsoc/mdsoc/{types/,checker_types/,...}` (double `mdsoc` caused resolution failure)
After: `85.mdsoc/{types/,checker_types/,...}` (flat)

### Symlink Workaround

**`src/compiler/mdsoc` -> `85.mdsoc`**

The runtime interpreter's `resolve_module_path()` has 5 resolution strategies. Strategy 5 (numbered directory resolution via `resolve_with_numbered_dirs()`) finds the correct file paths but `register_module_functions()` only calls `irt_track_struct()`/`irt_track_enum()` for resource tracking — it does NOT call `struct_table_register()`. This means structs loaded through numbered-dir resolution can't be constructed.

The symlink forces strategy 3 (direct `src/` path: `src/compiler/mdsoc/types/caret_id.spl`) to match, bypassing the bug entirely.

### Other Convenience Symlinks

The compiler directory also has convenience symlinks for frequently-imported layers:

| Symlink | Target | Purpose |
|---------|--------|---------|
| `src/compiler/common` | `00.common` | Shorthand imports |
| `src/compiler/frontend` | `10.frontend` | Shorthand imports |
| `src/compiler/mir` | `50.mir` | Shorthand imports |
| `src/compiler/backend` | `70.backend/backend` | Direct access to backend subdir |
| `src/compiler/driver` | `80.driver` | Shorthand imports |
| `src/compiler/mdsoc` | `85.mdsoc` | Runtime resolution workaround |
| `src/compiler/interp` | `95.interp` | Shorthand imports |
| `src/compiler/loader` | `99.loader` | Shorthand imports |

Additionally, `src/compiler/linker/` exists as an empty directory (its contents were deleted: `smf_reader.spl` moved to `70.backend/linker/`).

### Cleanup

- Deleted 36 dead boilerplate files (12 construct capsule data + 24 `arch {}` metadata-only `__init__.spl`)
- Removed empty `construct/` subdirectories
- Fixed 2 stale consumer files (`doc_warnings.spl`, `check_capsule.spl`)
- Fixed import paths in test files (`compiler.feature.` -> `compiler.mdsoc.feature.`, `compiler.transform.` -> `compiler.mdsoc.transform.`)
- Deleted old unnumbered `core/` directory files (`aop_debug_log.spl`, `backend_types.spl`, `interpreter/jit.spl`, `lexer.spl`) — migrated to numbered layers
- Deleted `linker/smf_reader.spl` — moved to `70.backend/linker/`
- Old unnumbered dirs (`core/`, `linker/`) are now empty or deleted; remaining unnumbered dirs (`common`, `frontend`, `mir`, `backend`, `driver`, `interp`, `loader`, `mdsoc`) are convenience symlinks to their numbered counterparts

## What Was Implemented

### Core Engine (`85.mdsoc/`)

- `types/` (14 files) - All MDSOC type definitions, one struct per file
- `checker_types/` (4 files) - Layer violation, doc violation, bypass audit/report
- `construct_types/` (6 files) - Construct dimension types
- `config.spl` - SDN manifest parser
- `layer_checker.spl` - Layer enforcement + cycle detection + bypass audit
- `construct_checker.spl` - Construct tier checker
- `cross_query.spl` - Cross-dimension queries
- `layer_doc_checker.spl` - Public export documentation checker
- `mod.spl` - Module re-exports
- `types.spl` - Hub re-export for `use compiler.mdsoc.types.*`
- `construct_types.spl` - Hub re-export for `use compiler.mdsoc.construct_types.*`

### D_feature: Pipeline Stage Ports (`85.mdsoc/feature/`)

12 pipeline stages, each with `__init__.spl` + `app/ports.spl` (hub) + individual port files:
lexing, parsing, desugaring, type_checking, hir_lowering, mir_lowering,
monomorphization, optimization, codegen, linking, module_loading, events

Plus: `codegen/backends/interpreter/backend.spl`

### D_transform: Stage Boundary Views (`85.mdsoc/transform/`)

9 transform boundaries, each with `__init__.spl` + `entity_view/*.spl`:
lexing_to_parsing, parsing_to_desugaring, desugaring_to_typing,
typing_to_hir, hir_to_mir, mir_to_backend, mir_to_optimizer,
backend_to_linker, loading_to_parsing

### Weaving (`85.mdsoc/weaving/`)

8 files: advice_form, join_point_kind, join_point, matched_advice, weaving_rule, weaving_config, weaving_result, types (hub)

### Adapters (`85.mdsoc/adapters/`)

- Inbound: `language_server_adapter.spl`, `profiler_adapter.spl`
- Outbound: `file_module_storage.spl`, `memory_module_storage.spl`

### Compiler Integration Points

- `src/compiler/80.driver/build/doc_warnings.spl` - Uses MDSOC for `--warn-docs`
- `src/compiler/00.common/compiler_services.spl` - Typed pipeline ports
- `src/compiler/00.common/dependency/visibility.spl` - `extract_layer_number()`
- `src/app/cli/arch_check.spl` - `check-arch` command
- `src/app/cli/check_capsule.spl` - `check-capsule` command

## L0 Layer Violation Fixes (2026-03-12)

### Span Unification (L0→L1 eliminated)
Canonical `Span` now lives in `00.common/diagnostics/span.spl`. Previously 4 duplicate definitions existed across `00.common`, `10.frontend/lexer_types.spl`, `10.frontend/block_types.spl`, and `10.frontend/core/lexer_types.spl` (bootstrap, untouched). All 8 L0 files that imported Span from frontend now import from `diagnostics.span`. The frontend files re-import from common.

### env_get Inlined (L0→L7 eliminated)
`config.spl` inlined `extern fn rt_env_get` to remove its import from `compiler.backend.ffi`. `compiler_services.spl` BackendPort import documented as orchestration bypass.

### HIR Files Moved to L35 (L0→L2 eliminated)
4 files moved from `00.common/` to `35.semantics/`: `unsafe.spl`, `volatile.spl`, `visibility_checker.spl`, `visibility_integration.spl`. These are semantic analysis passes that import HIR types — they don't belong in L0.

### Remaining Bypasses
- `compiler_services.spl`: BackendPort (L0→L7, orchestration type)
- `attributes.spl`: Attribute/Expr from L1, LayoutAttr from L3 (split deferred — L1 consumer blocks clean separation)

## What Was NOT Implemented

### D_entity: IR Type Extraction

The original plan called for extracting stable IR types into `src/compiler_core/entity/` with subdirectories for token, ast, hir, mir, types, and span. This extraction was **never performed** -- `src/compiler_core/` does not exist. The entity types remain in their original numbered compiler layers:

- Token types: `src/compiler/10.frontend/` (lexer, parser types)
- AST types: `src/compiler/10.frontend/` (parser, treesitter)
- HIR types: `src/compiler/20.hir/`
- Trait types: `src/compiler/25.traits/`
- Type system: `src/compiler/30.types/`
- MIR types: `src/compiler/50.mir/`
- Backend types: `src/compiler/70.backend/`

### Port-Based Pipeline Driver

Port structs are defined in `85.mdsoc/feature/*/app/` but the actual compiler pipeline in `80.driver/` still uses direct stage-to-stage function calls. The ports are architectural specifications, not wired into the real compilation flow.

## Test Status (2026-03-02)

13 test files in `test/unit/compiler/mdsoc/`:

| File | Result | Tests |
|------|--------|-------|
| types_spec.spl | PASS | 90 |
| config_spec.spl | PASS | 33 |
| layer_checker_spec.spl | PASS | 43 |
| feature_ports_spec.spl | PASS | 35 |
| transform_adapters_spec.spl | PASS | 67 |
| layer_enforcement_spec.spl | PASS | 13 |
| construct_types_spec.spl | PASS (skipped) | Pre-existing |
| construct_checker_spec.spl | PASS (skipped) | Pre-existing |
| cross_query_spec.spl | PASS (skipped) | Pre-existing |
| config_multi_dim_spec.spl | PASS (skipped) | Pre-existing |
| doc_validation_spec.spl | PASS (skipped) | Pre-existing |
| vc_static_spec.spl | PASS (skipped) | Pre-existing |
| vc_import_spec.spl | PASS (skipped) | Pre-existing |

**Total: 288 passed, 0 failed**

## Dependency Rules (from arch configs)

```
85.mdsoc/**             - Core engine, no feature/transform imports
85.mdsoc/feature/**     - Pipeline stages, imports via transform or own entity types
85.mdsoc/transform/**   - Imports entity types only, no feature imports
85.mdsoc/adapters/**    - Implements feature ports, no cross-adapter imports
85.mdsoc/weaving/**     - AOP types
```

## Import Patterns

### Preferred: Individual imports (one-struct-per-file)

```simple
use compiler.mdsoc.types.caret_id.{CaretId}
use compiler.mdsoc.types.layer_def.{LayerDef}
use compiler.mdsoc.types.virtual_capsule.{VirtualCapsule}
use compiler.mdsoc.checker_types.layer_violation.{LayerViolation}
```

### Backward-compatible: Hub imports

```simple
use compiler.mdsoc.types.*
use compiler.mdsoc.construct_types.*
```

## References

- Theory: `doc/research/mdsoc_design.md`
- Compiler design: `doc/research/compiler_mdsoc_design.md`
- User guide: `doc/guide/mdsoc_guide.md`
- Implementation plan: `doc/report/compiler_mdsoc_impl_plan.md`
- Phase 3f report: `doc/report/mdsoc_phase3f_feature_ports_2026-02-17.md`
- Feature status: `doc/feature/mdsoc_complete.md`
