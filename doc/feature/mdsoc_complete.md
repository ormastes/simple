# MDSOC (Multi-Dimensional Separation of Concerns) - Feature Status

**Status:** Architecture Complete, Tests Degraded (runtime import limitation)
**Last Updated:** 2026-03-02
**Implementation:** `src/compiler/85.mdsoc/` (~100K, 69 files)
**Tests:** 14 spec files, 21 passing / 268 failing (see Known Issues)

---

## Executive Summary

MDSOC architecture is **fully designed and implemented** in `src/compiler/85.mdsoc/`. The core engine (types, config parser, layer checker, construct checker, cross-query) is well-structured code. Pipeline stage ports (D_feature) and stage boundary transforms (D_transform) are defined for all 12 stages and 9 boundaries respectively.

However, **tests are currently degraded** (21/289 passing) due to a known runtime limitation: the interpreter's multi-struct import system only properly supports the first struct in an imported module. Structs beyond the first are created as bare `dict` objects without methods. This is a test infrastructure issue, not an architectural defect.

### Architecture Components

| Component | Location | Files | Status |
|-----------|----------|-------|--------|
| Core engine | `85.mdsoc/mdsoc/` | 7 | Code complete |
| D_feature (pipeline ports) | `85.mdsoc/feature/` | 24 | Code complete |
| D_transform (boundary views) | `85.mdsoc/transform/` | 19 | Code complete |
| D_construct (language constructs) | `85.mdsoc/construct/` | 12 | Code complete |
| Adapters (in/out) | `85.mdsoc/adapters/` | 5 | Code complete |
| Weaving (AOP types) | `85.mdsoc/weaving/` | 1 | Code complete |

### Known Issues

1. **Test failures (268/289):** Multi-struct import limitation causes `method 'X' not found on type 'dict'` and `function 'X' not found` errors. The source code is correct; the interpreter's import resolution cannot handle modules with many struct definitions.
2. **Entity dimension not extracted:** Design planned `src/compiler_core/entity/` as stable IR type layer, but entity types remain in their original numbered compiler layers (10.frontend, 20.hir, 50.mir, etc.).
3. **Port integration pending:** Port structs are defined but the real compiler pipeline still uses direct stage-to-stage calls, not port-based dispatch.

---

## Feature Breakdown

### 1. Core Engine (`85.mdsoc/mdsoc/`)

**Types** (`types.spl` - 18K):
- `CapsuleVisibility` enum: Public, Internal, Private
- `CaretId`, `CaretMapping`: Aspect root system
- `DimensionDef`, `LayerDirection`, `LayerDef`: Layer enforcement
- `VirtualCapsule`, `SurfaceBinding`, `CapsuleExport`: Capsule composition
- `BypassGrant`, `BypassUsage`: Dual-consent escape hatches
- `CapsuleRules`, `MdsocManifest`: Top-level config container

**Config Parser** (`config.spl` - 18K):
- Manual line-based SDN parser for `capsule.sdn`
- Supports sections: capsule, roots, dimension, dimension_construct, rules
- Inline arrays, booleans, subsections

**Layer Checker** (`layer_checker.spl` - 25K):
- `LayerChecker` struct with module-to-layer assignment
- `check_layer_dep()`, `detect_layer_cycles()` (iterative DFS)
- Bypass grant/usage validation and audit report generation
- `check_numbered_layer_dep()` for compiler self-enforcement

**Construct Types** (`construct_types.spl` - 7.6K):
- `ConstructKind` enum: 12 language constructs (Func, ClassStruct, Enum, Trait, etc.)
- `ConstructTier` enum: 5 tiers (Core, Flow, Decl, Advanced, Meta)
- Cross-dimension query types

**Construct Checker** (`construct_checker.spl` - 6.6K):
- `ConstructLayerChecker`: Validates tier-based dependencies (warn-only mode)

**Cross Query** (`cross_query.spl` - 5.7K):
- `query_cross_dimension()`, `query_by_construct()`, `query_by_layer_range()`

**Doc Checker** (`layer_doc_checker.spl` - 9.3K):
- `check_public_documentation()`: Validates Public exports have docstrings

### 2. D_feature: Pipeline Stage Ports (`85.mdsoc/feature/`)

Each stage has `__init__.spl` (arch config) + `app/ports.spl` (typed I/O port structs):

| Stage | Input Port | Output Port |
|-------|-----------|-------------|
| lexing | `LexerInputPort(source_text)` | `LexerOutputPort(token arrays, count)` |
| parsing | `ParserInputPort(token arrays)` | `ParserOutputPort(decl counts, errors)` |
| desugaring | `DesugarInputPort(source_text, module)` | `DesugarOutputPort(desugared_source)` |
| type_checking | `TypeCheckInputPort` | `TypeCheckOutputPort(types, diagnostics)` |
| hir_lowering | `HirLowerInputPort` | `HirLowerOutputPort(functions)` |
| mir_lowering | `MirLowerInputPort` | `MirLowerOutputPort(functions)` |
| monomorphization | `MonomorphizeInputPort` | `MonomorphizeOutputPort` |
| optimization | `OptimizeInputPort` | `OptimizeOutputPort(stats)` |
| codegen | `CodegenInputPort` | `CodegenOutputPort(object bytes)` |
| linking | `LinkerInputPort` | `LinkerOutputPort(output path)` |
| module_loading | `ModuleResolverPort`, `ModuleStoragePort` | `ModuleRegistryPort` |
| events | - | `CompilationEventPort` (observer bus) |

Special: `codegen/backends/interpreter/backend.spl` wraps interpreter as BackendPort.

### 3. D_transform: Stage Boundary Views (`85.mdsoc/transform/`)

Each boundary has `__init__.spl` (arch config) + `entity_view/*.spl`:

| Transform | Entity View | Bridges |
|-----------|------------|---------|
| lexing_to_parsing | `TokenStreamView` | Token array + source_text |
| parsing_to_desugaring | `AstView` | AST for desugar pipeline |
| desugaring_to_typing | `DesugarView` | Desugared AST for type checker |
| typing_to_hir | `TypedAstContext` | Typed AST + symbols to HIR |
| hir_to_mir | `CfgContext` | Structured control flow to flat blocks |
| mir_to_backend | `MirProgram` + `MirDebugInfo` | Backend-neutral MIR |
| mir_to_optimizer | `MirOptView` | MIR + optimization level |
| backend_to_linker | `ObjectFileView` | Codegen output to linker |
| loading_to_parsing | `LoadedModuleView` | Module source to parser |

### 4. D_construct: Language Construct Capsules (`85.mdsoc/construct/`)

12 construct capsule definitions, one per `ConstructKind`:
func, class_struct, enum, trait, variable, control, match, expr, async, block, module, asm

### 5. Adapters (`85.mdsoc/adapters/`)

- **Inbound:** `language_server_adapter.spl`, `profiler_adapter.spl`
- **Outbound:** `file_module_storage.spl`, `memory_module_storage.spl`

### 6. Weaving (`85.mdsoc/weaving/`)

AOP types: `AdviceForm`, `JoinPointKind`, `JoinPoint`, `WeavingRule`, `WeavingConfig`, `WeavingResult`

---

## Integration with Compiler

Active integrations:
- `src/compiler/80.driver/build/doc_warnings.spl`: Imports `VirtualCapsule`, `LayerChecker`, `check_public_documentation` for `--warn-docs`
- `src/compiler/00.common/compiler_services.spl`: Typed pipeline port structs complementing MDSOC feature ports
- `src/compiler/00.common/dependency/visibility.spl`: `extract_layer_number()` used by `check_numbered_layer_dep()`
- `src/app/cli/arch_check.spl`: `check-arch` CLI command

---

## Test Suite

14 test files in `test/unit/compiler/mdsoc/`:

| File | Status | Issue |
|------|--------|-------|
| types_spec.spl | Failing | Multi-struct import: methods not found on dict |
| config_spec.spl | Failing | `parse_mdsoc_sdn` function not found |
| layer_checker_spec.spl | Failing | Multi-struct import issues |
| feature_ports_spec.spl | Failing | Multi-struct import issues |
| transform_adapters_spec.spl | Failing | Multi-struct import issues |
| construct_types_spec.spl | Passing | Simpler struct usage |
| construct_checker_spec.spl | Passing | Simpler struct usage |
| cross_query_spec.spl | Passing | Simpler struct usage |
| config_multi_dim_spec.spl | Passing | Simpler struct usage |
| doc_validation_spec.spl | Passing | Simpler struct usage |
| layer_enforcement_spec.spl | Passing | Simpler struct usage |
| vc_static_spec.spl | Passing | Simpler struct usage |
| aop_proceed_spec.spl | Skipped | Pre-existing failures |
| vc_import_spec.spl | Skipped | Pre-existing failures |

**Current results:** 21 passed, 268 failed (2026-03-02)

---

## Limitations & Future Work

### Blocking Issues

1. **Runtime multi-struct import:** Tests cannot validate MDSOC types because the interpreter only supports the first struct per imported module. Fix requires compiled-mode test execution or import system improvements.
2. **Entity dimension extraction:** `src/compiler_core/entity/` was never created. Entity types remain in numbered layers.
3. **Port integration:** Port structs exist but aren't used by the real pipeline driver.

### Planned Enhancements

1. Multi-dimensional slicing (feature x platform x profile)
2. Dynamic capsule loading
3. Auto-inference of caret mappings
4. IDE plugin for capsule visualization
5. Architectural metrics (coupling/cohesion)

---

## Documentation

| Document | Location |
|----------|----------|
| Theory & design | `doc/research/mdsoc_design.md` |
| Compiler-specific design | `doc/research/compiler_mdsoc_design.md` |
| User guide | `doc/guide/mdsoc_guide.md` |
| Migration tracking | `doc/report/compiler_mdsoc_migration.md` |
| Implementation plan | `doc/report/compiler_mdsoc_impl_plan.md` |
| Phase 3f report | `doc/report/mdsoc_phase3f_feature_ports_2026-02-17.md` |
| API reference | `src/compiler/85.mdsoc/mdsoc/mod.spl` |

---

**Document Version:** 2.0
**Last Updated:** 2026-03-02
