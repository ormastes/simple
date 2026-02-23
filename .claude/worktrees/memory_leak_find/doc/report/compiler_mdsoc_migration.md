# Compiler MDSoC Migration Status

**Last Updated:** 2026-02-17
**Overall Status:** Phases 0-7 + 3f + Feature Ports + Span Entity + Remaining Transforms COMPLETE ✅

## Summary

| Phase | Status | Files Changed | Tests |
|-------|--------|---------------|-------|
| Phase 0: Initial implementations | ✅ DONE | +30 files | 2815/2815 |
| Phase 1a: token entity | ✅ DONE | +3 files | 2815/2815 |
| Phase 1b: ast entity | ✅ DONE | +4 files | 2815/2815 |
| Phase 1c: hir entity | ✅ DONE | +3 files | 2815/2815 |
| Phase 1d: mir entity | ✅ DONE | +4 files | 2815/2815 |
| Phase 1e: types entity | ✅ DONE | +3 files | 2815/2815 |
| Phase 2a: lexing stage | ✅ DONE | +2 files | 239/239 |
| Phase 2b: parsing stage | ✅ DONE | +2 files | 239/239 |
| Phase 2c: desugar stage | ✅ DONE | +2 files | 239/239 |
| Phase 2d: typecheck stage | ✅ DONE | +2 files | 239/239 |
| Phase 2e: hir_lowering stage | ✅ DONE | +2 files | 239/239 |
| Phase 2f: mir_lowering stage | ✅ DONE | +2 files | 239/239 |
| Phase 2g: codegen stage | ✅ DONE | +2 files | 239/239 |
| Phase 2h: monomorphization stage | ✅ DONE | +2 files | 242/242 |
| Phase 2i: optimization stage | ✅ DONE | +2 files | 242/242 |
| Phase 2j: linking stage | ✅ DONE | +2 files | 242/242 |
| Phase 3a: typing→hir | ✅ DONE | +3 files | 239/239 |
| Phase 3b: hir→mir | ✅ DONE | +3 files | 239/239 |
| Phase 3c: mir→backend | ✅ DONE | +3 files | 239/239 |
| Phase 3d: parse→desugar | ✅ DONE | +3 files | 239/239 |
| Phase 3e: desugar→type | ✅ DONE | +3 files | 239/239 |
| Phase 3f: lexing→parsing | ✅ DONE | +3 files | 242/242 |
| Phase 4: arch enforcement | ✅ DONE | +2 files | 239/239 |
| Phase 5: module loader | ✅ DONE | +5 files | 239/239 |
| Phase 6: interp backend | ✅ DONE | +3 files | 239/239 |
| Phase 7: event bus | ✅ DONE | +4 files | 239/239 |
| doc_validation_spec fixes | ✅ DONE | 1 file | 242/242 |

## Phase Details

### Phase 0: Initial Implementations (Pre-Migration)
**New files (key):**
- `src/app/desugar/forwarding.spl` — alias forwarding desugar pass
- `src/app/desugar/trait_desugar.spl` — trait → struct desugaring
- `src/app/desugar/trait_scanner.spl` — text-level trait scanner
- `src/app/desugar/context_params.spl` — context parameter desugaring
- `src/app/cli/arch_check.spl` — architecture validation CLI
- `src/compiler/backend_port.spl` — BackendPort typed contract
- `src/compiler/compiler_services.spl` — CompilerServices port container
- `src/lib/error_suggest.spl` — error suggestion system
- `src/compiler_shared/` — 28 shared compiler files extracted

### Phase 1: Entity Dimension
**New directory:** `src/compiler_core/entity/`
- `token/kinds.spl` — all TOK_* constants + helpers
- `token/stream.spl` — CoreLexer struct
- `ast/nodes.spl` — CoreExpr/CoreStmt/CoreDecl structs
- `ast/tags.spl` — EXPR_*/STMT_*/DECL_* constants
- `ast/arena.spl` — parallel-array arenas + alloc fns
- `hir/types.spl` — CoreHirType + HIR_TYPE_* constants
- `hir/symbol_table.spl` — CoreSymbolTable/CoreSymbolEntry
- `mir/inst.spl` — CoreMirInst + MIR_* opcodes
- `mir/block.spl` — CoreBasicBlock
- `mir/func.spl` — CoreMirFunction
- `types/core_types.spl` — TYPE_* constants
- `types/generic.spl` — GenericParam/GenericInst
- Tests: `test/unit/compiler_core/entity/entity_structure_spec.spl`

### Phase 2: Feature Dimension
**New directory:** `src/compiler/feature/`

All 12 pipeline stages now have ports (7 original + 3 new + event bus + module loading):
- `lexing/app/ports.spl` — LexerInputPort, LexerOutputPort
- `parsing/app/ports.spl` — ParseError, ParserInputPort, ParserOutputPort
- `desugaring/app/ports.spl` — DesugarInputPort, DesugarOutputPort
- `type_checking/app/ports.spl` — Diagnostic, TypeCheckInputPort, TypeCheckOutputPort
- `hir_lowering/app/ports.spl` — HirLowerInputPort, HirFunction, HirLowerOutputPort
- `mir_lowering/app/ports.spl` — MirLowerInputPort, MirLowerOutputPort
- `codegen/app/ports.spl` — CodegenInputPort, CodegenOutputPort
- `monomorphization/app/ports.spl` — MonomorphizeInputPort, MonomorphizeOutputPort (added 2026-02-17)
- `optimization/app/ports.spl` — OptimizeInputPort, OptimizeOutputPort (added 2026-02-17)
- `linking/app/ports.spl` — LinkerInputPort, LinkerOutputPort (added 2026-02-17)
- `events/ports.spl` — CompilationEventPort, create_noop_event_port
- Each with `__init__.spl` arch config

### Phase 3: Transform Dimension
**New directory:** `src/compiler/transform/feature/`

All 9 D_transform stage boundaries now implemented (5 original + 4 added 2026-02-17):
- `typing_to_hir/entity_view/TypedAstView.spl` — TypedAstContext
- `hir_to_mir/entity_view/HirView.spl` — CfgContext
- `mir_to_backend/entity_view/MirView.spl` — MirProgram, MirDebugInfo
- `parsing_to_desugaring/entity_view/AstView.spl` — AstDesugarView
- `desugaring_to_typing/entity_view/DesugarView.spl` — DesugarTypingView
- `lexing_to_parsing/entity_view/TokenStreamView.spl` — TokenStreamView (Phase 3f)
- `mir_to_optimizer/entity_view/MirOptView.spl` — MirOptView (added 2026-02-17)
- `backend_to_linker/entity_view/ObjectFileView.spl` — ObjectFileView (added 2026-02-17)
- `loading_to_parsing/entity_view/LoadedModuleView.spl` — LoadedModuleView (added 2026-02-17)
- Each with `__init__.spl` arch config

### Phase 4: Architecture Enforcement
- `src/app/cli/arch_check.spl` — run_arch_check() CLI command
- `src/app/cli/main.spl` — `check-arch` command registered

### Phase 5: Module Loader as Adapter
- `src/compiler/feature/module_loading/app/ports.spl` — ModuleResolverPort, ModuleStoragePort, ModuleRegistryPort
- `src/compiler/adapters/out/file_module_storage.spl` — production disk adapter
- `src/compiler/adapters/out/memory_module_storage.spl` — test in-memory adapter

### Phase 6: Interpreter as Backend
- `src/compiler/feature/codegen/backends/interpreter/backend.spl` — create_interpreter_backend()
- Tests: `test/unit/compiler/interpreter_backend_spec.spl`

### Phase 7: Event Bus
- `src/compiler/feature/events/ports.spl` — CompilationEventPort, create_noop_event_port
- `src/compiler/adapters/in/language_server_adapter.spl` — IDE integration adapter
- `src/compiler/adapters/in/profiler_adapter.spl` — performance profiling adapter

## Architecture Map

```
src/
  core/
    entity/          ← D_entity: stable IR types (Phase 1)
      token/
      ast/
      hir/
      mir/
      types/
      span/          ← source location span (added 2026-02-17)
  compiler/
    feature/         ← D_feature: pipeline stages (Phase 2)
      lexing/
      parsing/
      desugaring/
      type_checking/
      hir_lowering/
      mir_lowering/
      codegen/
        backends/
          interpreter/  ← interpreter as backend (Phase 6)
      monomorphization/ ← mono ports (added 2026-02-17)
      optimization/     ← opt ports (added 2026-02-17)
      linking/          ← linker ports (added 2026-02-17)
      events/           ← event bus (Phase 7)
      module_loading/   ← module loader ports (Phase 5)
    transform/       ← D_transform: stage boundaries (Phase 3)
      feature/
        typing_to_hir/
        hir_to_mir/
        mir_to_backend/
        parsing_to_desugaring/
        desugaring_to_typing/
        lexing_to_parsing/    ← Phase 3f (added 2026-02-17)
        mir_to_optimizer/     ← (added 2026-02-17)
        backend_to_linker/    ← (added 2026-02-17)
        loading_to_parsing/   ← (added 2026-02-17)
    adapters/        ← outbound/inbound adapters
      out/           ← file system, disk
      in/            ← language server, profiler
    mdsoc/           ← MDSOC enforcement engine (pre-existing)
```

## Dependency Rules (Enforced by check-arch)

```
compiler_core/entity/**          ← can only import compiler_core/entity/** or shared/**
compiler/feature/**     ← imports via transform/ or own entity types
compiler/transform/**   ← imports entity types only, no feature imports
compiler/adapters/**    ← implements feature ports, no cross-adapter imports
```

## Test Counts

| Milestone | Compiler Tests | Notes |
|-----------|---------------|-------|
| Phases 2–6 complete | 239/239 | baseline |
| Phase 7 event bus | 241/241 | +2 port struct tests |
| Phase 3f + feature ports + spec fixes | 242/242 | +9 transform tests, +18 feature port tests |
| Span entity + 3 transform boundaries | 243/243 | +16 span tests, +24 transform tests |

## Future Work

All originally planned items are now complete. The architecture is fully covered:

- **D_entity:** 13 entity files (`token/`, `ast/`, `hir/`, `mir/`, `types/`, `span/`)
- **D_feature:** 12 pipeline stage port files
- **D_transform:** 9 stage boundary view files
- **D_adapters:** inbound (language server, profiler) and outbound (file, memory)

## References

- Design: `doc/research/compiler_mdsoc_design.md`
- Plan: `doc/report/compiler_mdsoc_impl_plan.md`
- Standard Architecture: `doc/guide/standard_architecture.md`
- MDSOC Guide: `doc/guide/mdsoc_guide.md`
- Session report: `doc/report/mdsoc_phase3f_feature_ports_2026-02-17.md`
