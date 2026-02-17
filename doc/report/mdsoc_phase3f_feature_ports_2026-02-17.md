# MDSOC Phase 3f + Feature Ports - Implementation Report

**Date:** 2026-02-17
**Status:** Complete

## Summary

Three parallel work streams completed this session, bringing compiler MDSOC coverage to 242/242 tests passing:

1. **Phase 3f (lexing_to_parsing transform):** Added the missing D_transform boundary between the lexing and parsing pipeline stages.
2. **Feature stage ports (monomorphization, optimization, linking):** Added ports for 3 pipeline stages that lacked them, completing all 12 D_feature stages.
3. **doc_validation_spec fixes:** Corrected API mismatches in the MDSOC validation test file.

## Changes Made

### Phase 3f: lexing_to_parsing Transform

- `src/compiler/transform/feature/lexing_to_parsing/__init__.spl` — arch config for the lexing_to_parsing capsule
- `src/compiler/transform/feature/lexing_to_parsing/entity_view/TokenStreamView.spl` — `TokenStreamView` struct bridging `LexerOutputPort` to `ParserInputPort`; adds `source_text` field required for parser error messages

`TokenStreamView` is the entity view that carries the token stream across the D_transform boundary from lexing to parsing. It holds the `tokens` array (from `LexerOutputPort`) plus `source_text` (the original source, needed by the parser for error reporting).

### Feature Stage Ports

Three pipeline stages that had no D_feature ports:

- `src/compiler/feature/monomorphization/__init__.spl` — arch config
- `src/compiler/feature/monomorphization/app/ports.spl` — `MonomorphizeInputPort` (typed HIR), `MonomorphizeOutputPort` (monomorphized HIR)
- `src/compiler/feature/optimization/__init__.spl` — arch config
- `src/compiler/feature/optimization/app/ports.spl` — `OptimizeInputPort` (MIR), `OptimizeOutputPort` (optimized MIR + stats)
- `src/compiler/feature/linking/__init__.spl` — arch config
- `src/compiler/feature/linking/app/ports.spl` — `LinkerInputPort` (object files + entry point), `LinkerOutputPort` (linked binary path)

### doc_validation_spec Fixes

`test/unit/compiler/mdsoc/doc_validation_spec.spl` had API calls that no longer matched the current MDSOC structs. Fixed:

- `LayerDirection.TopDown` → `LayerDirection.UpperToLower`
- `LayerDef(name:..., layers:..., allowed_deps:...)` → `LayerDef.new([...], direction)`
- `SurfaceBinding(name:..., visibility:..., source_module:..., alias:...)` → `SurfaceBinding.new(caret, path, alias)`
- `VirtualCapsule(surface:..., path:..., internal_modules:..., rules:...)` → `VirtualCapsule.new(name, dimension, layer)`

### Tests Added

- `test/unit/compiler/transform_adapters_spec.spl` — +9 tests for `TokenStreamView` (Phase 3f)
- `test/unit/compiler/feature_ports_spec.spl` — +18 tests for monomorphization, optimization, and linking ports

## Results

| Metric | Before | After |
|--------|--------|-------|
| Compiler tests | 241/241 | 242/242 |
| D_transform boundaries | 5/6 | 6/6 |
| D_feature pipeline stages with ports | 9/12 | 12/12 |
| doc_validation_spec passing | no | yes |

## Architecture Completeness

All planned MDSOC dimensions are now fully populated:

- **D_entity:** 12 entity files in `src/core/entity/` (token, ast, hir, mir, types)
- **D_feature:** 12 pipeline stage port files in `src/compiler/feature/`
- **D_transform:** 6 stage boundary views in `src/compiler/transform/feature/`
- **D_adapters:** inbound (language server, profiler) and outbound (file, memory) adapters

## Follow-up (same session)

All 4 future-work items implemented:

1. `src/core/entity/span/Span.spl` — `SourceLocation` (line, col, to_text, at) + `Span` (start, end_loc, is_single_line, contains_line, line_count, single_line, empty)
2. `src/compiler/transform/feature/mir_to_optimizer/entity_view/MirOptView.spl` — bridges MIR lowering → optimizer; has_functions, is_optimized, average_insts_per_fn
3. `src/compiler/transform/feature/backend_to_linker/entity_view/ObjectFileView.spl` — bridges codegen output → linker; is_empty, has_symbols, from_codegen, failed
4. `src/compiler/transform/feature/loading_to_parsing/entity_view/LoadedModuleView.spl` — bridges module loader → parser; has_source, is_empty, from_source, empty

Tests added:
- `test/unit/core/entity/entity_span_spec.spl` — 16 tests for SourceLocation + Span
- `test/unit/compiler/transform_adapters_spec.spl` — +24 tests (8 each for MirOptView, ObjectFileView, LoadedModuleView)

All 9 D_transform boundaries now complete (was 6/9 after phase 3f, now 9/9).
