# Migration Status - What Remains

**Date:** 2026-02-04
**After Session:** 3 modules migrated today

## Overall Statistics

| Category | Count | Lines |
|----------|-------|-------|
| **Total Rust modules** | 538 | 187,317 |
| **Migrated** | 43 (8.0%) | 19,274 (10.3%) |
| **Not migrated** | 495 (92.0%) | 168,043 (89.7%) |

## Today's Progress

✅ **3 modules migrated:**
1. `monomorphize/note_sdn` - 494 → 303 lines
2. `semantics/truthiness` - 196 → 126 lines
3. `semantics/type_coercion` - 209 → 168 lines

**Total:** 899 Rust lines migrated

## Unmigrated by Subsystem (Top 15)

| Subsystem | Modules | Lines | Notes |
|-----------|---------|-------|-------|
| codegen | 103 | 38,344 | Many are library bindings (LLVM, Cranelift) |
| hir | 67 | 18,404 | Lowering logic |
| interpreter_extern | 51 | 15,901 | FFI wrappers |
| mir | 37 | 15,749 | MIR lowering + analysis |
| blocks | 31 | 8,319 | Math blocks, shell blocks |
| interpreter | 17 | 6,474 | Expression evaluation |
| linker | 17 | 5,910 | SMF file format |
| interpreter_call | 15 | 5,768 | BDD, block execution |
| interpreter_method | 10 | 4,327 | Method dispatch |
| lint | 6 | 4,057 | Linting rules |
| mock_helper | 14 | 4,052 | Test mocking |
| monomorphize | 11 | 3,614 | Generic instantiation |
| pipeline | 8 | 3,012 | Compilation pipeline |
| macro | 7 | 2,025 | Macro expansion |
| concurrent_providers | 4 | 2,005 | Concurrency abstraction |

## Top 20 Unmigrated Modules (Logic Only, Excluding Tests/Libraries)

| Priority | Module | Lines | Complexity |
|----------|--------|-------|-----------|
| P1 | lint/checker | 1,982 | High - Complex linting rules |
| P1 | error | 1,789 | Medium - Error handling |
| P1 | interpreter_call/bdd | 1,421 | Medium - BDD framework |
| P1 | interpreter/node_exec | 1,283 | High - AST execution |
| P1 | hir/lower/stmt_lowering | 1,231 | High - Statement lowering |
| P1 | interpreter_eval | 1,156 | High - Expression evaluation |
| P1 | lint/mod | 1,089 | Medium - Lint orchestration |
| P1 | interpreter_call/block_execution | 1,079 | Medium - Block execution |
| P1 | codegen/mir_interpreter | 1,058 | High - MIR interpretation |
| P2 | interpreter_method/collections | 1,051 | Medium - Collection methods |
| P2 | hir/lower/expr/control | 1,035 | High - Control flow lowering |
| P2 | pretty_printer | 1,028 | Low - Pretty printing |
| P2 | interpreter/expr/ops | 976 | Medium - Operator evaluation |
| P2 | blocks/math/backend/torch_eval | 929 | Medium - Torch integration |
| P2 | pipeline/module_loader | 838 | Medium - Module loading |
| P2 | monomorphize/cache | 805 | Low - Caching logic |
| P2 | compilability | 791 | Low - Compilability checks |
| P2 | semantic_diff | 770 | Medium - Semantic diffing |
| P2 | web_compiler | 768 | Medium - Web target |
| P2 | value_bridge | 750 | Medium - Value conversion |

## Good Next Targets (200-400 lines, Self-Contained)

### Semantics Module (Complete the module)

| Module | Lines | Status |
|--------|-------|--------|
| binary_ops | 375 | ❌ Not migrated |
| cast_rules | 264 | ❌ Not migrated |
| truthiness | 196 | ✅ Migrated |
| type_coercion | 209 | ✅ Migrated |
| mod | 28 | ❌ Not migrated |

**Recommendation:** Complete the semantics module (375 + 264 + 28 = 667 lines remaining)

### Other Self-Contained Modules (200-400 lines)

| Module | Lines | Type |
|--------|-------|------|
| type_check/mod | 208 | Type checking utilities |
| weaving/types | 231 | AOP types |
| build_mode | 232 | ✅ Already migrated |
| mir/async_sm | 233 | Async state machine |
| mir/ghost_erasure | 234 | Ghost type erasure |
| method_registry/registry | 239 | Method registry |
| text_diff | 241 | ✅ Already migrated |
| smf_builder | 250 | SMF file builder |
| spec_coverage | 251 | Coverage tracking |
| type_inference_config | 261 | Type inference config |
| interpreter_extern/sdn | 222 | SDN FFI wrappers |
| src/i18n/registry | 226 | i18n registry |

## Migration Strategy Recommendations

### Phase 1: Complete Semantics Module (Next Step)
Migrate remaining 3 files (667 lines):
1. `binary_ops.rs` (375 lines) - Binary operator semantics
2. `cast_rules.rs` (264 lines) - Type casting rules
3. `mod.rs` (28 lines) - Module exports

This completes a full subsystem (semantics).

### Phase 2: Small Utility Modules (200-300 lines)
- `type_check/mod` (208 lines)
- `src/i18n/registry` (226 lines)
- `weaving/types` (231 lines)
- `mir/async_sm` (233 lines)
- `smf_builder` (250 lines)

### Phase 3: Medium Modules (300-500 lines)
- `binary_ops` (375 lines)
- `symbol_analyzer` (374 lines)
- `smf_writer` (397 lines)
- `value_async` (419 lines)
- `trait_coherence` (451 lines)

### Phase 4: Large Subsystems (>500 lines)
Requires more planning, tackle after momentum is established.

## Excluded from Migration (Library Bindings)

These should stay in Rust as they wrap external libraries:
- **Cranelift:** `codegen/cranelift_*` (4 modules, ~3,000 lines)
- **LLVM:** `codegen/llvm/*` (35 modules, ~12,000 lines)
- **GPU/CUDA:** `codegen/gpu/*`, `blocks/cuda/*`
- **Native implementations:** `concurrent_providers/native_impl`

## Summary

**Immediate Next Steps:**
1. ✅ Complete semantics module (667 lines remaining)
2. Migrate 5-10 small utility modules (200-300 lines each)
3. Build momentum with self-contained modules
4. Tackle larger subsystems once patterns are established

**Current Progress:** 10.3% of code migrated (19,274 / 187,317 lines)
**Estimated Remaining:** ~150,000 lines of pure logic to migrate (excluding library bindings and tests)
