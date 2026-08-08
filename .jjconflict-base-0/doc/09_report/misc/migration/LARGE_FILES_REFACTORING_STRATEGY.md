# Large Files Refactoring Strategy

**Date:** 2025-12-24
**Purpose:** Document refactoring strategies for remaining large files
**Target:** Files > 1000 lines that need splitting

## Overview

This document outlines refactoring strategies for 6 remaining large files in the codebase. The goal is to split each file into logical, maintainable modules of < 700 lines while preserving functionality and test coverage.

## Files to Refactor

| File | Lines | Type | Priority |
|------|-------|------|----------|
| src/parser/src/parser_tests.rs | 1255 | Test | High |
| src/compiler/src/hir/lower/lower_tests.rs | 1520 | Test | High |
| src/driver/tests/interpreter_types.rs | 1213 | Test | High |
| src/util/simple_mock_helper/src/coverage_extended.rs | 1036 | Source | Medium |
| src/ui/src/parser/mod.rs | 1026 | Source | Medium |
| src/compiler/src/codegen/llvm/functions.rs | 1007 | Source | Low |

---

## 1. parser_tests.rs (1255 lines)

### Current Structure Analysis

**Test Categories (by line ranges):**
- Expression Tests (13-90): 7 tests - literals, binary ops, precedence, calls, arrays
- Statement Tests (94-116): 2 tests - let, let mut
- Function Tests (119-142): 2 tests - function definitions
- Struct Tests (146-156): 1 test - struct definition
- Enum Tests (160-170): 1 test - enum definition
- Control Flow Tests (174-204): 3 tests - if, for, while
- Pattern Tests (208-219): 1 test - tuple patterns
- Module System Tests (223-340): 8 tests - use, mod, common use, export, auto import
- SIMD Type Tests (344-428): 4 tests - vec types
- Multi-Base Unit Tests (432-478): 3 tests - unit definitions
- String Unit Suffix Tests (481-528): 3 tests - typed strings
- Doc Comment Tests (532-590): 4 tests - doc comments
- Strict Mode Tests (593-722): 10 tests - parser mode validation
- Infix Keyword Tests (725-813): 5 tests - to/not_to keywords
- SIMD Bounds Block Tests (816-1040): 11 tests - bounds patterns
- GPU Tests (1043-1130): 3 tests - shared let, dynamic arrays
- Provenance Tracking Tests (1133-1255): 6 tests - @generated_by decorator

### Split Strategy

**Target:** 5 files, ~250 lines each

#### File 1: `parser_tests_expressions.rs` (~250 lines)
- Expression Tests (13-90)
- Binary operations, precedence
- Function/method calls
- Array/tuple literals

#### File 2: `parser_tests_statements.rs` (~250 lines)
- Statement Tests (94-116)
- Function Tests (119-142)
- Struct Tests (146-156)
- Enum Tests (160-170)
- Control Flow Tests (174-204)
- Pattern Tests (208-219)

#### File 3: `parser_tests_modules.rs` (~250 lines)
- Module System Tests (223-340)
- Doc Comment Tests (532-590)
- Provenance Tracking Tests (1133-1255)

#### File 4: `parser_tests_types.rs` (~250 lines)
- SIMD Type Tests (344-428)
- Multi-Base Unit Tests (432-478)
- String Unit Suffix Tests (481-528)

#### File 5: `parser_tests_modes.rs` (~250 lines)
- Strict Mode Tests (593-722)
- Infix Keyword Tests (725-813)
- SIMD Bounds Block Tests (816-1040)
- GPU Tests (1043-1130)

### Implementation Plan

1. Create new test files in `src/parser/src/tests/`
2. Move test groups with helper functions
3. Update `mod.rs` to include new modules
4. Run tests to verify no regressions
5. Delete original `parser_tests.rs`

---

## 2. hir/lower/lower_tests.rs (1520 lines)

### Current Structure Analysis

**Test Categories (by line ranges):**
- Basic Lowering Tests (12-308): 25 tests - types, functions, literals, control flow
- SIMD Intrinsics Tests (326-502): 11 tests - this.index(), thread_group, barriers
- SIMD Vec Tests (504-606): 8 tests - vec types, literals, operations
- SIMD Reduction Tests (608-656): 3 tests - sum, min/max, all/any
- GPU Intrinsics Tests (658-752): 6 tests - gpu.global_id(), barrier, local_size
- SIMD Decorator Tests (755-793): 1 test - decorator parsing
- SIMD Operations Tests (795-862): 5 tests - extract, with, sqrt, abs
- SIMD Math Tests (863-929): 3 tests - floor/ceil/round
- SIMD Advanced Tests (931-1089): 9 tests - shuffle, blend, select
- GPU Atomic Tests (991-1115): 7 tests - atomic operations
- SIMD Load/Store Tests (1120-1206): 4 tests - load, gather, store, scatter
- SIMD Math2 Tests (1208-1274): 3 tests - fma, recip
- SIMD Swizzle Tests (1254-1408): 7 tests - xyzw, rgba, partial swizzles
- SIMD Masked Tests (1410-1454): 2 tests - masked load/store
- SIMD MinMax Tests (1456-1520): 3 tests - min, max, clamp

### Split Strategy

**Target:** 3 files, ~500 lines each

#### File 1: `lower_tests_basic.rs` (~500 lines)
- Basic Lowering Tests (12-308)
- Test helper functions
- Type checking, control flow, expressions

#### File 2: `lower_tests_simd.rs` (~500 lines)
- SIMD Intrinsics Tests (326-502)
- SIMD Vec Tests (504-606)
- SIMD Reduction Tests (608-656)
- SIMD Operations Tests (795-862)
- SIMD Math Tests (863-929)
- SIMD Load/Store Tests (1120-1206)
- SIMD Math2 Tests (1208-1274)

#### File 3: `lower_tests_gpu.rs` (~520 lines)
- GPU Intrinsics Tests (658-752)
- SIMD Decorator Tests (755-793)
- SIMD Advanced Tests (931-1089)
- GPU Atomic Tests (991-1115)
- SIMD Swizzle Tests (1254-1408)
- SIMD Masked Tests (1410-1454)
- SIMD MinMax Tests (1456-1520)

### Implementation Plan

1. Create `tests/` submodule in `src/compiler/src/hir/lower/`
2. Move test groups preserving helper functions
3. Update `mod.rs` to include test modules
4. Verify all tests pass
5. Remove original file

---

## 3. interpreter_types.rs (1213 lines)

### Current Structure Analysis

**Test Categories (by line ranges):**
- Helper Functions (7-40): Error handling helpers
- Basic Type Tests (42-115): 4 tests - enum comparison, union types, type alias
- Union Type Tests (117-150): 2 tests - pattern matching
- Optional & Generic Tests (152-219): 4 tests - optional, generic functions/structs/enums
- Option Methods Tests (222-270): 6 tests - Some/None, unwrap, map
- Strong Enum Tests (274-351): 4 tests - exhaustive matching, wildcard errors
- Type Suffix Tests (355-424): 9 tests - i32, i64, u32, unit suffixes
- Standalone Unit Tests (428-453): 2 tests - unit definitions
- String Methods Tests (456-457): Placeholder section
- Unit Family Tests (461-590): 10 tests - unit families, conversions
- Unit Method Tests (592-623): 3 tests - value(), suffix(), to_string()
- Primitive API Tests (625-622): 2 tests - warnings, semantic types
- Unit Arithmetic Tests (627-745): 9 tests - type-safe arithmetic
- Compound Unit Tests (748-843): 6 tests - compound units, cancellation
- SI Prefix Tests (849-983): 11 tests - kilo, mega, giga, milli, nano, tera
- Unit Inference Tests (987-1098): 7 tests - parameter/return type checking
- Unit Assertion Tests (1101-1213): 7 tests - assert_unit! macro

### Split Strategy

**Target:** 3 files, ~400 lines each

#### File 1: `interpreter_types_basic.rs` (~400 lines)
- Helper Functions (7-40)
- Basic Type Tests (42-115)
- Union Type Tests (117-150)
- Optional & Generic Tests (152-219)
- Option Methods Tests (222-270)
- Strong Enum Tests (274-351)
- Type Suffix Tests (355-424)

#### File 2: `interpreter_types_units.rs` (~400 lines)
- Standalone Unit Tests (428-453)
- Unit Family Tests (461-590)
- Unit Method Tests (592-623)
- Primitive API Tests (625-622)
- Unit Arithmetic Tests (627-745)
- Compound Unit Tests (748-843)

#### File 3: `interpreter_types_advanced.rs` (~413 lines)
- SI Prefix Tests (849-983)
- Unit Inference Tests (987-1098)
- Unit Assertion Tests (1101-1213)

### Implementation Plan

1. Create test submodules in `src/driver/tests/interpreter_types/`
2. Move helper functions to shared module
3. Split tests by category
4. Update parent `mod.rs`
5. Verify all tests pass

---

## 4. coverage_extended.rs (1036 lines)

### Current Structure Analysis

**Sections:**
- Imports & Types (1-63): Demangle utilities
- Coverage Types & Structs (86-406): Data models (20 structs/enums)
- CoverageAnalyzer Core (408-446): Initialization
- Analysis Methods (448-804): 4 large methods (100-200 lines each)
- Utility Functions (806-924): Print summary
- Tests (926-1036): 10 unit tests

### Split Strategy

**Target:** 3 files, ~350 lines each

#### File 1: `coverage_types.rs` (~200 lines)
- All type definitions (CoverageType, Metrics, Summaries, etc.)
- Basic impl blocks
- Serde derives

#### File 2: `coverage_analyzer.rs` (~450 lines)
- CoverageAnalyzer struct
- Core analysis methods:
  - build_function_counts
  - generate_system_report
  - generate_integration_report
  - generate_service_report
  - generate_merged_report

#### File 3: `coverage_utils.rs` (~200 lines)
- Demangle utilities
- matches_type_method helper
- print_coverage_summary
- Helper functions

#### File 4: `coverage_tests.rs` (~186 lines)
- All unit tests
- Test fixtures
- Assertions

### Implementation Plan

1. Create `coverage/` submodule
2. Extract types to separate file
3. Move analyzer logic
4. Move utilities
5. Move tests
6. Update imports in `lib.rs`

---

## 5. ui/src/parser/mod.rs (1026 lines)

### Current Structure Analysis

**Sections:**
- Module declarations & imports (1-12)
- ParseError enum (14-37)
- SuiParser struct (40-56)
- Main parse method (58-92)
- Directive parsing (95-156)
- Declaration parsing (159-188)
- Server/Client blocks (190-226)
- Template node parsing (229-268)
- Element parsing (271-333)
- Attribute parsing (336-404)
- Output/Control parsing (424-632)
- Control flow parsing (454-632)
- Directive node parsing (635-733)
- Statement parsing (738-821)
- Type parsing (824-843)
- Helper methods (846-899)
- Tests (902-1026)

### Split Strategy

**Target:** 4 files, ~250 lines each

#### File 1: `parser_core.rs` (~250 lines)
- SuiParser struct & initialization
- Main parse method
- Helper methods (peek, advance, expect, etc.)
- ParseError enum

#### File 2: `parser_blocks.rs` (~250 lines)
- Directive parsing
- Declaration parsing
- Server/Client blocks
- Template node parsing

#### File 3: `parser_elements.rs` (~270 lines)
- Element parsing
- Attribute parsing
- Output/Control parsing
- Control flow parsing (if/for/let)

#### File 4: `parser_directives.rs` (~130 lines)
- Directive node parsing (embed, slot, fill)
- Statement parsing
- Type parsing

#### File 5: `parser_tests.rs` (~120 lines)
- All unit tests
- Test fixtures

### Implementation Plan

1. Create `parser/` submodule structure
2. Extract parser components maintaining pub visibility
3. Keep `mod.rs` as re-export hub
4. Move tests to separate file
5. Verify parsing works correctly

---

## 6. codegen/llvm/functions.rs (1007 lines)

### Current Structure Analysis

**Sections:**
- Imports & setup (1-13)
- compile_function method (15-999)
  - Function setup (17-79): Type mapping, function creation
  - Block & vreg setup (61-85): Basic block creation, parameter mapping
  - Instruction compilation (86-992): Massive match statement
    - Basic instructions (94-135): ConstInt, ConstBool, Copy, BinOp
    - Memory instructions (136-178): Load, Store, GcAlloc
    - String/Symbol (179-186): ConstString
    - Function calls (187-227): Call, argument handling
    - Collections (228-291): ArrayLit, TupleLit
    - Indexing (292-370): IndexGet, IndexSet
    - Interpreter bridge (372-421): InterpCall
    - Dictionary (422-479): DictLit
    - Struct operations (480-631): StructInit, FieldGet, FieldSet
    - Closures (632-706): ClosureCreate
    - Indirect calls (707-818): IndirectCall
    - Symbols & slicing (819-907): ConstSymbol, SliceOp
    - Interpreter eval (908-929): InterpEval
    - GPU instructions (931-987): GpuGlobalId, barriers, atomics
- Non-LLVM stub (1001-1006)

### Split Strategy

**Target:** 4 files, ~250 lines each

#### File 1: `function_core.rs` (~200 lines)
- Function setup logic
- Block creation
- Parameter mapping
- Helper methods for function compilation

#### File 2: `instruction_basic.rs` (~250 lines)
- Basic instructions (ConstInt, ConstBool, Copy, BinOp, UnaryOp)
- Memory instructions (Load, Store, GcAlloc)
- String/Symbol instructions
- Function calls

#### File 3: `instruction_collections.rs` (~280 lines)
- Collections (ArrayLit, TupleLit, DictLit)
- Indexing operations (IndexGet, IndexSet)
- Struct operations (StructInit, FieldGet, FieldSet)
- Slicing operations

#### File 4: `instruction_advanced.rs` (~280 lines)
- Closures (ClosureCreate, IndirectCall)
- Interpreter bridge (InterpCall, InterpEval)
- GPU instructions (all GPU/atomic operations)

### Implementation Plan

1. Create `llvm/function_compile/` submodule
2. Extract instruction handlers to separate files
3. Keep main compile_function as orchestrator
4. Use trait or impl blocks to organize
5. Verify LLVM feature flag works

---

## General Refactoring Guidelines

### For Test Files
1. **Preserve test isolation** - Each test should remain independent
2. **Share helpers wisely** - Put common helpers in `common.rs` or `helpers.rs`
3. **Maintain test names** - Don't rename tests to avoid breaking CI
4. **Group by feature** - Split by language feature or test category
5. **Keep fixtures together** - Test data should be near the tests that use it

### For Source Files
1. **Maintain public API** - Use re-exports to keep interface stable
2. **Preserve feature flags** - Keep #[cfg(feature)] attributes intact
3. **Share types carefully** - Common types go in dedicated module
4. **Document splits** - Add module docs explaining organization
5. **Test after split** - Run full test suite to verify

### Module Organization Pattern

For large refactorings, use this structure:

```
original_file/
├── mod.rs           # Re-exports, orchestration
├── types.rs         # Type definitions
├── core.rs          # Core functionality
├── helpers.rs       # Utility functions
├── feature_a.rs     # Feature implementation
├── feature_b.rs     # Feature implementation
└── tests.rs         # Unit tests (if applicable)
```

### Verification Checklist

After each file split:
- [ ] All tests pass (`cargo test`)
- [ ] No new clippy warnings (`cargo clippy`)
- [ ] Code coverage maintained
- [ ] Documentation builds (`cargo doc`)
- [ ] Feature flags work correctly
- [ ] File sizes are < 700 lines
- [ ] No duplicate code introduced

---

## Implementation Priority

### Phase 1 (High Priority - Test Files)
1. **parser_tests.rs** - Split into 5 test modules
2. **lower_tests.rs** - Split into 3 test modules
3. **interpreter_types.rs** - Split into 3 test modules

**Rationale:** Test files are easiest to split and provide immediate value in code organization. No API changes needed.

### Phase 2 (Medium Priority - Utility Files)
4. **coverage_extended.rs** - Split into 4 modules
5. **ui/parser/mod.rs** - Split into 5 modules

**Rationale:** These files have clear boundaries and limited external dependencies.

### Phase 3 (Low Priority - Complex Files)
6. **llvm/functions.rs** - Split into 4 modules

**Rationale:** This file requires careful handling of feature flags and complex type dependencies. Should be done last when patterns from other refactorings are established.

---

## Success Metrics

- **Line count:** All files < 700 lines
- **Test coverage:** No decrease in coverage percentage
- **Build time:** No significant increase
- **Maintainability:** Easier to locate and modify specific functionality
- **Documentation:** Clear module structure with appropriate docs

---

## References

- [RUST_LONG_FILES.md](./RUST_LONG_FILES.md) - Original analysis
- [FILE_SPLITTING_SUMMARY.md](./FILE_SPLITTING_SUMMARY.md) - Previous splitting work
- Rust module system: https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html
