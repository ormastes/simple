# File Splitting Refactoring Plan

**Date:** 2025-12-15  
**Goal:** Split files over 1000 lines into smaller, focused modules  
**Found:** 9 files over 1000 lines (total: 11,198 lines)

---

## Overview

Large files make codebases harder to navigate, understand, and maintain. This plan splits 9 files (11,000+ lines) into 49 focused modules, improving maintainability and reducing cognitive load.

---

## Files to Split (Priority Order)

### Priority 1: Critical - Largest Files (Must Do First)

#### 1. monomorphize.rs (1798 lines) ⚠️ LARGEST
**Current:** All monomorphization logic in one massive file  
**Impact:** High complexity, hard to navigate

**Split into:**
```
src/compiler/src/monomorphize/
├── mod.rs              - Public API, Monomorphizer struct (~300 lines)
├── types.rs            - ConcreteType, PointerKind, SpecializationKey (~200 lines)
├── table.rs            - MonomorphizationTable (~300 lines)
├── analyzer.rs         - CallSiteAnalyzer (~200 lines)
├── specialization.rs   - Specialization logic (~400 lines)
└── instantiate.rs      - Type instantiation (~400 lines)
```

**Estimated savings:** 100-150 lines (reduced duplication)

---

#### 2. pipeline.rs (1489 lines)
**Current:** Entire compilation pipeline in one file  
**Impact:** High complexity, multiple responsibilities

**Split into:**
```
src/compiler/src/pipeline/
├── mod.rs              - CompilerPipeline struct, public API (~300 lines)
├── module_loader.rs    - Module loading and imports (~400 lines)
├── smf_generation.rs   - SMF generation functions (~300 lines)
├── elf_utils.rs        - ELF extraction and relocation (~300 lines)
└── script_detection.rs - Script vs module detection (~100 lines)
```

**Estimated savings:** 100-120 lines

---

#### 3. lexer.rs (1343 lines)
**Current:** All lexer logic in one file  
**Impact:** Multiple concerns mixed

**Split into:**
```
src/parser/src/lexer/
├── mod.rs          - Lexer struct, public API (~200 lines)
├── scanner.rs      - Character scanning and peeking (~200 lines)
├── tokens.rs       - Token generation (numbers, strings, identifiers) (~400 lines)
├── indentation.rs  - Indentation tracking (INDENT/DEDENT) (~200 lines)
├── comments.rs     - Comment and docstring handling (~200 lines)
└── escape.rs       - String escape sequences (~150 lines)
```

**Estimated savings:** 100-130 lines

---

### Priority 2: Test Files (Easy Wins)

#### 4. llvm_tests.rs (1119 lines)
**Current:** All LLVM backend tests in one file  
**Impact:** Hard to find specific tests

**Split into:**
```
src/compiler/src/codegen/llvm_tests/
├── mod.rs              - Test helpers, common setup (~100 lines)
├── function_tests.rs   - Function compilation tests (~300 lines)
├── binop_tests.rs      - Binary operation tests (~250 lines)
├── control_flow_tests.rs - Control flow tests (~250 lines)
└── memory_tests.rs     - Memory operation tests (~200 lines)
```

**Estimated savings:** 80-100 lines

---

### Priority 3: Instruction Compiler

#### 5. instr.rs (1305 lines)
**Current:** All MIR instruction compilation in one file  
**Impact:** High complexity, many instruction types

**Split into:**
```
src/compiler/src/codegen/instr/
├── mod.rs          - InstrContext, compile_instruction dispatcher (~200 lines)
├── arithmetic.rs   - Binary/unary operations (~200 lines)
├── memory.rs       - Load/store/allocation (~200 lines)
├── control_flow.rs - Calls, jumps, branches (~200 lines)
├── objects.rs      - Structs, closures, methods (~300 lines)
└── builtin.rs      - Builtin calls (I/O, etc.) (~200 lines)
```

**Estimated savings:** 100-120 lines

---

### Priority 4: Type System

#### 6. ast.rs (1045 lines)
**Current:** All AST node definitions  
**Impact:** Hard to find specific node types  
**Note:** Mostly enum definitions - harder to split, but improves organization

**Split into:**
```
src/parser/src/ast/
├── mod.rs   - Re-exports (~50 lines)
├── types.rs - Type-related enums (Visibility, Mutability, etc.) (~200 lines)
├── expr.rs  - Expression nodes (~300 lines)
├── stmt.rs  - Statement nodes (~300 lines)
└── decl.rs  - Declaration nodes (~200 lines)
```

**Estimated savings:** 50-80 lines (mainly organization)

---

### Priority 5: HIR Lowering

#### 7. hir/lower.rs (1023 lines)
**Current:** All AST→HIR lowering in one file  
**Impact:** Complex transformations, hard to test individual parts

**Split into:**
```
src/compiler/src/hir/lower/
├── mod.rs      - Lowerer struct, public API (~150 lines)
├── expr.rs     - Expression lowering (~300 lines)
├── stmt.rs     - Statement lowering (~250 lines)
├── types.rs    - Type lowering (~200 lines)
└── context.rs  - FunctionContext and helpers (~150 lines)
```

**Estimated savings:** 80-100 lines

---

### Priority 6: LLVM Backend

#### 8. llvm.rs (1071 lines)
**Current:** All LLVM backend implementation  
**Impact:** Multiple responsibilities

**Split into:**
```
src/compiler/src/codegen/llvm/
├── mod.rs          - LlvmBackend struct (~150 lines)
├── types.rs        - Type definitions and conversions (~200 lines)
├── function.rs     - Function compilation (~300 lines)
├── instructions.rs - Instruction generation (~300 lines)
└── native.rs       - NativeBackend trait impl (~150 lines)
```

**Estimated savings:** 80-100 lines

---

### Priority 7: Settlement Container

#### 9. settlement/container.rs (1005 lines)
**Current:** All settlement logic in one file  
**Impact:** Multiple responsibilities, hard to test

**Split into:**
```
src/loader/src/settlement/container/
├── mod.rs        - Settlement struct (~200 lines)
├── module.rs     - SettlementModule (~200 lines)
├── config.rs     - SettlementConfig (~150 lines)
├── error.rs      - SettlementError (~100 lines)
├── loading.rs    - Module loading logic (~200 lines)
└── resolution.rs - Symbol resolution (~200 lines)
```

**Estimated savings:** 80-100 lines

---

## Summary Table

| File | Lines | Priority | New Modules | Est. Saved |
|------|-------|----------|-------------|------------|
| monomorphize.rs | 1798 | P1 ⚠️ | 6 | 100-150 |
| pipeline.rs | 1489 | P1 ⚠️ | 5 | 100-120 |
| lexer.rs | 1343 | P1 ⚠️ | 6 | 100-130 |
| instr.rs | 1305 | P3 | 6 | 100-120 |
| llvm_tests.rs | 1119 | P2 ✅ | 5 | 80-100 |
| llvm.rs | 1071 | P6 | 5 | 80-100 |
| ast.rs | 1045 | P4 | 5 | 50-80 |
| hir/lower.rs | 1023 | P5 | 5 | 80-100 |
| container.rs | 1005 | P7 | 6 | 80-100 |
| **TOTAL** | **11,198** | - | **49** | **770-1000** |

---

## Expected Benefits

### Code Quality
1. ✅ **Improved Maintainability** - Smaller, focused modules
2. ✅ **Better Navigation** - Clear module boundaries
3. ✅ **Reduced Cognitive Load** - Each file has single responsibility
4. ✅ **Easier Testing** - Can test modules independently
5. ✅ **Parallel Development** - Multiple developers can work on different modules
6. ✅ **Reduced Duplication** - Clearer boundaries reveal common patterns

### Metrics
- **Lines per file:** Average 250-300 (down from 1000+)
- **Modules created:** 49 new focused modules
- **Duplication reduction:** 770-1000 lines
- **Cognitive load:** ~70% reduction (1000+ → 250-300 lines per file)

---

## Implementation Strategy

### Recommended Order

1. **Phase 1: Largest Files (P1)**
   - monomorphize.rs (1798 lines) → 6 modules
   - pipeline.rs (1489 lines) → 5 modules
   - lexer.rs (1343 lines) → 6 modules
   - **Impact:** ~40% of total lines, biggest wins

2. **Phase 2: Easy Wins (P2)**
   - llvm_tests.rs (1119 lines) → 5 modules
   - **Impact:** Quick win, just tests, low risk

3. **Phase 3: Medium Complexity (P3-P5)**
   - instr.rs (1305 lines) → 6 modules
   - ast.rs (1045 lines) → 5 modules
   - hir/lower.rs (1023 lines) → 5 modules
   - **Impact:** Core functionality, need careful testing

4. **Phase 4: Backend & Infrastructure (P6-P7)**
   - llvm.rs (1071 lines) → 5 modules
   - container.rs (1005 lines) → 6 modules
   - **Impact:** Infrastructure, need comprehensive testing

### Refactoring Process (Per File)

1. **Analyze** - Identify natural module boundaries
2. **Create** - Create module directory structure
3. **Move** - Move code to appropriate modules
4. **Test** - Ensure all tests still pass
5. **Cleanup** - Remove duplication revealed by split
6. **Document** - Update module documentation

### Testing Strategy

- Run full test suite after each file split
- Check compilation with `cargo build --workspace`
- Verify no performance regression
- Update documentation as needed

---

## Risk Mitigation

### Low Risk
- ✅ Test files (llvm_tests.rs) - Easy to split, low coupling
- ✅ Type definitions (ast.rs) - Mostly enums, clear boundaries

### Medium Risk
- ⚠️ Lexer, Pipeline - Complex but well-structured
- ⚠️ HIR lowering - Clear phases (expr, stmt, types)

### High Risk
- 🔴 Monomorphize - Complex interdependencies, need careful planning
- 🔴 Instruction compiler - Many cross-references

**Mitigation:**
- Start with low-risk files to build confidence
- Comprehensive testing after each split
- Keep git commits atomic (one file split per commit)
- Can revert easily if issues arise

---

## Next Steps

1. **Review this plan** with team
2. **Start with P1 files** (monomorphize, pipeline, lexer)
3. **Track progress** in TODO_IMPLEMENTATION.md
4. **Measure impact** on duplication and maintainability

---

**Status:** PLANNED  
**Estimated Effort:** 2-3 weeks (one file per day)  
**Expected Outcome:** 11,000 lines → 49 focused modules, ~800 lines saved
