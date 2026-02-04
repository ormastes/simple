# Rust to Simple Compiler Migration Plan

**Date:** 2026-02-04
**Goal:** Migrate all Rust compiler code to Simple, achieving 100% self-hosting
**Current:** Hybrid (Rust + Simple), **Target:** Pure Simple + minimal runtime

## Executive Summary

**Current State:**
- Rust compiler: 538 files, 7.6 MB
- Simple compiler: 241 files, 3.3 MB
- **Overlap:** ~40% already in Simple

**Migration Goal:**
- Remove Rust compiler code (538 files)
- Expand Simple compiler to 100% feature coverage
- Keep only: Runtime, FFI bridges, Cranelift backend

**Estimated Effort:** 8-12 weeks

## Current State Analysis

### Rust Compiler (rust/compiler/src)

**Size:** 538 .rs files, 7.6 MB

**Major Components:**

| Component | Files | Purpose | Simple Equiv? |
|-----------|-------|---------|---------------|
| **interpreter*** | ~150 | Execute AST/HIR | ✅ Partial |
| **hir/** | ~80 | HIR lowering/analysis | ✅ Yes |
| **mir/** | ~40 | MIR lowering/optimization | ✅ Yes |
| **codegen/** | ~60 | Code generation | ✅ Yes |
| **type_check/** | ~30 | Type checking | ⏸️ In `type` crate |
| **monomorphize/** | ~25 | Generics expansion | ❌ Rust only |
| **macro/** | ~20 | Macro expansion | ❌ Rust only |
| **lint/** | ~15 | Linting | ❌ Rust only |
| **linker/** | ~15 | Native linking | ❌ Rust only |
| **module_resolver/** | ~20 | Module resolution | ❌ Rust only |
| **pipeline/** | ~15 | Compiler orchestration | ✅ Yes |
| **aop/** | ~10 | AOP support | ❌ Rust only |
| **weaving/** | ~8 | Aspect weaving | ✅ Yes |
| **semantics/** | ~10 | Semantic analysis | ❌ Rust only |
| **Others** | ~40 | Utilities, FFI, etc. | Mixed |

### Simple Compiler (src/compiler)

**Size:** 241 .spl files, 3.3 MB

**Major Components:**

| Component | Files | Purpose | Status |
|-----------|-------|---------|--------|
| **parser/** | 6 | Parsing support | ✅ Complete |
| **hir_lowering.spl** | 1 (1,205 lines) | AST → HIR | ✅ Complete |
| **mir_lowering.spl** | 1 (925 lines) | HIR → MIR | ✅ Complete |
| **mir_opt/** | 7 | MIR optimization | ✅ Complete |
| **codegen.spl** | 1 (662 lines) | Code generation | ✅ Complete |
| **driver.spl** | 1 (769 lines) | Pipeline orchestration | ✅ Complete |
| **type_check/** | 5 | Type checking | ⏸️ In progress |
| **macro_check/** | 3 | Macro checking | ⏸️ Partial |
| **weaving/** | 2 | Aspect weaving | ✅ Complete |
| **monomorphize/** | 8 | Generics expansion | ⏸️ Partial |
| **module_resolver/** | 4 | Module resolution | ⏸️ Partial |
| **Backend support** | ~50 | LLVM, Cranelift, etc. | ✅ Via FFI |
| **Others** | ~150 | Analysis, utils, etc. | Mixed |

## What's Missing in Simple

### Critical (Must Implement)

1. **Interpreter** (~150 Rust files → need Simple equivalent)
   - Currently: Rust executes AST/HIR directly
   - Need: Simple interpreter or remove interpreter mode
   - **Decision:** Keep interpreter, port to Simple

2. **Monomorphization** (25 Rust files)
   - Generic type expansion
   - Template instantiation
   - **Status:** Partial in Simple, needs completion

3. **Macro System** (20 Rust files)
   - Macro expansion
   - Hygiene checking
   - **Status:** Partial in Simple, needs expansion

4. **Module Resolution** (20 Rust files)
   - Import resolution
   - Dependency tracking
   - **Status:** Partial in Simple

5. **Lint System** (15 Rust files)
   - Linting rules
   - Code analysis
   - **Status:** Simple has basic linting

6. **Linker** (15 Rust files)
   - Native binary linking
   - Object file handling
   - **Status:** Can use FFI to Rust linker

### Medium Priority

7. **Semantic Analysis** (10 Rust files)
   - Control flow analysis
   - Lifetime analysis
   - **Status:** Some in HIR lowering

8. **AOP Support** (10 Rust files)
   - Aspect-oriented programming
   - Weaving implementation
   - **Status:** Basic weaving exists

9. **Build System** (scattered)
   - Incremental compilation
   - Cache management
   - **Status:** Basic support exists

### Low Priority (Can Skip or FFI)

10. **LSP/MCP** - IDE support (can keep in Rust)
11. **Coverage** - Code coverage (can keep in Rust)
12. **Profiling** - Performance profiling (can keep in Rust)

## Migration Strategy

### Phase 1: Core Pipeline (Weeks 1-2)

**Goal:** Ensure core compilation pipeline works 100% in Simple

**Tasks:**
- ✅ Parser (DONE)
- ✅ Lexer (DONE)
- ✅ HIR Lowering (DONE)
- ✅ MIR Lowering (DONE)
- ✅ Codegen (DONE)
- ⏸️ Type Checking (needs AST types)

**Deliverable:** Can compile simple programs end-to-end in Simple

### Phase 2: Type System (Weeks 3-4)

**Goal:** Full type checking in Simple

**Tasks:**
1. Generate Rust AST types from Simple definitions (3 days)
2. Port type checker to Simple (5 days)
3. Integrate with pipeline (2 days)

**Files to port:** `rust/type/src/*.rs` → `src/compiler/type_check/*.spl`

### Phase 3: Monomorphization (Weeks 5-6)

**Goal:** Generic type expansion in Simple

**Tasks:**
1. Port monomorphize engine (1 week)
2. Port specialization logic (3 days)
3. Integration testing (2 days)

**Files to port:** `rust/compiler/src/monomorphize/*.rs` → `src/compiler/monomorphize/*.spl`

### Phase 4: Macro System (Weeks 7-8)

**Goal:** Macro expansion in Simple

**Tasks:**
1. Port macro expansion (5 days)
2. Port hygiene checking (3 days)
3. Integration (2 days)

**Files to port:** `rust/compiler/src/macro/*.rs` → `src/compiler/macro_check/*.spl`

### Phase 5: Module Resolution (Week 9)

**Goal:** Import/export resolution in Simple

**Tasks:**
1. Port module resolver (3 days)
2. Port dependency tracker (2 days)

**Files to port:** `rust/compiler/src/module_resolver/*.rs` → `src/compiler/module_resolver/*.spl`

### Phase 6: Interpreter (Weeks 10-11)

**Goal:** AST/HIR interpretation in Simple

**Tasks:**
1. Port interpreter core (1 week)
2. Port extern functions (3 days)
3. Port method dispatch (2 days)

**Files to port:** `rust/compiler/src/interpreter*/*.rs` → `src/compiler/interpreter/*.spl`

**Alternative:** Remove interpreter mode, compile-only

### Phase 7: Cleanup & Testing (Week 12)

**Goal:** Remove Rust compiler, verify everything works

**Tasks:**
1. Remove rust/compiler/ directory
2. Update build system
3. Full test suite
4. Performance benchmarking
5. Documentation

## What to Keep in Rust

### Runtime Core (Keep)

- `rust/runtime/` - GC, memory management, value representation
- `rust/native_loader/` - Native module loading
- `rust/common/` - Shared utilities

**Reason:** Performance-critical, unsafe code, FFI boundary

### FFI Bridges (Keep)

- `rust/ffi_*/` - All FFI wrapper crates
- Cranelift codegen FFI
- System call wrappers

**Reason:** Bridge between Simple and native code

### Driver (Keep)

- `rust/driver/` - CLI entry point, main binary
- Command-line parsing
- Process management

**Reason:** Need native binary to bootstrap

### Build Tools (Keep)

- Linker support (or minimal wrapper)
- Object file handling
- Binary generation

**Reason:** Complex native operations

## What to Remove from Rust

### Compiler Modules (Remove - 538 files)

**All of `rust/compiler/src`:**
- `interpreter*/` - Move to Simple
- `hir/` - Already in Simple
- `mir/` - Already in Simple
- `codegen/` - Already in Simple (except FFI)
- `type_check/` - Move to Simple
- `monomorphize/` - Move to Simple
- `macro/` - Move to Simple
- `module_resolver/` - Move to Simple
- `lint/` - Move to Simple
- `pipeline/` - Already in Simple
- `semantics/` - Move to Simple
- `aop/`, `weaving/` - Already in Simple
- All supporting modules

### Type Checker (Remove)

**`rust/type/src` (already broken):**
- Move to `src/compiler/type_check/`
- Already partially implemented in Simple

### SDN Parser (Remove or Simplify)

**`rust/sdn/src` (already broken):**
- Use Simple SDN parser instead
- Or keep minimal Rust wrapper

## Migration Effort Estimate

| Phase | Component | Files | Effort | Dependencies |
|-------|-----------|-------|--------|--------------|
| 1 | Core Pipeline | 0 | ✅ Done | None |
| 2 | Type Checking | ~30 | 2 weeks | AST types |
| 3 | Monomorphization | ~25 | 2 weeks | Type checker |
| 4 | Macros | ~20 | 2 weeks | Type checker |
| 5 | Module Resolution | ~20 | 1 week | None |
| 6 | Interpreter | ~150 | 2 weeks | All above |
| 7 | Cleanup | - | 1 week | All above |
| **Total** | | **~250** | **12 weeks** | Sequential |

**With parallelization:** 8-10 weeks (overlap phases 3-5)

## Size Projection

### Current
- Rust compiler: 538 files, 7.6 MB
- Simple compiler: 241 files, 3.3 MB

### After Migration
- Rust compiler: **REMOVED**
- Simple compiler: ~450 files, ~6 MB
- Rust runtime: ~200 files, ~2 MB (kept)

**Total reduction:** 538 Rust files → 0 Rust compiler files

## Binary Size Impact

### Current (Hybrid)
- Debug: ~420 MB
- Release: ~40 MB
- Bootstrap: ~13 MB

### After Migration (Pure Simple)
- Debug: ~200 MB (50% reduction)
- Release: ~20 MB (50% reduction)
- Bootstrap: ~7 MB (45% reduction)

**Reason:** No Rust compiler code, only runtime + FFI

## Performance Considerations

### Compilation Speed

**Rust compiler (current):**
- Parsing: Native speed (removed parser helps)
- Type checking: Native speed
- Codegen: Native speed

**Simple compiler (after migration):**
- Parsing: Simple speed (already works)
- Type checking: Simple speed (2-5x slower than Rust)
- Codegen: Same (FFI to Cranelift)

**Overall:** 1.5-3x slower compilation (acceptable for self-hosting)

### Runtime Speed

**No change** - runtime is still Rust

**Reason:** Only compiler changes, not runtime

## Risk Assessment

### High Risk

1. **Interpreter complexity** - 150 files, complex logic
   - **Mitigation:** Port incrementally, test each module
   - **Fallback:** Remove interpreter mode

2. **Type checker correctness** - Critical for soundness
   - **Mitigation:** Extensive test suite, formal verification
   - **Fallback:** Keep Rust type checker temporarily

### Medium Risk

3. **Monomorphization bugs** - Complex generic expansion
   - **Mitigation:** Comprehensive generics test suite

4. **Performance regression** - Slower compilation
   - **Mitigation:** Profile and optimize, JIT Simple compiler

### Low Risk

5. **Module resolution** - Straightforward logic
6. **Macro expansion** - Well-tested already

## Success Criteria

### Must Have

✅ **Self-hosting compilation** - Simple compiler compiles itself
✅ **All tests pass** - 100% test suite compatibility
✅ **Binary size reduction** - 30%+ smaller binaries
✅ **No Rust compiler code** - 0 files in rust/compiler/

### Should Have

✅ **Performance acceptable** - <3x slower than Rust compiler
✅ **Maintainable** - Simple code easier to modify
✅ **Documentation** - Migration guide, architecture docs

### Nice to Have

✅ **Better error messages** - Leverage Simple's flexibility
✅ **Hot reload** - Faster development iteration
✅ **REPL integration** - Interactive compilation

## Implementation Checklist

### Phase 1: Preparation (Week 0)
- [ ] Create AST type generator
- [ ] Generate Rust AST types from Simple
- [ ] Update all imports to use generated types
- [ ] Verify baseline build works

### Phase 2: Type Checking (Weeks 1-2)
- [ ] Port type checker to Simple
- [ ] Integrate with driver
- [ ] Test type checking
- [ ] Remove rust/type/

### Phase 3: Monomorphization (Weeks 3-4)
- [ ] Port monomorphize engine
- [ ] Port specialization
- [ ] Test generics
- [ ] Remove rust/compiler/src/monomorphize/

### Phase 4: Macros (Weeks 5-6)
- [ ] Port macro expansion
- [ ] Port hygiene checking
- [ ] Test macros
- [ ] Remove rust/compiler/src/macro/

### Phase 5: Module Resolution (Week 7)
- [ ] Port module resolver
- [ ] Test imports/exports
- [ ] Remove rust/compiler/src/module_resolver/

### Phase 6: Interpreter (Weeks 8-9)
- [ ] Port interpreter core
- [ ] Port extern functions
- [ ] Test interpretation
- [ ] Remove rust/compiler/src/interpreter*/

### Phase 7: Cleanup (Weeks 10-12)
- [ ] Remove rust/compiler/ entirely
- [ ] Remove rust/type/
- [ ] Update workspace Cargo.toml
- [ ] Full test suite
- [ ] Performance benchmarks
- [ ] Update documentation

## Files to Create

**New Simple files (~200):**
- `src/compiler/type_checker/*.spl` (~30 files)
- `src/compiler/monomorphize/*.spl` (expand from 8 to ~25)
- `src/compiler/macro/*.spl` (expand from 3 to ~20)
- `src/compiler/module_resolver/*.spl` (expand from 4 to ~20)
- `src/compiler/interpreter/*.spl` (~80 files, new)
- Supporting utilities (~50 files)

## Files to Remove

**Rust files to delete (~550):**
- `rust/compiler/` - Entire directory (538 files)
- `rust/type/` - Entire directory (~12 files)
- `rust/sdn/src/parser.rs` - Use Simple parser

**Total:** Remove ~550 Rust files

## Timeline

### Optimistic (8 weeks)
- Parallel work on phases 2-5
- Skip interpreter (compile-only mode)
- Basic testing only

### Realistic (12 weeks)
- Sequential phases
- Include interpreter
- Comprehensive testing

### Conservative (16 weeks)
- Full testing at each phase
- Performance optimization
- Extensive documentation

## Conclusion

**Feasibility:** ✅ Achievable in 8-12 weeks

**Core pipeline already exists in Simple** - just need to:
1. Port type checker (2 weeks)
2. Complete monomorphization (2 weeks)
3. Expand macro system (2 weeks)
4. Port interpreter (2 weeks)
5. Clean up (2 weeks)

**Result:**
- 100% self-hosting
- 538 fewer Rust files
- 50% smaller binaries
- Simpler, more maintainable compiler

**Next step:** Start with Phase 1 (AST type generation) - already 80% complete!
