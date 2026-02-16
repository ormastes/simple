# LLVM Backend Unification Plan

**Date**: 2026-02-13
**Goal**: Unified LLVM backend shared by Core Simple and Full Simple compilers

---

## Executive Summary

Create a shared LLVM backend infrastructure that eliminates ~50% code duplication between `compiler/` (Full Simple) and `compiler_core/` (Core Simple), while maintaining compatibility with both feature-rich Full Simple and desugared Core Simple.

**Key Metrics:**
- **Current duplication**: ~1,300 lines duplicated LLVM code
- **Files affected**: 10 LLVM-related files (5 in compiler, 5 in compiler_core)
- **Estimated reduction**: 40-50% fewer lines via shared library
- **Complexity**: Medium (requires abstraction over generics/no-generics)

---

## Current State Analysis

### File Inventory

| Component | Location | Lines | Features |
|-----------|----------|-------|----------|
| **Full Simple LLVM** ||||
| llvm_backend.spl | compiler/backend/ | 503 | Option types, full features |
| llvm_ir_builder.spl | compiler/backend/ | 1,122 | Complex optimizations |
| llvm_target.spl | compiler/backend/ | 363 | All architectures |
| llvm_type_mapper.spl | compiler/backend/ | 304 | Generic types |
| llvm_tools.spl | compiler/backend/ | 85 | Shared utilities |
| **Core Simple LLVM** ||||
| llvm_backend.spl | compiler_core/backend/ | 289 | Desugared (no Option) |
| llvm_ir_builder.spl | compiler_core/backend/ | 386 | Basic optimizations |
| llvm_target.spl | compiler_core/backend/ | 230 | Limited architectures |
| llvm_type_mapper.spl | compiler_core/backend/ | 108 | No generics |
| llvm_tools.spl | compiler_core/backend/ | 85 | **Identical to Full** |
| **App-level Integration** ||||
| llvm_direct.spl | app/compile/ | ~200 | Hybrid C→LLVM path |
| compile_to_llvm.spl | app/build/ | ~150 | Build integration |
| **TOTAL** | | **~3,475 lines** | |

### Duplication Analysis

**High duplication (>70% similar):**
- `llvm_tools.spl`: **100% identical** (85 lines duplicated)
- `llvm_target.spl`: ~80% similar (target triples, CPU configs)
- `llvm_backend.spl`: ~60% similar (compilation pipeline structure)

**Medium duplication (30-60% similar):**
- `llvm_ir_builder.spl`: ~40% similar (basic IR building logic shared)
- `llvm_type_mapper.spl`: ~30% similar (primitive type mapping shared)

**Key Differences:**
1. **Full Simple** uses Option types (`text?`), generics (`Vec<T>`)
2. **Core Simple** uses nil-safe patterns, no generics
3. **Full Simple** has richer optimization passes (120+ lines vs 40 lines)
4. **Core Simple** is bootstrap-compatible (seed_cpp can compile it)

### Architecture Patterns

**Current approach** (per-compiler):
```
compiler/backend/llvm_backend.spl
  ├─ Use compiler.mir_data.*
  ├─ Use compiler.backend.llvm_target
  ├─ Use compiler.backend.llvm_ir_builder
  └─ Class LlvmBackend (Full Simple features)

compiler_core/backend/llvm_backend.spl
  ├─ Use compiler.mir_data.*
  ├─ Use compiler.backend.llvm_target  (DUPLICATE)
  ├─ Use compiler.backend.llvm_ir_builder  (DUPLICATE)
  └─ Class LlvmBackend (Desugared, bootstrap-safe)
```

**Problem**: Two independent LLVM implementations sharing 40-70% of logic.

---

## Design Principles

### 1. **Shared Core, Divergent Wrappers**

Create `src/llvm_core/` (or `src/std/llvm/`) with shared LLVM primitives:
- Target configuration (triples, CPUs, features)
- LLVM tool invocations (llc, opt, clang)
- Type mapping (Simple types → LLVM types)
- Optimization pass definitions

Compiler-specific wrappers handle:
- MIR → LLVM translation (uses compiler-specific MIR structures)
- Backend API implementation (uses compiler-specific interfaces)

### 2. **Bootstrap Compatibility**

All shared code must be **Core Simple compatible**:
- No generics (`Vec<T>` → `[T]` arrays)
- No Option types (`text?` → `text` with nil)
- No advanced pattern matching (only simple case statements)
- Compilable by seed_cpp

### 3. **Progressive Extraction**

Extract in phases to minimize risk:
1. **Phase 1**: Extract 100% identical code (llvm_tools.spl)
2. **Phase 2**: Extract target configuration (llvm_target.spl)
3. **Phase 3**: Extract type mapping primitives
4. **Phase 4**: Extract optimization pass definitions
5. **Phase 5**: Refactor backends to use shared library

---

## Proposed Architecture

### Directory Structure

```
src/
├── llvm_shared/              # NEW: Shared LLVM infrastructure
│   ├── mod.spl               # Public API
│   ├── target.spl            # Target triples, CPU configs
│   ├── tools.spl             # LLVM tool invocations (llc, opt, clang)
│   ├── types.spl             # Type mapping (i64, f64, bool, text → LLVM)
│   ├── passes.spl            # Optimization pass definitions
│   └── ir_primitives.spl     # Basic IR building blocks
│
├── compiler/backend/
│   ├── llvm_backend.spl      # REFACTORED: Uses llvm_shared.*
│   ├── llvm_ir_builder.spl   # REFACTORED: Compiler-specific MIR→LLVM
│   └── llvm_type_mapper.spl  # REFACTORED: Compiler-specific type mapping
│
├── compiler_core/backend/
│   ├── llvm_backend.spl      # REFACTORED: Uses llvm_shared.* (desugared wrapper)
│   ├── llvm_ir_builder.spl   # REFACTORED: Core-specific MIR→LLVM
│   └── llvm_type_mapper.spl  # REFACTORED: Core-specific type mapping
│
└── app/compile/
    └── llvm_direct.spl       # REFACTORED: Uses llvm_shared.tools
```

### Shared Module API

**src/llvm_shared/mod.spl**:
```simple
# Shared LLVM infrastructure for Core and Full Simple compilers.
# Bootstrap-compatible: No generics, no Option types, seed_cpp compilable.

# Re-exports
export llvm_shared.target.*
export llvm_shared.tools.*
export llvm_shared.types.*
export llvm_shared.passes.*
```

**src/llvm_shared/target.spl** (extracted from compiler/backend/llvm_target.spl):
```simple
# Target triple and CPU configuration (shared by Core and Full)

struct LlvmTargetTriple:
    arch: text       # x86_64, aarch64, riscv64, armv7, i686, riscv32
    vendor: text     # unknown, pc, apple, none (baremetal)
    os: text         # linux, darwin, windows, none (baremetal)
    env: text        # gnu, musl, msvc, eabi, ""

fn llvm_triple_for_target(target: CodegenTarget, baremetal: bool) -> LlvmTargetTriple
fn llvm_triple_to_string(triple: LlvmTargetTriple) -> text
fn llvm_cpu_for_target(target: CodegenTarget, compat_mode: bool) -> text
fn llvm_features_for_target(target: CodegenTarget) -> text
```

**src/llvm_shared/tools.spl** (extracted from compiler/backend/llvm_tools.spl):
```simple
# LLVM tool invocations (shared by Core and Full)
# This file is 100% identical in compiler and compiler_core

fn find_llvm_tool(tool: text) -> text
fn invoke_llc(input_ll: text, output_o: text, triple: text, cpu: text, features: text, opt_level: text) -> i64
fn invoke_opt(input_ll: text, output_ll: text, passes: [text]) -> i64
fn invoke_clang(input_files: [text], output: text, triple: text, opt_level: text) -> i64
```

**src/llvm_shared/types.spl** (extracted common parts):
```simple
# LLVM type mapping (primitive types only - shared)

fn llvm_type_i64() -> text: "i64"
fn llvm_type_i32() -> text: "i32"
fn llvm_type_f64() -> text: "double"
fn llvm_type_bool() -> text: "i1"
fn llvm_type_ptr() -> text: "ptr"  # LLVM 15+ opaque pointers
fn llvm_type_void() -> text: "void"

# Compiler-specific type mapping stays in compiler/compiler_core
# (handles structs, enums, generic types)
```

**src/llvm_shared/passes.spl** (extracted pass definitions):
```simple
# LLVM optimization pass definitions

enum LlvmPass:
    MemToReg
    SCCP
    LICM
    GVN
    DeadCodeElim
    InlineFunctions
    TailCallElim
    # ... (all pass names)

fn pass_to_flag(pass: LlvmPass) -> text
fn passes_for_opt_level(level: i64) -> [LlvmPass]
```

### Backend Refactoring

**compiler/backend/llvm_backend.spl** (after refactoring):
```simple
# Full Simple LLVM Backend
# Uses shared llvm_shared.* infrastructure

use llvm_shared.target.{llvm_triple_for_target, llvm_cpu_for_target}
use llvm_shared.tools.{invoke_llc, invoke_opt, invoke_clang}
use llvm_shared.passes.{passes_for_opt_level}
use compiler.backend.llvm_ir_builder.{MirToLlvmFull}  # Compiler-specific
use compiler.backend.llvm_type_mapper.{FullTypeMapper}  # Compiler-specific

class LlvmBackend:
    target: CodegenTarget
    opt_level: OptimizationLevel
    # ... Full Simple-specific features (Option types, etc.)

    fn compile_module(module: MirModule) -> CompiledModule:
        # 1. Get target config from shared library
        val triple = llvm_triple_for_target(self.target, self.bare_metal)
        val cpu = llvm_cpu_for_target(self.target, self.compat_mode)

        # 2. Translate MIR→LLVM using compiler-specific translator
        val ir_builder = MirToLlvmFull.create(triple, cpu)
        val llvm_ir = ir_builder.translate(module)

        # 3. Optimize using shared passes
        val passes = passes_for_opt_level(self.opt_level)
        invoke_opt(llvm_ir, output_ir, passes)

        # 4. Compile to object code using shared tools
        invoke_llc(output_ir, output_o, triple, cpu, features, opt_level)
```

**compiler_core/backend/llvm_backend.spl** (after refactoring):
```simple
# Core Simple LLVM Backend (desugared, bootstrap-safe)
# Uses shared llvm_shared.* infrastructure

use llvm_shared.target.{llvm_triple_for_target, llvm_cpu_for_target}
use llvm_shared.tools.{invoke_llc, invoke_opt, invoke_clang}
use llvm_shared.passes.{passes_for_opt_level}
use compiler_core.backend.llvm_ir_builder.{MirToLlvmCore}  # Core-specific
use compiler_core.backend.llvm_type_mapper.{CoreTypeMapper}  # Core-specific

class LlvmBackend:
    target: CodegenTarget
    opt_level: OptimizationLevel
    cpu_override: text  # NOTE: NOT text? (desugared)
    # ... Core Simple-specific patterns (no Option, no generics)

    static fn create(target: CodegenTarget, opt_level: OptimizationLevel) -> LlvmBackend:
        # Desugared constructor (no Option type)
        LlvmBackend(
            target: target,
            opt_level: opt_level,
            cpu_override: ""  # "" instead of nil (desugared pattern)
        )

    fn compile_module(module: MirModule) -> CompiledModule:
        # SAME logic as Full, but using Core-specific translators
        val triple = llvm_triple_for_target(self.target, self.bare_metal)
        val cpu = if self.cpu_override == "":
            llvm_cpu_for_target(self.target, false)
        else:
            self.cpu_override

        # Core-specific MIR translator
        val ir_builder = MirToLlvmCore.create(triple, cpu)
        # ... rest is identical to Full
```

---

## Implementation Plan

### Phase 1: Extract Identical Code (Low Risk)

**Goal**: Extract 100% identical llvm_tools.spl

**Steps**:
1. Create `src/llvm_shared/` directory
2. Move `compiler/backend/llvm_tools.spl` → `src/llvm_shared/tools.spl`
3. Update imports in:
   - `compiler/backend/llvm_backend.spl`
   - `compiler_core/backend/llvm_backend.spl`
4. Delete `compiler_core/backend/llvm_tools.spl`
5. Run tests: `bin/simple test test/feature/llvm_backend*`

**Files changed**: 4 files (1 created, 1 deleted, 2 imports updated)
**Risk**: LOW (code is 100% identical)
**Estimated time**: 30 minutes

### Phase 2: Extract Target Configuration (Medium Risk)

**Goal**: Extract target triple and CPU configuration logic

**Steps**:
1. Create `src/llvm_shared/target.spl`
2. Extract shared functions from `llvm_target.spl`:
   - `llvm_triple_for_target()`
   - `llvm_cpu_for_target()`
   - `llvm_features_for_target()`
   - Target triple struct and helpers
3. Update `compiler/backend/llvm_target.spl`:
   - Keep Full Simple-specific target configs
   - Import and delegate to shared functions
4. Update `compiler_core/backend/llvm_target.spl`:
   - Keep Core Simple-specific target configs
   - Import and delegate to shared functions
5. Run tests

**Files changed**: 5 files (1 created, 4 updated)
**Risk**: MEDIUM (target configuration is platform-critical)
**Estimated time**: 2 hours

### Phase 3: Extract Type Mapping Primitives (Medium Risk)

**Goal**: Extract primitive type mappings (i64, f64, bool, ptr, void)

**Steps**:
1. Create `src/llvm_shared/types.spl`
2. Extract primitive type functions from `llvm_type_mapper.spl`:
   - `llvm_type_i64()`, `llvm_type_i32()`, etc.
   - Array type construction
   - Pointer type construction
3. Keep compiler-specific logic in respective `llvm_type_mapper.spl`:
   - Full: struct/enum/generic type mapping
   - Core: desugared struct/enum mapping
4. Run tests

**Files changed**: 5 files (1 created, 4 updated)
**Risk**: MEDIUM (type mapping is core to codegen)
**Estimated time**: 2 hours

### Phase 4: Extract Optimization Passes (Low Risk)

**Goal**: Extract optimization pass definitions and configurations

**Steps**:
1. Create `src/llvm_shared/passes.spl`
2. Extract from `llvm_ir_builder.spl`:
   - `LlvmPass` enum (pass names)
   - `passes_for_opt_level()` (pass selection)
   - `pass_to_flag()` (pass → LLVM flag)
3. Update both `llvm_ir_builder.spl` files to import passes
4. Run tests

**Files changed**: 5 files (1 created, 4 updated)
**Risk**: LOW (pass definitions are data, not logic)
**Estimated time**: 1 hour

### Phase 5: Refactor Backends (High Risk)

**Goal**: Refactor both backends to use shared infrastructure

**Steps**:
1. Refactor `compiler/backend/llvm_backend.spl`:
   - Replace direct LLVM tool calls with `llvm_shared.tools.*`
   - Replace target config with `llvm_shared.target.*`
   - Replace pass selection with `llvm_shared.passes.*`
2. Refactor `compiler_core/backend/llvm_backend.spl`:
   - Same refactoring as Full
   - Ensure desugared patterns preserved
3. Update IR builders to use shared primitives
4. Run full test suite:
   - Unit tests: `test/unit/compiler/backend/llvm_*`
   - Feature tests: `test/feature/llvm_backend_*`
   - Integration tests: `test/integration/llvm_backend_e2e_spec.spl`
5. Test bootstrap compilation:
   - Core → Core2 (using Core LLVM backend)
   - Full → Full2 (using Full LLVM backend)

**Files changed**: 10+ files (major refactoring)
**Risk**: HIGH (affects both compiler pipelines)
**Estimated time**: 1 day
**Verification**: Full bootstrap test required

---

## Verification Strategy

### Per-Phase Testing

**After each phase**:
```bash
# 1. Unit tests for LLVM components
bin/simple test test/unit/compiler/backend/llvm_*

# 2. Feature tests for all architectures
bin/simple test test/feature/llvm_backend_*

# 3. Integration test
bin/simple test test/integration/llvm_backend_e2e_spec.spl

# 4. Verify both backends work
bin/simple build --backend=llvm              # Full Simple backend
bin/simple build --backend=llvm-core         # Core Simple backend (if exposed)
```

### Final Verification (After Phase 5)

**Bootstrap compilation test**:
```bash
# 1. Core Simple bootstrap
scripts/bootstrap-from-scratch.sh

# 2. Full Simple self-compilation
bin/simple build --backend=llvm src/compiler/*.spl

# 3. Verify reproducibility
bin/simple build --backend=llvm src/compiler/*.spl --output=compiler_v2
diff compiler_v1 compiler_v2  # Should be identical
```

### Regression Tests

Create new tests:
1. **test/system/llvm_shared_backend_spec.spl**
   - Verify shared library functions work correctly
   - Test target triple generation for all platforms
   - Test CPU selection logic
   - Test optimization pass selection

2. **test/system/backend_parity_spec.spl**
   - Verify Core and Full backends produce equivalent output
   - Compile same Simple code with both backends
   - Compare generated LLVM IR (should be structurally similar)

---

## Estimated Impact

### Code Reduction

**Current**:
- compiler/backend/llvm_*.spl: ~2,377 lines
- compiler_core/backend/llvm_*.spl: ~1,098 lines
- **Total**: ~3,475 lines

**After refactoring**:
- src/llvm_shared/*.spl: ~800 lines (shared)
- compiler/backend/llvm_*.spl: ~1,200 lines (Full-specific)
- compiler_core/backend/llvm_*.spl: ~500 lines (Core-specific)
- **Total**: ~2,500 lines

**Reduction**: ~975 lines eliminated (~28% reduction)

### Maintenance Benefits

**Before**:
- Bug fix requires updating 2 places (compiler + compiler_core)
- New architecture support requires 2 implementations
- Target triple updates need 2 changes
- Optimization pass changes need 2 updates

**After**:
- Bug fix in shared code: 1 change affects both
- New architecture: 1 shared implementation
- Target triple: 1 update
- Optimization passes: 1 definition

### Performance Impact

**Expected**: ZERO performance change
- Shared library is compile-time abstraction only
- Generated LLVM IR should be identical
- No runtime overhead (all static functions)

---

## Risk Assessment

### High Risk Areas

1. **Bootstrap Compatibility**
   - **Risk**: Shared library uses features seed_cpp can't compile
   - **Mitigation**: Enforce Core Simple subset (no generics, no Option)
   - **Verification**: Compile shared library with seed_cpp before integration

2. **Backend API Changes**
   - **Risk**: Refactoring breaks existing backend interface
   - **Mitigation**: Keep backend API unchanged, only internals change
   - **Verification**: Run full test suite after each phase

3. **Platform-Specific Code**
   - **Risk**: Target configuration differs subtly between platforms
   - **Mitigation**: Extensive testing on Linux, macOS, Windows, FreeBSD
   - **Verification**: Cross-compilation tests for all targets

### Medium Risk Areas

1. **Type Mapping**
   - **Risk**: Subtle differences in type representation
   - **Mitigation**: Extract only primitive types first
   - **Verification**: Compare generated IR before/after

2. **Optimization Passes**
   - **Risk**: Pass ordering affects correctness
   - **Mitigation**: Keep pass selection logic simple
   - **Verification**: Benchmark performance before/after

### Low Risk Areas

1. **Tool Invocations**
   - **Risk**: LLVM tool interfaces change
   - **Mitigation**: Already isolated in llvm_tools.spl
   - **Verification**: Tool version check in tests

2. **Documentation**
   - **Risk**: Docs become outdated
   - **Mitigation**: Update docs alongside code
   - **Verification**: Doc review as part of PR

---

## Dependencies

### External Dependencies

**LLVM toolchain** (already required):
- llc (LLVM static compiler)
- opt (LLVM optimizer)
- clang (C compiler with LLVM backend)

**Version requirements**:
- LLVM 15+ (opaque pointers)
- Clang 15+

### Internal Dependencies

**Must exist before refactoring**:
- ✅ MIR (Middle IR) representation in both compilers
- ✅ Backend API interface
- ✅ CodegenTarget enum
- ✅ OptimizationLevel enum

**Will create during refactoring**:
- src/llvm_shared/ module
- Shared LLVM infrastructure

---

## Alternative Approaches Considered

### Alternative 1: Merge compiler_core into compiler

**Pros**:
- Complete elimination of duplication
- Single codebase

**Cons**:
- Breaks bootstrap (compiler_core must be seed_cpp compatible)
- Full Simple uses features Core Simple can't have
- Would require reverting 6-phase core refactoring

**Decision**: REJECTED (breaks bootstrap compatibility)

### Alternative 2: Generate compiler_core from compiler

**Pros**:
- Single source of truth (compiler/)
- Automated desugaring

**Cons**:
- Complex code generation tool needed
- Hard to debug generated code
- Adds build-time dependency

**Decision**: REJECTED (too complex, fragile)

### Alternative 3: Keep duplication, improve documentation

**Pros**:
- No refactoring risk
- Clear separation

**Cons**:
- Maintenance burden (2x updates)
- Bug fixes need 2 changes
- Technical debt accumulates

**Decision**: REJECTED (maintenance cost too high)

### Alternative 4: Shared library with abstraction layer (CHOSEN)

**Pros**:
- Eliminates ~30% duplication
- Maintains bootstrap compatibility
- Clear separation of concerns
- Low-risk incremental approach

**Cons**:
- Some duplication remains (compiler-specific logic)
- Adds new module dependency

**Decision**: CHOSEN (best balance of benefits vs risk)

---

## Success Criteria

### Functional Requirements

1. ✅ Core Simple compiler uses shared LLVM backend
2. ✅ Full Simple compiler uses shared LLVM backend
3. ✅ Both compilers produce equivalent LLVM IR for same input
4. ✅ All existing tests pass
5. ✅ Bootstrap compilation works (seed_cpp → Core → Core2)
6. ✅ Self-compilation works (Full → Full2)

### Performance Requirements

1. ✅ Compilation time unchanged (±5%)
2. ✅ Generated code performance unchanged
3. ✅ Memory usage unchanged

### Code Quality Requirements

1. ✅ Shared code is Core Simple compatible (seed_cpp can compile)
2. ✅ No generics in shared library
3. ✅ No Option types in shared library
4. ✅ All shared code has unit tests
5. ✅ Documentation updated

### Maintenance Requirements

1. ✅ Bug fixes only need 1 change (not 2)
2. ✅ New architecture support: 1 shared implementation
3. ✅ Clear module boundaries documented
4. ✅ Migration guide for contributors

---

## Timeline

**Total estimated time**: 2-3 days

| Phase | Tasks | Time | Risk |
|-------|-------|------|------|
| **Phase 1** | Extract llvm_tools.spl | 30 min | LOW |
| **Phase 2** | Extract target config | 2 hours | MEDIUM |
| **Phase 3** | Extract type primitives | 2 hours | MEDIUM |
| **Phase 4** | Extract optimization passes | 1 hour | LOW |
| **Phase 5** | Refactor both backends | 1 day | HIGH |
| **Verification** | Full test suite + bootstrap | 4 hours | - |
| **Documentation** | Update docs, migration guide | 2 hours | - |

**Recommended schedule**:
- Day 1: Phases 1-4 (extract shared code)
- Day 2: Phase 5 (refactor backends)
- Day 3: Verification + documentation

---

## Next Steps

1. **Review this plan** with stakeholders
2. **Create tracking issue** for the refactoring
3. **Set up feature branch** for development
4. **Execute Phase 1** (extract llvm_tools.spl)
5. **Verify Phase 1** before proceeding

---

## Questions for Review

1. Should `llvm_shared/` be under `src/` or `src/std/`?
2. Should we expose `--backend=llvm-core` CLI flag, or keep it internal?
3. Should we extract IR building primitives, or keep them compiler-specific?
4. What's the minimum LLVM version we want to support (15, 16, 17)?
5. Should we add LLVM version detection to fail fast on old versions?

---

**Status**: PLAN READY FOR REVIEW
**Next**: Execute Phase 1 after approval
