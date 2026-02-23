# Backend Production Readiness Plan

**Status**: Design & Implementation Plan
**Date**: 2026-02-05
**Goal**: Make LLVM backend production-ready and evaluate as default for release builds

## Executive Summary

### Current State
- **Cranelift**: Production-ready (100% complete, 64-bit only)
- **LLVM**: Framework complete (~60% coverage, supports 32-bit + 64-bit)
- **Interpreter**: Fully working (95% coverage, debugging/testing)
- **WebAssembly**: Framework only (~20% coverage)
- **Lean**: Experimental (~15% coverage)

### Proposal
Make LLVM the **default backend for release builds** while keeping Cranelift for development builds due to:
1. Better code optimization (LLVM aggressive optimizer vs Cranelift fast codegen)
2. 32-bit architecture support (critical for embedded/IoT)
3. Industry-standard backend (mature, well-tested)
4. Future expansion path (GPU, SIMD vectorization)

### Timeline
- **Phase 1**: Complete LLVM implementation (4-6 weeks)
- **Phase 2**: Production hardening (2-3 weeks)
- **Phase 3**: Default switch + validation (1-2 weeks)
- **Total**: 7-11 weeks to production-ready LLVM backend

---

## 1. ARCHITECTURE OVERVIEW

### Backend Ecosystem

```
┌─────────────────────────────────────────────────────────────┐
│                    Simple Compiler Pipeline                  │
├─────────────────────────────────────────────────────────────┤
│  Frontend: Lexer → Parser → Type Check → HIR               │
│  Middle-end: HIR → MIR Lowering                             │
│  Backend Selection (based on target + build mode)           │
└─────────────────────────────────────────────────────────────┘
                              │
         ┌────────────────────┼────────────────────┐
         │                    │                    │
    ┌────▼────┐         ┌────▼────┐         ┌────▼────┐
    │Cranelift│         │  LLVM   │         │Interpret│
    │ (Fast)  │         │(Quality)│         │ (Debug) │
    └────┬────┘         └────┬────┘         └────┬────┘
         │                    │                    │
    ┌────▼────┐         ┌────▼────┐         ┌────▼────┐
    │ JIT/AOT │         │  AOT    │         │  HIR    │
    │ 64-bit  │         │32+64-bit│         │  Exec   │
    └─────────┘         └─────────┘         └─────────┘
```

### Target Architecture Support Matrix

| Architecture | Cranelift | LLVM | Interpreter | Wasm | Recommended |
|--------------|-----------|------|-------------|------|-------------|
| x86_64       | ✅ 100%   | ⚠️ 60%  | ✅ 95%      | N/A  | Cranelift (dev), LLVM (prod) |
| AArch64      | ✅ 100%   | ⚠️ 60%  | ✅ 95%      | N/A  | Cranelift (dev), LLVM (prod) |
| RISC-V 64    | ✅ 100%   | ⚠️ 60%  | ✅ 95%      | N/A  | Cranelift (dev), LLVM (prod) |
| i686         | ❌ 0%     | ⚠️ 60%  | ✅ 95%      | N/A  | **LLVM only** |
| ARMv7        | ❌ 0%     | ⚠️ 60%  | ✅ 95%      | N/A  | **LLVM only** |
| RISC-V 32    | ❌ 0%     | ⚠️ 60%  | ✅ 95%      | N/A  | **LLVM only** |
| Wasm32       | ❌ 0%     | ⚠️ 20%  | ✅ 95%      | ⚠️ 20%  | Wasm backend (future) |
| Wasm64       | ❌ 0%     | ⚠️ 20%  | ✅ 95%      | ⚠️ 20%  | Wasm backend (future) |

**Legend**: ✅ Production-ready | ⚠️ Partial implementation | ❌ Not supported

---

## 2. COMPREHENSIVE GAP ANALYSIS

### Critical Missing Components (TIER 1 - BLOCKING)

#### 2.1. LLVM Type System Bridge (Priority: P0)

**Current Status**: Stub implementation only
**Location**: `src/compiler/backend/llvm_backend.spl:258-271`

**What's Missing**:
```simple
fn mir_type_to_llvm(ty: MirType) -> text:
    match ty.kind:
        case I64: "i64"
        case I32: "i32"
        # ... basic types work
        case Ptr(inner, _): "ptr"  # Opaque pointers only
        case _: "i64"  # ❌ FALLBACK - Many types not handled!
```

**Needs Implementation**:
- [ ] Struct/class type lowering (field layout, alignment)
- [ ] Array types (fixed-size + dynamic)
- [ ] Tuple types (anonymous structs)
- [ ] Function pointer types (for closures)
- [ ] Generic instantiation (monomorphization required)
- [ ] Reference capabilities (mut, iso) → LLVM metadata
- [ ] Type metadata for GC (if GC is used)

**Estimated Work**: 1-2 weeks

#### 2.2. Complete MIR → LLVM IR Instruction Lowering (Priority: P0)

**Current Coverage**: ~30% of 80+ MIR instruction variants

**What Works**:
```simple
# From llvm_backend.spl:321-341
match inst.kind:
    case Assign(dest, value):  # Partially implemented
        val dest_name = self.get_local(dest.id)
        # ❌ Rvalue translation not complete
```

**Instruction Categories Needing Implementation**:

| Category | Instructions | Status | Priority |
|----------|-------------|--------|----------|
| **Arithmetic** | Add, Sub, Mul, Div, Mod, Neg | ⚠️ Basic only | P0 |
| **Bitwise** | And, Or, Xor, Shl, Shr, Not | ❌ Missing | P0 |
| **Comparison** | Eq, Ne, Lt, Le, Gt, Ge | ⚠️ Partial | P0 |
| **Memory** | Load, Store, Copy, Alloca | ⚠️ Basic only | P0 |
| **Control Flow** | Goto, Branch, Switch, Return | ⚠️ Partial | P0 |
| **Function Calls** | Call, CallIndirect, Invoke | ❌ Missing | P0 |
| **Collections** | ArrayLit, TupleLit, DictLit, IndexGet, IndexSet | ❌ Missing | P1 |
| **Pattern Matching** | Match, Is, As, Guard | ❌ Missing | P1 |
| **Closures** | ClosureLit, Capture, Apply | ❌ Missing | P1 |
| **SIMD** | VecLit, VecSum, VecProduct, VecFMA, VecShuffle | ❌ Missing | P2 |
| **GPU** | GpuGlobalId, GpuBarrier, GpuAtomic* | ❌ Missing | P2 |
| **Async** | AsyncAwait, AsyncYield, ActorSpawn, ActorSend | ❌ Missing | P2 |
| **Error Handling** | Try, Catch, Throw, Unwind | ❌ Missing | P1 |

**Total Missing**: 50+ instruction variants (out of 80+)

**Estimated Work**: 3-4 weeks for P0+P1, 2-3 weeks for P2

#### 2.3. Object Code Generation (Priority: P0)

**Current Status**: Framework defined, no actual emission
**Location**: `src/compiler/backend/llvm_backend.spl:403-420`

**What's Stubbed**:
```simple
fn compile_module(module: MirModule) -> Result<LlvmCompileResult, CompileError>:
    # ... IR generation works

    # ❌ Would call into Rust FFI to:
    # 1. Parse LLVM IR
    # 2. Run optimization passes
    # 3. Generate object code

    Ok(LlvmCompileResult(
        object_code: nil,  # ❌ No actual object code!
        compile_time_ms: 0
    ))
```

**Needs Implementation**:
- [ ] Rust FFI bindings for LLVM object emission
- [ ] Target machine configuration
- [ ] Optimization pass execution
- [ ] Object file format selection (ELF, PE, Mach-O)
- [ ] Relocation handling
- [ ] Symbol table generation
- [ ] Section management (.text, .data, .rodata, .bss)

**Estimated Work**: 1-2 weeks

#### 2.4. Runtime FFI Integration (Priority: P0)

**Issue**: LLVM backend needs to emit extern declarations for runtime functions

**Current Runtime FFI** (from `src/app/io/mod.spl`):
- 50+ `extern fn rt_*()` functions
- File I/O, process execution, memory management
- String operations, collections, error handling

**Needs**:
- [ ] LLVM extern function declarations
- [ ] Calling convention mapping (C ABI)
- [ ] Type marshalling (Simple types ↔ C types)
- [ ] Symbol name mangling consistency
- [ ] Varargs support (for printf-like functions)

**Estimated Work**: 1 week

#### 2.5. Testing and Validation (Priority: P0)

**Current Test Coverage**: 110+ tests, but only 36 actually test LLVM (rest are framework)

**What's Missing**:
- [ ] Differential testing: Cranelift vs LLVM output comparison
- [ ] Instruction-level verification tests
- [ ] Cross-architecture validation (x86_64 ↔ i686 ↔ ARMv7)
- [ ] Integration tests (full compile → link → execute)
- [ ] Performance benchmarks (compile speed + runtime speed)
- [ ] Memory safety tests (no leaks, correct lifetimes)

**Test Files to Expand**:
- `test/system/features/llvm_backend/llvm_backend_spec.spl` (179 lines, @pending)
- `test/compiler/backend/differential_testing_spec.spl` (needs LLVM variant)
- `test/compiler/backend/instruction_coverage_spec.spl` (needs LLVM coverage)

**Estimated Work**: 2-3 weeks

---

### Important Missing Components (TIER 2 - STRONGLY RECOMMENDED)

#### 2.6. Debug Information (DWARF/Debug Symbols)

**Current Status**: No debug info generation at all

**Impact**:
- No stack traces in production binaries
- Debuggers (GDB/LLDB) cannot inspect variables
- Profilers cannot map samples to source lines

**Needs**:
- [ ] DWARF debug info generation via LLVM DIBuilder
- [ ] Source line to instruction mapping
- [ ] Variable location tracking
- [ ] Type information for debuggers
- [ ] Inline frame tracking

**Estimated Work**: 2 weeks

#### 2.7. Calling Convention Support

**Current Status**: Default C calling convention only

**Needs for Production**:
- [ ] System V ABI (Linux/BSD) - partially working
- [ ] Win64 calling convention (Windows x86_64)
- [ ] ARM EABI (32-bit ARM)
- [ ] RISC-V calling convention
- [ ] Variadic function support
- [ ] Stack alignment per platform

**Estimated Work**: 1 week

#### 2.8. Platform-Specific Object Formats

**Current Status**: ELF only (partially through Cranelift)

**Needs**:
- [ ] **Windows PE/COFF**: Object files, relocations, symbol tables
- [ ] **macOS Mach-O**: Object files, sections, dynamic linking
- [ ] **Linux ELF**: Complete implementation (relocatable, shared, executable)

**Estimated Work**: 2-3 weeks (1 week per platform)

#### 2.9. 32-bit Architecture Validation

**Critical for LLVM as Default**: Must validate on real hardware

**Test Requirements**:
- [ ] i686 (Intel 32-bit) execution tests
- [ ] ARMv7 (Raspberry Pi 2/3) execution tests
- [ ] RISC-V 32 (QEMU or SiFive boards) execution tests
- [ ] Cross-compilation toolchain setup
- [ ] ABI compliance verification

**Estimated Work**: 1-2 weeks

#### 2.10. Error Recovery and Fallback

**Current Status**: Basic error types defined, no fallback strategy

**Needs**:
- [ ] Graceful fallback: LLVM fails → try Cranelift
- [ ] Error categorization (recoverable vs fatal)
- [ ] User-friendly error messages
- [ ] Compilation mode selection (force backend via flag)
- [ ] Build system integration for fallback

**Estimated Work**: 1 week

---

### Nice-to-Have Components (TIER 3 - FUTURE WORK)

#### 2.11. JIT Compilation (LLVM ORC)

**Current Status**: Not implemented (Cranelift JIT works)

**Use Cases**:
- Interactive REPL
- Fast development iteration
- Dynamic code loading

**Estimated Work**: 3-4 weeks

#### 2.12. Advanced Optimizations

**Needs**:
- [ ] Link-Time Optimization (LTO)
- [ ] Profile-Guided Optimization (PGO)
- [ ] Auto-vectorization (loop vectorization)
- [ ] Interprocedural optimization
- [ ] Constant propagation across modules

**Estimated Work**: 4-6 weeks (ongoing)

#### 2.13. SIMD Support

**Current Status**: SIMD instructions defined in MIR, no backend support

**Needs**:
- [ ] LLVM vector type lowering
- [ ] SIMD intrinsic mapping (AVX2, AVX-512, NEON, SVE)
- [ ] Auto-vectorization hints
- [ ] Alignment requirements
- [ ] Performance validation

**Estimated Work**: 3-4 weeks

#### 2.14. GPU/CUDA Support

**Current Status**: GPU instructions in MIR, no backend

**Needs**:
- [ ] LLVM NVPTX backend integration
- [ ] PTX code generation
- [ ] CUDA runtime bindings
- [ ] Kernel launch infrastructure
- [ ] Memory transfer management

**Estimated Work**: 4-6 weeks

---

## 3. IMPLEMENTATION PLAN

### Phase 1: Complete LLVM AOT Compilation (4-6 weeks)

**Goal**: End-to-end compilation from MIR → native code via LLVM

#### Week 1-2: Type System Bridge
- [ ] Implement `mir_type_to_llvm()` for all types
- [ ] Struct/class layout calculation
- [ ] Array and tuple type lowering
- [ ] Function pointer types
- [ ] Test suite for type lowering

**Deliverable**: All MirType variants map to LLVM types

#### Week 3-4: Core Instruction Lowering (P0)
- [ ] Arithmetic operations (Add, Sub, Mul, Div, Mod, Neg)
- [ ] Bitwise operations (And, Or, Xor, Shl, Shr, Not)
- [ ] Comparison operations (Eq, Ne, Lt, Le, Gt, Ge)
- [ ] Memory operations (Load, Store, Alloca, Copy)
- [ ] Control flow (Branch, Switch, Return, Goto)
- [ ] Function calls (Call, CallIndirect)
- [ ] Test each instruction category

**Deliverable**: Core instructions compile to LLVM IR

#### Week 5: Object Code Generation
- [ ] Rust FFI for LLVM backend
  ```rust
  // src/runtime/llvm_ffi.rs
  #[no_mangle]
  pub extern "C" fn rt_llvm_compile_ir(
      ir: *const u8, ir_len: usize,
      target_triple: *const u8,
      opt_level: u8,
      out_buffer: *mut *mut u8,
      out_len: *mut usize
  ) -> i32;
  ```
- [ ] Integration with backend_api.spl
- [ ] Object file emission (ELF format)
- [ ] Symbol and relocation handling

**Deliverable**: LLVM backend produces object files

#### Week 6: Integration Testing
- [ ] End-to-end tests: source → object file
- [ ] Link object files with system linker
- [ ] Execute resulting binaries
- [ ] Compare Cranelift vs LLVM output
- [ ] Performance baseline measurement

**Deliverable**: Working LLVM compilation pipeline

---

### Phase 2: Production Hardening (2-3 weeks)

**Goal**: Stabilize LLVM backend for production use

#### Week 7: P1 Instruction Coverage
- [ ] Collections (ArrayLit, TupleLit, DictLit, IndexGet, IndexSet)
- [ ] Pattern matching (Match, Is, As)
- [ ] Closures (ClosureLit, Capture, Apply)
- [ ] Error handling (Try, propagate with ?)
- [ ] Test coverage for P1 instructions

**Deliverable**: All common language features work

#### Week 8: Platform Support
- [ ] Windows PE/COFF object generation
- [ ] macOS Mach-O object generation
- [ ] Calling convention handling (Win64, ARM EABI)
- [ ] Cross-platform test suite

**Deliverable**: Works on Windows, macOS, Linux

#### Week 9: 32-bit Validation
- [ ] Set up cross-compilation toolchain
- [ ] i686 execution tests (QEMU or real hardware)
- [ ] ARMv7 execution tests (Raspberry Pi)
- [ ] RISC-V 32 execution tests (QEMU)
- [ ] ABI compliance verification

**Deliverable**: 32-bit targets validated

---

### Phase 3: Default Switch & Validation (1-2 weeks)

**Goal**: Make LLVM the default for release builds

#### Week 10: Build System Updates
- [ ] Update `backend_api.spl` selection logic:
  ```simple
  fn default_backend_for_mode(target: CodegenTarget, mode: BuildMode) -> BackendKind:
      match mode:
          case Debug: BackendKind.Cranelift  # Fast compilation
          case Release: BackendKind.Llvm      # Better optimization
          case Test: BackendKind.Interpreter  # Fast feedback
  ```
- [ ] Add `--backend` CLI flag override
- [ ] Update build scripts
- [ ] Documentation updates

**Deliverable**: LLVM is default for release builds

#### Week 11: Validation & Benchmarking
- [ ] Comprehensive test suite execution
- [ ] Performance benchmarks:
  - Compilation speed (Cranelift vs LLVM)
  - Runtime speed (Cranelift vs LLVM)
  - Binary size comparison
- [ ] Memory profiling (compilation + runtime)
- [ ] Regression testing
- [ ] CI/CD pipeline updates

**Deliverable**: Production-ready LLVM backend

---

## 4. BACKEND SELECTION STRATEGY

### Proposed Default Selection

```simple
# src/compiler/backend/backend_api.spl

fn auto_select_backend(target: CodegenTarget, build_mode: BuildMode,
                       features: BuildFeatures) -> BackendKind:
    """
    Automatic backend selection based on context.

    Priority:
    1. User override (--backend flag)
    2. Target requirements (32-bit → LLVM only)
    3. Build mode (debug → speed, release → quality)
    4. Feature requirements (SIMD/GPU → LLVM)
    """

    # User override
    if features.backend_override.?:
        return features.backend_override.unwrap()

    # 32-bit requires LLVM
    if target.is_32bit():
        return BackendKind.Llvm

    # WebAssembly requires Wasm backend
    if target.is_wasm():
        return BackendKind.Wasm

    # Build mode determines backend for 64-bit
    match build_mode:
        case Debug:
            BackendKind.Cranelift  # Fast iteration (10-50ms per function)
        case Release:
            BackendKind.Llvm        # Optimized code (50-200ms per function)
        case Test:
            BackendKind.Interpreter # No compilation overhead
        case Bootstrap:
            BackendKind.Cranelift  # Minimize dependencies
```

### Build Mode Comparison

| Build Mode | Default Backend | Optimization | Use Case |
|------------|----------------|--------------|----------|
| **Debug** | Cranelift | -Og | Development, fast iteration |
| **Release** | LLVM | -O2 | Production deployment |
| **Release + Size** | LLVM | -Os | Embedded, size-constrained |
| **Release + Speed** | LLVM | -O3 | Performance-critical |
| **Test** | Interpreter | N/A | Unit testing |
| **Bootstrap** | Cranelift | -O1 | Compiler self-build |

### Performance Characteristics

**Compilation Speed**:
```
Cranelift: ████████████████████ 200 functions/sec (fast)
LLVM:      ████████             80 functions/sec (slower)
```

**Generated Code Quality** (estimated):
```
Cranelift: ████████████         Good code quality
LLVM:      ████████████████████ Excellent optimization
```

**Binary Size** (typical application):
```
Debug (Cranelift):    423 MB (includes debug info)
Release (Cranelift):   40 MB (optimized)
Release (LLVM):        38 MB (more aggressive optimization)
Bootstrap (Cranelift): 9.3 MB (minimal subset)
```

---

## 5. RISK MITIGATION

### Risk 1: LLVM Dependency Management

**Risk**: LLVM 18 may not be available on all platforms

**Mitigation**:
- [ ] Make LLVM optional (keep Cranelift as fallback)
- [ ] Detect LLVM availability at build time
- [ ] Graceful degradation: Fall back to Cranelift if LLVM fails
- [ ] Document LLVM installation for all platforms
- [ ] CI matrix: Test with and without LLVM

### Risk 2: Compilation Speed Regression

**Risk**: LLVM is 2-3x slower than Cranelift for compilation

**Mitigation**:
- [ ] Keep Cranelift as default for debug builds
- [ ] Implement incremental compilation caching
- [ ] Profile compilation pipeline for bottlenecks
- [ ] Parallel module compilation
- [ ] Option to disable heavy LLVM passes in development

### Risk 3: Code Quality Regression

**Risk**: LLVM backend bugs could produce incorrect code

**Mitigation**:
- [ ] Extensive differential testing (Cranelift vs LLVM vs Interpreter)
- [ ] Fuzzing infrastructure
- [ ] Gradual rollout (opt-in → default → mandatory)
- [ ] Escape hatch: `--backend=cranelift` override
- [ ] Continuous integration on multiple platforms

### Risk 4: 32-bit Platform Coverage

**Risk**: Limited access to 32-bit hardware for testing

**Mitigation**:
- [ ] QEMU emulation for i686, ARMv7, RISC-V 32
- [ ] CI/CD with cross-compilation tests
- [ ] Community testing program (call for testers)
- [ ] Conservative 32-bit feature set initially
- [ ] Document known limitations

### Risk 5: Platform-Specific Issues

**Risk**: Windows PE, macOS Mach-O may have edge cases

**Mitigation**:
- [ ] Per-platform test suites
- [ ] Use LLVM's object format handling (mature)
- [ ] Cross-platform CI (Linux, Windows, macOS)
- [ ] Platform-specific issue tracker
- [ ] Gradual platform rollout

---

## 6. TESTING STRATEGY

### Test Categories

#### A. Unit Tests (per-function validation)
**Location**: `test/compiler/backend/`

**Coverage**:
- [ ] Type lowering tests (50+ test cases)
- [ ] Instruction lowering tests (80+ test cases, one per instruction)
- [ ] IR generation tests (validation)
- [ ] Error handling tests (20+ error conditions)

#### B. Integration Tests (end-to-end)
**Location**: `test/system/features/llvm_backend/`

**Coverage**:
- [ ] Source → IR → Object → Binary (full pipeline)
- [ ] Cross-platform compilation (8 targets)
- [ ] Optimization level validation (O0, Og, O2, O3, Os)
- [ ] Linking and symbol resolution

#### C. Differential Tests (correctness)
**Location**: `test/compiler/backend/differential_testing_spec.spl`

**Coverage**:
- [ ] Cranelift vs LLVM (output comparison)
- [ ] LLVM vs Interpreter (semantic validation)
- [ ] Cross-architecture (x86_64 ↔ i686 behavior)
- [ ] Floating-point consistency (IEEE 754 compliance)

#### D. Performance Tests (benchmarking)
**Location**: `test/benchmarks/backend/`

**Metrics**:
- [ ] Compilation speed (time per function)
- [ ] Generated code speed (benchmark suite)
- [ ] Memory usage (peak resident set size)
- [ ] Binary size (final executable size)

#### E. Regression Tests (stability)
**Location**: `test/regression/`

**Coverage**:
- [ ] Historical bugs (prevent reintroduction)
- [ ] Edge cases (null pointers, integer overflow, etc.)
- [ ] Platform-specific quirks
- [ ] Optimization-level differences

### Test Execution Matrix

| Platform | Architecture | Cranelift | LLVM | Interpreter |
|----------|-------------|-----------|------|-------------|
| Linux    | x86_64      | ✅ Full   | 🎯 Target | ✅ Full |
| Linux    | i686        | ❌ N/A    | 🎯 Target | ✅ Full |
| Linux    | AArch64     | ✅ Full   | 🎯 Target | ✅ Full |
| Linux    | ARMv7       | ❌ N/A    | 🎯 Target | ✅ Full |
| Linux    | RISC-V 64   | ✅ Full   | 🎯 Target | ✅ Full |
| Linux    | RISC-V 32   | ❌ N/A    | 🎯 Target | ✅ Full |
| Windows  | x86_64      | ✅ Full   | 🎯 Target | ✅ Full |
| Windows  | i686        | ❌ N/A    | 🎯 Target | ✅ Full |
| macOS    | x86_64      | ✅ Full   | 🎯 Target | ✅ Full |
| macOS    | AArch64     | ✅ Full   | 🎯 Target | ✅ Full |

---

## 7. DOCUMENTATION NEEDS

### User Documentation
- [ ] **Getting Started**: Build instructions with LLVM
- [ ] **Backend Selection Guide**: When to use which backend
- [ ] **Cross-Compilation Guide**: Targeting different platforms
- [ ] **Optimization Guide**: Optimization levels and flags
- [ ] **Troubleshooting**: Common LLVM issues

### Developer Documentation
- [ ] **Backend Architecture**: Design and implementation
- [ ] **Adding Instructions**: How to add new MIR instructions
- [ ] **Type System Bridge**: Type lowering algorithms
- [ ] **Calling Conventions**: Platform-specific ABIs
- [ ] **Testing Guidelines**: How to write backend tests

### API Documentation
- [ ] **BackendKind API**: Backend selection and configuration
- [ ] **CodegenTarget API**: Target specification
- [ ] **OptimizationLevel API**: Optimization control
- [ ] **LlvmBackend API**: LLVM-specific configuration

---

## 8. SUCCESS CRITERIA

### Must Have (Required for Production)
- ✅ All P0 instructions implemented (arithmetic, memory, control flow, functions)
- ✅ Object code generation works (ELF, PE, Mach-O)
- ✅ 32-bit targets validated (i686, ARMv7, RISC-V 32)
- ✅ Differential testing passes (LLVM matches Cranelift/Interpreter)
- ✅ Performance acceptable (compile speed + runtime speed)
- ✅ No memory leaks or crashes
- ✅ Error handling robust (fallback to Cranelift works)

### Should Have (Strongly Recommended)
- ✅ Debug symbols (DWARF) generated
- ✅ P1 instructions implemented (collections, closures, pattern matching)
- ✅ Windows and macOS support
- ✅ Performance benchmarks documented
- ✅ Cross-platform CI passing

### Nice to Have (Future Work)
- ⏸️ JIT support (LLVM ORC)
- ⏸️ SIMD instructions (P2 priority)
- ⏸️ GPU support (P2 priority)
- ⏸️ LTO and PGO support

---

## 9. TIMELINE SUMMARY

### Detailed Timeline

| Week | Phase | Focus Area | Deliverables |
|------|-------|-----------|--------------|
| 1-2  | Phase 1 | Type System | All MirType → LLVM type mapping |
| 3-4  | Phase 1 | Instructions (P0) | Core arithmetic, memory, control flow |
| 5    | Phase 1 | Object Emission | FFI bindings, object file generation |
| 6    | Phase 1 | Integration | End-to-end tests, baseline performance |
| 7    | Phase 2 | Instructions (P1) | Collections, closures, error handling |
| 8    | Phase 2 | Platforms | Windows PE, macOS Mach-O support |
| 9    | Phase 2 | 32-bit Testing | Cross-compilation validation |
| 10   | Phase 3 | Build System | LLVM as default, CLI flags |
| 11   | Phase 3 | Validation | Benchmarks, regression tests, CI |

### Milestone Dates

- **Week 2 (Feb 19)**: Type system complete
- **Week 4 (Mar 5)**: Core instructions working
- **Week 6 (Mar 19)**: End-to-end compilation working ← **MAJOR MILESTONE**
- **Week 9 (Apr 9)**: Production hardening complete
- **Week 11 (Apr 23)**: LLVM production-ready ← **RELEASE CANDIDATE**

---

## 10. RESOURCE REQUIREMENTS

### Development Resources
- **Senior Compiler Engineer**: 11 weeks full-time
- **Code reviewer**: 2-3 hours/week
- **Test infrastructure**: CI/CD time (parallel builds)

### Hardware Resources
- **x86_64 Linux**: Primary development (existing)
- **i686 Linux**: Cross-compilation testing (QEMU acceptable)
- **ARMv7 device**: Raspberry Pi 2/3 or equivalent
- **RISC-V boards**: QEMU or HiFive hardware (optional)
- **Windows machine**: PE/COFF testing
- **macOS machine**: Mach-O testing

### Software Dependencies
- **LLVM 18**: Must be available on all CI platforms
- **Cross-compilers**: GCC/Clang for target architectures
- **QEMU**: For cross-architecture testing
- **Debuggers**: GDB, LLDB for validation

---

## 11. DECISION POINTS

### Decision 1: LLVM as Default for Release Builds?

**Recommendation**: YES ✅

**Rationale**:
- Better code optimization (industry-standard optimizer)
- 32-bit support (critical for embedded/IoT)
- Mature backend (LLVM used by Clang, Rust, Swift)
- Future expansion (SIMD, GPU easier with LLVM)

**Tradeoffs**:
- Slower compilation (2-3x vs Cranelift)
- LLVM dependency required
- More memory during compilation

**Keep Cranelift For**:
- Debug builds (fast iteration)
- Development (quick feedback)
- Systems without LLVM

### Decision 2: Feature Flag or Always Include?

**Recommendation**: Feature flag ✅ (optional LLVM)

**Rationale**:
- Not all users need 32-bit support
- LLVM dependency is large (~500 MB installed)
- Allows gradual adoption
- Supports environments without LLVM

**Implementation**:
```toml
# Cargo.toml
[features]
default = ["cranelift-backend"]
cranelift-backend = ["cranelift-codegen", "cranelift-module"]
llvm-backend = ["inkwell", "llvm-sys"]
all-backends = ["cranelift-backend", "llvm-backend"]
```

### Decision 3: Fallback Strategy?

**Recommendation**: Graceful degradation ✅

**Implementation**:
```simple
fn compile_with_fallback(module: MirModule, target: CodegenTarget)
    -> Result<CompiledUnit, CompileError>:

    # Try LLVM first (if available)
    if llvm_available():
        match compile_llvm(module, target):
            case Ok(unit): return Ok(unit)
            case Err(e):
                print_warning("LLVM compilation failed: {e}")
                print_warning("Falling back to Cranelift...")

    # Fall back to Cranelift
    if target.is_64bit():
        return compile_cranelift(module, target)

    # 32-bit with no LLVM - error
    Err(CompileError.NotImplemented(
        "32-bit compilation requires LLVM backend"
    ))
```

---

## 12. NEXT STEPS

### Immediate Actions (This Week)
1. ✅ Review and approve this plan
2. [ ] Set up LLVM development environment
3. [ ] Create feature branch: `feature/llvm-production`
4. [ ] Create detailed task breakdown in TODO list
5. [ ] Set up progress tracking (weekly updates)

### Week 1 Tasks (Feb 5-12)
1. [ ] Implement basic type lowering (primitives)
2. [ ] Set up Rust FFI stub for LLVM
3. [ ] Create type lowering test suite
4. [ ] Document type mapping rules

### Communication Plan
- **Weekly Status Updates**: Every Monday
- **Blockers Channel**: Immediate escalation
- **Code Reviews**: 24-hour turnaround
- **Demo**: End of each phase

---

## 13. CONCLUSION

### Why This Plan Works

1. **Incremental Approach**: 11 weeks with clear milestones
2. **Risk Mitigation**: Fallback to Cranelift always available
3. **Comprehensive Testing**: Unit, integration, differential, performance
4. **Production Focus**: Addresses all critical gaps
5. **Resource Realistic**: Achievable with existing team

### Expected Outcomes

**After Phase 1 (6 weeks)**:
- LLVM backend works end-to-end
- Basic programs compile and run
- Comparable to Cranelift in functionality

**After Phase 2 (9 weeks)**:
- Production-ready LLVM backend
- All platforms supported
- 32-bit validated

**After Phase 3 (11 weeks)**:
- LLVM is default for release builds
- Full test coverage
- Documentation complete
- **Ready for v0.5.0 release**

### Long-Term Vision

With LLVM as the default release backend, Simple gains:
- **Best-in-class code generation**: Industry-standard optimizer
- **Broad platform support**: 32-bit + 64-bit, all major OSes
- **Future expansion**: SIMD, GPU, advanced optimizations
- **Competitive advantage**: First-class 32-bit support (rare in modern languages)

---

## APPENDIX A: File Locations Reference

### Implementation Files
- `src/compiler/backend/backend_api.spl` (461 lines) - Backend selection
- `src/compiler/backend/llvm_backend.spl` (442 lines) - LLVM implementation
- `src/compiler/backend/interpreter.spl` (807 lines) - Interpreter backend
- `src/compiler/backend_types.spl` - Result and error types

### Test Files
- `test/compiler/backend/backend_basic_spec.spl` (150+ lines)
- `test/compiler/backend/backend_capability_spec.spl` (320+ lines)
- `test/compiler/backend/differential_testing_spec.spl`
- `test/system/features/llvm_backend/llvm_backend_spec.spl` (179 lines, @pending)

### Documentation Files
- `doc/plan/23_llvm_backend_support.md` - Original plan
- `doc/archive/llvm_implementation_complete.md` - Phase 5 completion
- `doc/archive/codegen/llvm_backend.md` - User guide
- `BACKEND_IMPLEMENTATION_STATUS.md` - Status tracking

---

## APPENDIX B: Technology Stack

### Languages
- **Simple**: 100% of compiler (5,080 LOC in backend/)
- **Rust**: FFI bindings only

### Dependencies
- **Cranelift**: Fast native codegen (production-ready)
- **LLVM 18**: Advanced optimizer (via Inkwell)
- **Inkwell**: Rust bindings to LLVM

### Build System
- **Simple build system**: Self-hosting (100% Simple)
- **Cargo**: For Rust FFI bindings
- **Make**: Legacy support only

---

**Document Status**: Design & Implementation Plan
**Review By**: Team lead
**Approval Required**: Yes
**Target Start Date**: Week of Feb 5, 2026
**Target Completion**: Week of Apr 23, 2026 (11 weeks)
