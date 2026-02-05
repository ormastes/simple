# Backend Completeness Checklist

**Purpose**: Comprehensive checklist to ensure no components are missing before LLVM backend production release
**Date**: 2026-02-05
**Status**: Planning Document

---

## ✅ TIER 1: CRITICAL (MUST COMPLETE)

### 1.1. Type System Bridge ⬜

- [ ] **Primitive Types** (8 types)
  - [ ] I64, I32, I16, I8 → LLVM integer types
  - [ ] F64, F32 → LLVM floating-point types
  - [ ] Bool → i1
  - [ ] Unit → void

- [ ] **Composite Types** (5 categories)
  - [ ] Struct/Class types → LLVM struct
    - [ ] Field layout calculation
    - [ ] Alignment requirements
    - [ ] Padding insertion
  - [ ] Array types → LLVM array
    - [ ] Fixed-size arrays: `[T; N]`
    - [ ] Dynamic arrays: slice representation
  - [ ] Tuple types → Anonymous struct
  - [ ] Function pointer types → LLVM function type
  - [ ] Closure types → Struct with function pointer + captures

- [ ] **Advanced Types** (4 categories)
  - [ ] Generic instantiation (monomorphization)
  - [ ] Reference capabilities → LLVM metadata
    - [ ] `mut T` → mutable pointer metadata
    - [ ] `iso T` → unique ownership metadata
    - [ ] `T` → shared/immutable metadata
  - [ ] Optional types `T?` → LLVM struct with discriminant
  - [ ] Result types `Result<T, E>` → LLVM enum representation

- [ ] **Type Metadata** (for GC/debugging)
  - [ ] Type size calculation
  - [ ] Type alignment
  - [ ] GC pointer marking (if GC used)

**Total Tasks**: ~20 | **Estimated**: 1-2 weeks

---

### 1.2. MIR Instruction Lowering (P0 Instructions) ⬜

#### Arithmetic Operations (10 instructions)
- [ ] `Add(dest, lhs, rhs)` → llvm.add
- [ ] `Sub(dest, lhs, rhs)` → llvm.sub
- [ ] `Mul(dest, lhs, rhs)` → llvm.mul
- [ ] `Div(dest, lhs, rhs)` → llvm.sdiv / llvm.udiv
- [ ] `Mod(dest, lhs, rhs)` → llvm.srem / llvm.urem
- [ ] `Neg(dest, operand)` → llvm.neg
- [ ] `FAdd, FSub, FMul, FDiv` → Floating-point variants

#### Bitwise Operations (7 instructions)
- [ ] `And(dest, lhs, rhs)` → llvm.and
- [ ] `Or(dest, lhs, rhs)` → llvm.or
- [ ] `Xor(dest, lhs, rhs)` → llvm.xor
- [ ] `Shl(dest, lhs, rhs)` → llvm.shl (shift left)
- [ ] `Shr(dest, lhs, rhs)` → llvm.lshr / llvm.ashr (shift right)
- [ ] `Not(dest, operand)` → llvm.xor with -1
- [ ] `BitCount, LeadingZeros, TrailingZeros` → LLVM intrinsics

#### Comparison Operations (6 instructions)
- [ ] `Eq(dest, lhs, rhs)` → llvm.icmp eq
- [ ] `Ne(dest, lhs, rhs)` → llvm.icmp ne
- [ ] `Lt(dest, lhs, rhs)` → llvm.icmp slt / ult
- [ ] `Le(dest, lhs, rhs)` → llvm.icmp sle / ule
- [ ] `Gt(dest, lhs, rhs)` → llvm.icmp sgt / ugt
- [ ] `Ge(dest, lhs, rhs)` → llvm.icmp sge / uge

#### Memory Operations (8 instructions)
- [ ] `Load(dest, ptr, ty)` → llvm.load
- [ ] `Store(ptr, value, ty)` → llvm.store
- [ ] `Alloca(dest, ty, count)` → llvm.alloca
- [ ] `Copy(dest, src, size)` → llvm.memcpy
- [ ] `Move(dest, src, size)` → llvm.memmove
- [ ] `Fill(dest, value, size)` → llvm.memset
- [ ] `GetElementPtr(dest, base, indices)` → llvm.getelementptr
- [ ] `PtrCast(dest, ptr, ty)` → llvm.bitcast / llvm.ptrtoint

#### Control Flow (10 instructions)
- [ ] `Goto(target_block)` → llvm.br
- [ ] `Branch(cond, true_block, false_block)` → llvm.br i1
- [ ] `Switch(value, cases, default)` → llvm.switch
- [ ] `Return(value?)` → llvm.ret
- [ ] `Unreachable` → llvm.unreachable
- [ ] `Phi(dest, [(value, block)])` → llvm.phi
- [ ] `Select(dest, cond, true_val, false_val)` → llvm.select
- [ ] `Call(dest?, func, args)` → llvm.call
- [ ] `CallIndirect(dest?, func_ptr, args)` → llvm.call indirect
- [ ] `Invoke(dest?, func, args, normal, unwind)` → llvm.invoke (for exceptions)

**Total P0 Tasks**: ~41 | **Estimated**: 2-3 weeks

---

### 1.3. Function Compilation Pipeline ⬜

- [ ] **Function Signature Generation**
  - [ ] Parameter type lowering
  - [ ] Return type lowering
  - [ ] Calling convention selection
  - [ ] Variadic function support

- [ ] **Function Body Compilation**
  - [ ] Entry block creation
  - [ ] Basic block creation for MIR blocks
  - [ ] Instruction emission per block
  - [ ] Terminator handling (return, branch, etc.)

- [ ] **Local Variable Management**
  - [ ] Stack slot allocation (alloca)
  - [ ] SSA conversion (variables → SSA values)
  - [ ] Phi node insertion for control flow merges

- [ ] **Function Metadata**
  - [ ] Function attributes (noinline, alwaysinline, etc.)
  - [ ] Parameter attributes (noalias, nocapture, etc.)
  - [ ] Debug metadata (if debug info enabled)

**Total Tasks**: ~15 | **Estimated**: 1 week

---

### 1.4. Object Code Generation ⬜

- [ ] **LLVM IR to Object**
  - [ ] Parse/validate LLVM IR
  - [ ] Create target machine
  - [ ] Run optimization passes
  - [ ] Emit object code

- [ ] **Rust FFI Bindings** (in `rust/runtime/src/llvm_ffi.rs`)
  - [ ] `rt_llvm_compile_ir()` - Compile IR to object code
  - [ ] `rt_llvm_init_target()` - Initialize LLVM target
  - [ ] `rt_llvm_create_target_machine()` - Configure target
  - [ ] `rt_llvm_optimize()` - Run optimization passes
  - [ ] `rt_llvm_emit_object()` - Generate object file

- [ ] **Simple Wrapper** (in `src/compiler/backend/llvm_backend.spl`)
  - [ ] Call FFI functions
  - [ ] Handle errors and fallback
  - [ ] Return CompiledUnit with object bytes

- [ ] **Object File Formats**
  - [ ] ELF (Linux, BSD)
  - [ ] PE/COFF (Windows)
  - [ ] Mach-O (macOS)

- [ ] **Symbol Management**
  - [ ] Symbol table generation
  - [ ] Relocation entries
  - [ ] Section management (.text, .data, .rodata, .bss)

**Total Tasks**: ~15 | **Estimated**: 1-2 weeks

---

### 1.5. Runtime FFI Integration ⬜

- [ ] **Extern Function Declarations**
  - [ ] File I/O functions (~10 functions)
  - [ ] Memory management functions (~5 functions)
  - [ ] String operations (~8 functions)
  - [ ] Collection operations (~12 functions)
  - [ ] Error handling functions (~5 functions)
  - [ ] Process operations (~6 functions)
  - [ ] Environment functions (~4 functions)

- [ ] **Calling Convention Mapping**
  - [ ] System V ABI (Linux/BSD)
  - [ ] Win64 calling convention
  - [ ] ARM EABI
  - [ ] RISC-V calling convention

- [ ] **Type Marshalling**
  - [ ] Simple `text` ↔ C `char*`
  - [ ] Simple `[T]` ↔ C array pointer + length
  - [ ] Simple `bool` ↔ C `bool` / `i8`
  - [ ] Simple `i64` ↔ C `int64_t`
  - [ ] Simple `Dict` ↔ C struct representation

- [ ] **Symbol Name Mangling**
  - [ ] Consistent with Cranelift backend
  - [ ] No name collisions
  - [ ] C-compatible names for FFI

**Total Tasks**: ~25 | **Estimated**: 1 week

---

### 1.6. Testing Infrastructure ⬜

#### Unit Tests (per-function validation)
- [ ] **Type Lowering Tests** (~50 tests)
  - [ ] Primitive types (8 tests)
  - [ ] Struct types (10 tests)
  - [ ] Array types (8 tests)
  - [ ] Function pointer types (6 tests)
  - [ ] Generic types (10 tests)
  - [ ] Reference capabilities (8 tests)

- [ ] **Instruction Lowering Tests** (~80 tests)
  - [ ] One test per MIR instruction variant
  - [ ] Edge cases (division by zero, overflow, etc.)
  - [ ] Type-specific variants (int vs float)

- [ ] **IR Generation Tests** (~20 tests)
  - [ ] Function signature generation
  - [ ] Basic block creation
  - [ ] Phi node insertion
  - [ ] IR validation

- [ ] **Error Handling Tests** (~20 tests)
  - [ ] Type mismatch errors
  - [ ] Unsupported instruction errors
  - [ ] LLVM compilation errors
  - [ ] Fallback to Cranelift

#### Integration Tests (end-to-end)
- [ ] **Compilation Pipeline Tests** (~30 tests)
  - [ ] Source → IR → Object → Binary
  - [ ] Small programs (Hello World, FizzBuzz, etc.)
  - [ ] Medium programs (sorting, search algorithms)
  - [ ] Complex programs (mini compiler, interpreter)

- [ ] **Cross-Platform Tests** (~15 tests)
  - [ ] Linux x86_64, i686
  - [ ] Windows x86_64, i686
  - [ ] macOS x86_64, AArch64
  - [ ] Linux AArch64, ARMv7
  - [ ] Linux RISC-V 64, RISC-V 32

- [ ] **Optimization Level Tests** (~10 tests)
  - [ ] -O0 (no optimization)
  - [ ] -Og (debug optimization)
  - [ ] -O1, -O2, -O3 (speed)
  - [ ] -Os (size)

#### Differential Tests (correctness validation)
- [ ] **Cranelift vs LLVM** (~50 tests)
  - [ ] Output comparison (stdout, return values)
  - [ ] Behavior equivalence
  - [ ] Floating-point consistency

- [ ] **LLVM vs Interpreter** (~50 tests)
  - [ ] Semantic correctness
  - [ ] Edge case handling

- [ ] **Cross-Architecture** (~20 tests)
  - [ ] x86_64 ↔ i686 behavior
  - [ ] AArch64 ↔ ARMv7 behavior
  - [ ] Endianness consistency

#### Performance Tests (benchmarking)
- [ ] **Compilation Speed** (~10 benchmarks)
  - [ ] Small, medium, large programs
  - [ ] Different optimization levels
  - [ ] Cranelift vs LLVM comparison

- [ ] **Runtime Speed** (~20 benchmarks)
  - [ ] Micro-benchmarks (arithmetic, loops)
  - [ ] Macro-benchmarks (algorithms, data structures)
  - [ ] Real-world programs

- [ ] **Memory Usage** (~5 benchmarks)
  - [ ] Peak memory during compilation
  - [ ] Runtime memory usage
  - [ ] Memory leak detection

- [ ] **Binary Size** (~5 benchmarks)
  - [ ] Final executable size
  - [ ] Per-optimization level
  - [ ] Stripped vs unstripped

**Total Test Tasks**: ~390 tests | **Estimated**: 2-3 weeks

---

## ✅ TIER 2: IMPORTANT (STRONGLY RECOMMENDED)

### 2.1. P1 Instruction Coverage ⬜

#### Collection Operations (12 instructions)
- [ ] `ArrayLit(dest, elements)` → Struct with pointer + length
- [ ] `TupleLit(dest, elements)` → Anonymous struct literal
- [ ] `DictLit(dest, pairs)` → Hash map initialization
- [ ] `IndexGet(dest, collection, index)` → GEP + load
- [ ] `IndexSet(collection, index, value)` → GEP + store
- [ ] `Slice(dest, array, start, end)` → Create slice view
- [ ] `Concat(dest, lhs, rhs)` → Array concatenation
- [ ] `Append(dest, array, element)` → Push to array
- [ ] `Length(dest, collection)` → Get length field
- [ ] `Capacity(dest, collection)` → Get capacity field
- [ ] `Reserve(collection, additional)` → Realloc if needed
- [ ] `Clear(collection)` → Set length to 0

#### Pattern Matching (8 instructions)
- [ ] `Match(value, arms)` → Switch/branch tree
- [ ] `Is(dest, value, variant)` → Type test
- [ ] `As(dest, value, ty)` → Type cast
- [ ] `Guard(cond, success_block, fail_block)` → Conditional branch
- [ ] `Unpack(dests, value)` → Destructure tuple/struct
- [ ] `VariantTag(dest, enum_value)` → Extract discriminant
- [ ] `VariantData(dest, enum_value, variant)` → Extract payload
- [ ] `WildcardMatch` → Unconditional branch to default

#### Closure Support (6 instructions)
- [ ] `ClosureLit(dest, func, captures)` → Allocate closure object
- [ ] `Capture(dest, var)` → Copy variable to closure
- [ ] `Apply(dest, closure, args)` → Call closure function pointer
- [ ] `PartialApply(dest, func, partial_args)` → Currying support
- [ ] `ClosureEnv(dest, closure)` → Get capture environment
- [ ] `FreeClosureEnv(closure)` → Deallocate captures

#### Error Handling (6 instructions)
- [ ] `Try(value, ok_block, err_block)` → Result unwrap or branch
- [ ] `Propagate(result)` → ? operator (early return on Err)
- [ ] `WrapOk(dest, value)` → Create Ok variant
- [ ] `WrapErr(dest, error)` → Create Err variant
- [ ] `UnwrapOr(dest, optional, default)` → Get value or default
- [ ] `UnwrapOrElse(dest, optional, func)` → Get value or compute

**Total P1 Tasks**: ~32 | **Estimated**: 2 weeks

---

### 2.2. Debug Information (DWARF) ⬜

- [ ] **DIBuilder Setup**
  - [ ] Initialize LLVM DIBuilder
  - [ ] Create compile unit
  - [ ] Set source file metadata

- [ ] **Type Debug Info**
  - [ ] DIBasicType for primitives
  - [ ] DICompositeType for structs
  - [ ] DISubroutineType for functions
  - [ ] DIDerivedType for pointers

- [ ] **Function Debug Info**
  - [ ] DISubprogram for each function
  - [ ] DILocalVariable for parameters
  - [ ] DILocalVariable for local variables
  - [ ] DILexicalBlock for scopes

- [ ] **Line Mapping**
  - [ ] DILocation for each instruction
  - [ ] Source line → IR instruction mapping
  - [ ] Inline frame tracking

- [ ] **Variable Inspection**
  - [ ] Variable lifetime tracking
  - [ ] Location information (register, stack, etc.)
  - [ ] Value availability

**Total Tasks**: ~20 | **Estimated**: 2 weeks

---

### 2.3. Platform-Specific Support ⬜

#### Windows PE/COFF (Priority: High)
- [ ] PE object file generation
- [ ] Windows calling convention (Win64)
- [ ] Import/export tables
- [ ] Exception handling (SEH)
- [ ] DLL linking support

#### macOS Mach-O (Priority: High)
- [ ] Mach-O object file generation
- [ ] macOS calling convention
- [ ] Objective-C interop (if needed)
- [ ] Dylib linking support
- [ ] Code signing support

#### Linux ELF (Priority: High)
- [ ] Complete ELF implementation
- [ ] Position Independent Code (PIC)
- [ ] Shared library support (.so)
- [ ] Static linking
- [ ] RPATH handling

**Total Tasks**: ~15 | **Estimated**: 2-3 weeks

---

### 2.4. 32-bit Architecture Validation ⬜

- [ ] **i686 (Intel 32-bit)**
  - [ ] Set up cross-compilation toolchain
  - [ ] ABI compliance tests
  - [ ] Execution tests (QEMU or real hardware)
  - [ ] Performance validation

- [ ] **ARMv7 (ARM 32-bit)**
  - [ ] Set up cross-compilation toolchain
  - [ ] EABI compliance tests
  - [ ] Execution tests (Raspberry Pi 2/3)
  - [ ] Hard-float vs soft-float

- [ ] **RISC-V 32**
  - [ ] Set up cross-compilation toolchain
  - [ ] ABI compliance tests
  - [ ] Execution tests (QEMU)
  - [ ] Compressed instruction support

**Total Tasks**: ~12 | **Estimated**: 1-2 weeks

---

### 2.5. Error Recovery and Fallback ⬜

- [ ] **Error Detection**
  - [ ] LLVM compilation errors
  - [ ] Type lowering errors
  - [ ] Unsupported instruction errors
  - [ ] Target unavailable errors

- [ ] **Fallback Strategy**
  - [ ] Detect LLVM availability
  - [ ] Graceful degradation to Cranelift
  - [ ] User notification (warning messages)
  - [ ] Preserve semantics across backends

- [ ] **Error Reporting**
  - [ ] User-friendly error messages
  - [ ] Suggested fixes (install LLVM, etc.)
  - [ ] Diagnostic information for bug reports

**Total Tasks**: ~10 | **Estimated**: 1 week

---

## ✅ TIER 3: NICE-TO-HAVE (FUTURE WORK)

### 3.1. P2 Instruction Coverage (SIMD) ⬜

- [ ] `VecLit(dest, elements)` → LLVM vector type
- [ ] `VecLoad(dest, ptr)` → Load vector
- [ ] `VecStore(ptr, vec)` → Store vector
- [ ] `VecAdd, VecSub, VecMul, VecDiv` → Vector arithmetic
- [ ] `VecShuffle(dest, vec, mask)` → Shuffle intrinsic
- [ ] `VecExtract(dest, vec, index)` → Extract element
- [ ] `VecInsert(dest, vec, index, value)` → Insert element
- [ ] `VecReduce(dest, vec, op)` → Horizontal reduction
- [ ] `VecFMA(dest, a, b, c)` → Fused multiply-add
- [ ] `VecSqrt(dest, vec)` → Vector square root
- [ ] `VecRsqrt(dest, vec)` → Reciprocal square root
- [ ] `VecAbs(dest, vec)` → Absolute value

**Total Tasks**: ~12 | **Estimated**: 2-3 weeks

---

### 3.2. GPU Support (CUDA/PTX) ⬜

- [ ] `GpuKernelLaunch(func, grid, block, args)` → CUDA kernel launch
- [ ] `GpuGlobalId(dest, dim)` → threadIdx + blockIdx * blockDim
- [ ] `GpuLocalId(dest, dim)` → threadIdx
- [ ] `GpuGroupId(dest, dim)` → blockIdx
- [ ] `GpuGlobalSize(dest, dim)` → gridDim * blockDim
- [ ] `GpuLocalSize(dest, dim)` → blockDim
- [ ] `GpuBarrier()` → __syncthreads()
- [ ] `GpuMemFence()` → __threadfence()
- [ ] `GpuAtomicAdd, GpuAtomicSub, etc.` → atomicAdd, atomicSub
- [ ] `GpuSharedAlloc(dest, size)` → __shared__ memory

**Total Tasks**: ~10 | **Estimated**: 3-4 weeks

---

### 3.3. Async/Actor Support ⬜

- [ ] `AsyncAwait(dest, future)` → Async runtime call
- [ ] `AsyncYield()` → Suspend current task
- [ ] `ActorSpawn(dest, func, args)` → Create actor
- [ ] `ActorSend(actor, message)` → Send message to actor
- [ ] `ActorRecv(dest, actor)` → Receive message from actor
- [ ] `FutureCreate(dest, func)` → Create future
- [ ] `FutureGet(dest, future)` → Block on future result

**Total Tasks**: ~7 | **Estimated**: 2-3 weeks

---

### 3.4. JIT Support (LLVM ORC) ⬜

- [ ] **ORC JIT Setup**
  - [ ] Initialize ORC JIT engine
  - [ ] Create JIT dylib
  - [ ] Symbol resolution

- [ ] **Lazy Compilation**
  - [ ] Compile-on-demand
  - [ ] Function lazy compilation
  - [ ] Module lazy compilation

- [ ] **Dynamic Linking**
  - [ ] Runtime symbol resolution
  - [ ] Dynamic library loading
  - [ ] Weak symbol support

**Total Tasks**: ~10 | **Estimated**: 3-4 weeks

---

### 3.5. Advanced Optimizations ⬜

- [ ] **Link-Time Optimization (LTO)**
  - [ ] Thin LTO support
  - [ ] Full LTO support
  - [ ] Cross-module inlining

- [ ] **Profile-Guided Optimization (PGO)**
  - [ ] Instrumentation pass
  - [ ] Profile collection
  - [ ] Profile-driven optimization

- [ ] **Auto-Vectorization**
  - [ ] Loop vectorization
  - [ ] SLP vectorization
  - [ ] Vectorization hints

**Total Tasks**: ~10 | **Estimated**: 4-6 weeks

---

## 📊 SUMMARY STATISTICS

### Total Tasks Breakdown

| Tier | Category | Tasks | Estimated Time |
|------|----------|-------|----------------|
| **Tier 1** | Type System | 20 | 1-2 weeks |
| **Tier 1** | P0 Instructions | 41 | 2-3 weeks |
| **Tier 1** | Function Pipeline | 15 | 1 week |
| **Tier 1** | Object Generation | 15 | 1-2 weeks |
| **Tier 1** | Runtime FFI | 25 | 1 week |
| **Tier 1** | Testing | 390 | 2-3 weeks |
| **Tier 2** | P1 Instructions | 32 | 2 weeks |
| **Tier 2** | Debug Info | 20 | 2 weeks |
| **Tier 2** | Platforms | 15 | 2-3 weeks |
| **Tier 2** | 32-bit Validation | 12 | 1-2 weeks |
| **Tier 2** | Error Recovery | 10 | 1 week |
| **Tier 3** | SIMD | 12 | 2-3 weeks |
| **Tier 3** | GPU | 10 | 3-4 weeks |
| **Tier 3** | Async | 7 | 2-3 weeks |
| **Tier 3** | JIT | 10 | 3-4 weeks |
| **Tier 3** | Advanced Opts | 10 | 4-6 weeks |

### Time Estimates

- **Tier 1 (Critical)**: 7-11 weeks
- **Tier 2 (Important)**: +5-8 weeks
- **Tier 3 (Nice-to-have)**: +14-20 weeks

**Minimum for Production Release**: 7-11 weeks (Tier 1 only)
**Recommended for Production**: 12-19 weeks (Tier 1 + Tier 2)
**Full Feature Parity**: 26-39 weeks (All tiers)

---

## 🎯 RECOMMENDED APPROACH

### Phase 1: Production Minimum (Weeks 1-11)
Focus on Tier 1 tasks only. Goal: LLVM backend works end-to-end with core features.

### Phase 2: Production Recommended (Weeks 12-19)
Add Tier 2 tasks. Goal: Full platform support, debugging, 32-bit validated.

### Phase 3: Advanced Features (Weeks 20+)
Add Tier 3 tasks incrementally based on user demand.

---

**Document Purpose**: Prevent missing components during LLVM backend implementation
**Usage**: Check off items as completed, track progress
**Review**: Weekly review during implementation
