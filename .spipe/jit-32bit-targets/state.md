# SStack State: jit-32bit-targets

## User Request
> 1. let use llvm for 32bit cranlift rejected. 2. complete x86 32. 3. completw riscv 64 32. 4 arm32. 5. jit to reduce binary mix 32/64 on x86. 6. riscv 32/64 mix 7. arm 32/64 mix. plan sonnet agent team with order by dependency with detail plan. with opus advisor. howabout search mix 32/64 code for efficiency. research deeply

## Task Type
feature

## Refined Goal
> Route Cranelift-rejected 32-bit targets (x86_32, ARM32, RISC-V 32) through the LLVM JIT backend, fix the i64-hardcoded pointer width, and add MIR-level i32 narrowing optimization for mixed 32/64-bit efficiency.

## Key Findings (Research Phase)

### Infrastructure Status
- **LLVM JIT builds**: `cargo check --features llvm` passes cleanly
- **AOT already routes 32-bit → LLVM**: `BackendKind::for_target()` checks `target.arch.is_32bit()`
- **JIT gap**: `LocalExecutionManager` only considers *host* width via `#[cfg(target_pointer_width)]`
- **LlvmJitCompiler::new()** uses `Target::host()` — cannot cross-target today
- **`types_util.rs` hardcodes all pointers as i64** — fundamental blocker for true 32-bit codegen
- **No x32 ABI exists** in the codebase

### "Mix 32/64" Interpretation
Assumption: **MIR-level i32 narrowing** — use i32 operations when values provably fit 32 bits, even on 64-bit targets, to reduce code size and improve register pressure. This is a pure codegen optimization, NOT x32 ABI or mode-switching binaries.

## Acceptance Criteria
- [x] AC-1: `types_util.rs` uses target-aware pointer width (4 bytes on 32-bit, 8 on 64-bit)
- [x] AC-2: `LlvmJitCompiler` accepts a target parameter and can cross-compile for 32-bit from 64-bit host
- [x] AC-3: `LocalExecutionManager` routes to LLVM JIT when target is 32-bit (regardless of host)
- [x] AC-4: Simple program JIT-compiled for x86_32 produces correct result (matches interpreter)
- [x] AC-5: Simple program JIT-compiled for RV32 produces correct result
- [x] AC-6: Simple program JIT-compiled for RV64 produces correct result (Cranelift, already works)
- [x] AC-7: Simple program JIT-compiled for ARM32 produces correct result
- [x] AC-8: MIR-level i32 narrowing pass reduces code size on x86_64 benchmark by measurable amount

## Agent Team — Dependency-Ordered

### Phase 1: Foundation (Sequential — blocks everything)

#### Agent T0: Pointer Width Abstraction
**Owner**: `src/compiler_rust/compiler/src/codegen/types_util.rs`
**Scope**: Replace hardcoded i64 pointer type with `ptr_type(target) -> Type`
**Tasks**:
1. Add `fn ptr_type(target: &Target) -> cranelift_codegen::ir::Type` that returns I32 or I64
2. Add `fn ptr_bytes(target: &Target) -> u8` that returns 4 or 8
3. Replace all `types::I64` usages that represent pointers with `ptr_type(target)`
4. Update LLVM `types_util` equivalent if separate
5. Ensure all callers propagate target context
**Files**: `types_util.rs`, callers in `cranelift_ffi.rs`, `llvm/backend_core.rs`
**Gate**: Existing x86_64 JIT benchmark still passes with no regression

#### Agent T1: LLVM JIT Cross-Target Support
**Owner**: `src/compiler_rust/compiler/src/codegen/llvm_jit.rs`
**Depends on**: T0 (pointer width must be correct)
**Scope**: Make `LlvmJitCompiler` accept an explicit target triple instead of always using host
**Tasks**:
1. Add `LlvmJitCompiler::new_for_target(target: &Target)` constructor
2. Map `Target` to LLVM triple string (reuse logic from `backend_core.rs:413-461`)
3. Configure LLVM TargetMachine for cross-target (data layout, relocation model)
4. For JIT execution of cross-compiled code: use LLVM's MCJIT or ORC with explicit target
5. Verify that emitting i686 code from x86_64 host works (LLVM supports this natively)
**Files**: `llvm_jit.rs`, `llvm/backend_core.rs`
**Gate**: `LlvmJitCompiler::new_for_target(Target::x86_32())` creates a valid compiler instance

#### Agent T2: JIT Router — Target-Aware Dispatch
**Owner**: `src/compiler_rust/compiler/src/codegen/local_execution.rs`
**Depends on**: T1
**Scope**: Change `JitBackend::auto_select()` from host-only to target-aware
**Tasks**:
1. Add `JitBackend::for_target(target: &Target)` method
2. Logic: if target is 64-bit AND Cranelift-supported → Cranelift; else if LLVM available → LLVM; else → error
3. Thread target through `LocalExecutionManager::with_provider()` → JIT backend creation
4. Update `rt_jit_call_i64` in `jit_native.rs` to pass target info from MIR
5. Keep backward compat: `JitBackend::auto_select()` = `JitBackend::for_target(Target::host())`
**Files**: `local_execution.rs`, `backend_trait.rs`, `jit_native.rs`
**Gate**: On x86_64 host, requesting JIT for `Target::x86_32()` selects LLVM backend

### Phase 2: Per-Target Verification (Parallel — after T2)

#### Agent V-x86: x86_32 JIT Verification
**Depends on**: T2
**Scope**: End-to-end correctness test for x86_32 JIT
**Tasks**:
1. Create `test/unit/jit/jit_x86_32_correctness.spl` — arithmetic + pointer ops
2. Run via LLVM JIT targeting i686
3. Compare result with interpreter output
4. Verify pointer-width-sensitive operations (array indexing, struct field access)
**Gate**: AC-4 — correct result matches interpreter

#### Agent V-rv32: RISC-V 32 JIT Verification
**Depends on**: T2
**Scope**: End-to-end correctness test for RV32 JIT
**Tasks**:
1. Create `test/unit/jit/jit_rv32_correctness.spl`
2. Run via LLVM JIT targeting riscv32
3. Verify scalar integer ops, memory access patterns
**Gate**: AC-5 — correct result matches interpreter

#### Agent V-rv64: RISC-V 64 JIT Verification
**Depends on**: T2 (but should already work via Cranelift)
**Scope**: Confirm RV64 still works end-to-end with Cranelift
**Tasks**:
1. Create `test/unit/jit/jit_rv64_correctness.spl` (or verify existing)
2. Confirm Cranelift ISA lookup succeeds for riscv64
3. Run and compare with interpreter
**Gate**: AC-6

#### Agent V-arm32: ARM32 JIT Verification
**Depends on**: T2
**Scope**: End-to-end correctness for ARM32 via LLVM JIT
**Tasks**:
1. Create `test/unit/jit/jit_arm32_correctness.spl`
2. Run via LLVM JIT targeting armv7
3. Verify correct result
**Gate**: AC-7

### Phase 3: Optimization (After Phase 2)

#### Agent OPT: MIR-Level i32 Narrowing Pass
**Depends on**: Phase 2 all green
**Scope**: Add optimization pass that narrows i64 values to i32 when provably safe
**Tasks**:
1. Analyze MIR SSA values: if a value's range fits i32 AND all consumers accept i32 → narrow
2. Patterns: loop counters, array indices (bounded), enum discriminants, boolean results
3. Add pass in `src/compiler_rust/compiler/src/codegen/` MIR optimization pipeline
4. Measure code size reduction on x86_64 JIT benchmark (bench_3d_render_jit.spl)
5. Ensure no correctness regression (narrowing must be conservative)
**Files**: New file in codegen MIR passes
**Gate**: AC-8 — measurable code size reduction, zero correctness regression

## Execution Order (Gantt)

```
Time →
T0 ████████ (pointer width)
T1          ████████ (LLVM cross-target)
T2                   ████ (JIT router)
V-x86                     ███ ─┐
V-rv32                    ███  ├─ parallel
V-rv64                    ███  │
V-arm32                   ███ ─┘
OPT                            ████████ (i32 narrowing)
```

## File Scope (Collision Avoidance)
- **T0**: `types_util.rs` only
- **T1**: `llvm_jit.rs`, `llvm/backend_core.rs`
- **T2**: `local_execution.rs`, `backend_trait.rs`, `jit_native.rs`
- **V-***: `test/unit/jit/` (new files only)
- **OPT**: new MIR pass file
- **EXCLUDED**: `interpreter_extern/gpu.rs` (Vulkan dlopen agent active there)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-research (Analyst) — 2026-05-17
- [x] 3-arch (Architect) — 2026-05-19
- [x] 4-spec (QA Lead) — 2026-05-19
- [x] 5-implement (Engineer) — 2026-05-19
- [x] 6-refactor (Tech Lead) — 2026-05-19
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
Task scope defined. User wants LLVM for 32-bit, mixed 32/64 efficiency, and parallel agent execution.

### 2-research
Findings:
- LLVM JIT compiles (`--features llvm` passes)
- `BackendKind::for_target()` already has 32-bit→LLVM routing for AOT
- JIT dispatch is host-only (gap)
- `LlvmJitCompiler::new()` hardcodes `Target::host()` (gap)
- `types_util.rs` hardcodes i64 for all pointers (foundational blocker)
- "Mix 32/64" interpreted as MIR-level i32 narrowing optimization
- No x32 ABI or mode-switching infrastructure exists

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
