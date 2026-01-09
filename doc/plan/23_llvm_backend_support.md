# Plan 23: LLVM Backend for 64-bit and 32-bit Targets

## Goal
- Add an LLVM-based backend to cover 32-bit architectures (per TODO.md) and provide an optional 64-bit alternative, while keeping the existing Cranelift path for fast builds.
- Share outlining/generator logic and runtime FFI specs with current backends to avoid duplication, and expose a common backend interface so the pipeline/driver can choose Cranelift or LLVM transparently.

## Context
- Current codegen uses Cranelift AOT (`codegen/cranelift.rs`) and JIT (`codegen/jit.rs`) built on shared MIR lowering (`codegen/common_backend.rs`, `instr.rs`, `shared.rs`, `runtime_ffi.rs`, `types_util.rs`).
- TODO.md calls out 32-bit support as deferred until an LLVM backend exists; research doc recommends LLVM for 32-bit coverage.
- `simple_common::target` already models 32-bit arches (x86, armv7, riscv32) but Cranelift cannot emit them; loader validation currently assumes 64-bit-only compilation.

## Constraints and Principles
- Minimize duplication: reuse existing MIR transforms (`expand_with_outlined`, generator lowering), runtime FFI specs, and type layout helpers. Avoid forking instruction semantics between backends.
- Provide a common backend abstraction so the pipeline and driver code paths stay unified; keep existing public APIs working (Codegen/JitCompiler) while adding LLVM as a selectable backend.
- Keep SMF emission, runtime symbol resolution, and capture layouts consistent across backends.

## Plan
1) Dependencies and scaffolding  
   - Add `inkwell` (llvm18 feature) as an optional dependency plus feature flag(s) to gate LLVM build; document expected LLVM toolchain detection and error messaging when missing.  
   - Wire cargo features so users can build Cranelift-only or LLVM-enabled; keep default build behavior unchanged for hosts without LLVM.

2) Shared backend interface  
   - Introduce a backend trait/facade (e.g., `NativeBackend` or `BackendKind`) that exposes the operations the pipeline needs: compile MIR → object bytes, (optional) JIT entry, target reporting.  
   - Refactor Cranelift AOT/JIT wrappers to implement/use this interface without changing their external constructors.  
   - Lift runtime FFI signature specs to a backend-agnostic representation so both Cranelift and LLVM declare the same externs from one source of truth.

3) Reusable MIR preparation  
   - Keep `expand_with_outlined`, generator lowering, and capture metadata fully backend-agnostic; expose any missing metadata needed for LLVM (frame slot counts, live-ins, body names).  
   - Add target-pointer-size helpers (from `simple_common::target`) to drive layout-sensitive code paths (struct/closure layouts) for both backends.

4) LLVM backend implementation (AOT first)  
   - Create `codegen/llvm.rs` (and helpers) that lower MIR to LLVM IR via Inkwell: type mapping (TypeId → LLVM types), function signatures, blocks, and instruction coverage matching `instr.rs` semantics.  
   - Declare runtime FFI functions from shared specs; ensure capture buffers, generator frames, and async/actor/future bodies use the same layouts/ordering as Cranelift.  
   - Emit object code for selected target triples (32-bit and 64-bit) and surface errors when the target lacks an LLVM triple or toolchain support.  
   - (Follow-up hook) Sketch JIT support via ORC/MCJIT as a later phase once AOT parity is stable.

5) Pipeline and driver integration  
   - Update `pipeline.rs`/`exec_core.rs` backend selection: default to Cranelift for 64-bit, automatically choose LLVM for 32-bit targets (with a flag/env to force either backend on 64-bit).  
   - Ensure SMF extraction handles LLVM-produced objects (section names/relocs) and that loader/arch validation allows 32-bit modules when built with LLVM.  
   - Thread backend selection through CLI/config without breaking current APIs/tests.

6) Testing and validation  
   - Unit tests: LLVM type mapping, runtime FFI declaration parity with Cranelift, basic function compile on host.  
   - Cross-target smoke tests generating objects for i686/armv7/riscv32 and verifying SMF headers/entry resolution (no execution needed on host).  
   - Parity tests: reuse existing MIR fixtures (e.g., generator/async/collections) to compare LLVM vs interpreter results; add a small end-to-end compile/run on a 64-bit host to catch regressions.  
   - CI guards to skip LLVM-specific tests when the toolchain is unavailable but keep Cranelift coverage intact.

## Risks and follow-ups
- LLVM toolchain availability and version drift; need clear build errors and docs.  
- Performance differences (compile-time and runtime); may require opt-level knobs and benchmarking.  
- Deferred work: LLVM JIT parity, SIMD intrinsic coverage, and deeper optimization passes once AOT parity is stable.
