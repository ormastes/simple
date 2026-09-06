# ARM32 + JIT + Metal: Architectural Constraints

Date: 2026-05-17
Status: durable — established constraints of the tooling and platform stack

## Summary

You cannot ship Simple with ARM32 JIT or with Metal on ARM32. The constraints
are not bugs to fix — they are upstream platform decisions and CPU silicon
limits. Mixing 32-bit and 64-bit machine code in one process is also not
viable as a workaround.

## Constraint 1 — Cranelift has no ARM32 backend

`vendor/cranelift-codegen/src/isa/mod.rs` ends with:

```rust
pub const ALL_ARCHITECTURES: &[&str] = &["x86_64", "aarch64", "s390x", "riscv64"];
```

The `lookup(triple)` dispatch returns `Err(LookupError::Unsupported)` for any
`Architecture::Arm(...)` triple. There is no armv7 codegen in Cranelift;
upstream has no roadmap to add one.

Simple's JIT is implemented entirely through Cranelift (`src/compiler/95.interp/
execution/tiered_jit.spl` + `src/compiler_rust/compiler/src/codegen/jit.rs`).
Without a Cranelift armv7 backend, Simple cannot JIT on ARM32 regardless of
host OS.

## Constraint 2 — Metal does not run on ARM32

Apple Metal ships only on:
- macOS (Intel x86_64 and Apple Silicon arm64)
- iOS / iPadOS — arm64 only since iPhone 5s (2013)
- tvOS — arm64

Apple has not produced a 32-bit-Metal-capable device or SDK in roughly a
decade. There is no Apple SDK target tuple that combines Metal with armv7;
adding one is not within the project's reach.

## Constraint 3 — Mixing 32-bit and 64-bit machine code in one process

### ARM (AArch32 vs AArch64)

The ARMv8 architecture defines two execution states, but a process runs in
one state for its entire lifetime — pinned at exec time by the kernel.

**Apple Silicon (M1 through M4) lacks AArch32 entirely.** Starting around
the A11 chip, Apple removed the AArch32 execution state from the CPU
silicon. M4 cannot decode or execute armv7 / Thumb opcodes; they trap as
invalid. macOS dropped user-mode 32-bit support in Catalina (2019). There
is no AArch32 shim on Apple Silicon — neither in hardware nor in the OS.

Linux/Android on AArch64-capable CPUs that retain AArch32 support (e.g.,
Cortex-A53/A72/A78 generations) can host mono-ABI AArch32 processes
alongside mono-ABI AArch64 processes, but no process mixes the two.

### x86 (i386 vs x86_64)

Each process runs in one mode. The "Heaven's Gate" trick (far-call to a
64-bit code segment from a 32-bit process via segment-register
manipulation) is a security-flagged anti-pattern, not an engineering
option.

### Implication for Simple JIT

A `JITModule` targets one ISA. An AArch64 Simple binary cannot embed
AArch32 JIT code; the host CPU may not even decode it. Conversely, a
hypothetical AArch32 Simple binary on AArch64 hardware would still have
no JIT backend to call (Constraint 1).

## What ARM32 deployments CAN use

| Path | Status | Notes |
|---|---|---|
| Pure Simple interpreter | works | Same as any other Simple host |
| LLVM AOT codegen | works | Simple's `--features llvm` enables `TargetArch::Arm => "armv7"` in `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs` |
| Cranelift Pulley32 | partial | Portable interpreter-style codegen; not native machine code; modest speedup (~2-5x) over the Simple interpreter |
| Vulkan / OpenGL ES | works | ARM32 Android (since Vulkan 1.0) and Linux armv7 expose Vulkan; ARM32 GLES is universal |
| Metal | impossible | Apple-only and arm64-only |
| Cranelift JIT | impossible | No armv7 backend |

## Recommended directions

1. **ARM32 GPU work**: target Vulkan. `test/05_perf/graphics_2d/bench_2d_vulkan.spl`
   already exists as the reference shape.
2. **ARM32 CPU speed**: build with `--features llvm` on the seed and rely on
   LLVM AOT. There is no JIT path; do not invest in adding one.
3. **Apple GPU work**: arm64 only. The Metal parity work in
   `test/05_perf/graphics_2d/bench_2d_metal_simple.spl` and
   `test/05_perf/graphics_2d/c_reference/bench_2d_metal.m` is the canonical
   measurement surface. See [graphics_backend_acceleration.md](graphics_backend_acceleration.md)
   for the broader plan.

## Why this document exists

These constraints have surfaced repeatedly in plan discussions. Each
investigation re-discovers the same facts. This document captures them
once so future plans for "ARM32 + JIT" or "ARM32 + Metal" can be redirected
to the viable paths above without re-running the diagnostic.
