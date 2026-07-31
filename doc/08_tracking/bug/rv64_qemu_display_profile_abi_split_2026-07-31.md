# RV64 QEMU display scenario selects the legacy soft profile (2026-07-31)

## Status

Open.  This is a profile-selection and ABI-propagation bug, not evidence that
the current `riscv64-unknown-none` lane is invalid.

## Problem

The canonical QEMU host-GPU/display scenario still builds its `riscv64` guest
as `riscv64-unknown-none` in
`scripts/check/check-simpleos-qemu-host-gpu-2d.shs:2556-2565`.  That is the
legacy bare-metal/soft-float target, while the QEMU desktop profile already
declares `riscv64gc-unknown-simpleos`, `rv64gc`, and `lp64d` in
`src/os/kernel/arch/riscv64/platform/boot_profile.spl:55-82`.

These are two related observations, not one build path.  The host-GPU script
currently invokes the Cranelift backend, so it demonstrates the stale
target-selection contract only.  Separately, Stage2/RV64 LLVM attempt 32
emitted soft-ABI ELF objects (`e_flags=0x1`, RVC) and ran through the Rust
native-project linker.  That linker hard-codes LP64D auxiliary objects in
`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:925-962`.
The active pure-Simple `link_simpleos_riscv64()` has the same propagation bug:
it compiles the entry shim, module-init caller, stubs, and freestanding runtime
with `-march=rv64gc -mabi=lp64d` in
`src/compiler/70.backend/backend/llvm_native_link.spl:1997-2065`.  A final link
must not combine those object ABIs.

## Affected source and tests

- `scripts/check/check-simpleos-qemu-host-gpu-2d.shs` — the QEMU display
  scenario chooses the obsolete target.
- `src/compiler/70.backend/backend/llvm_native_link.spl` — RV64 link support
  hard-codes LP64D instead of receiving ABI/ISA from the selected LLVM target.
- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` — the
  bootstrap linker used by attempt 32 independently hard-codes LP64D for its
  RV64 auxiliary objects.
- `src/os/kernel/arch/riscv64/platform/boot_profile.spl` — already contains
  the intended QEMU desktop profile and is the contract the scenario must use.
- `test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl` — add
  source-contract assertions for the profile-specific RV64 linker arguments.
- `test/03_system/os/multiarch/six_arch_boot_spec.spl` and
  `test/03_system/check/cpu_simd_engine2d_simple_bin_spec.spl` — extend the
  QEMU-display acceptance path rather than treating generic boot evidence as
  display-profile evidence.

## Required fix

Split the RV64 target contract into two explicit profiles:

1. Keep `riscv64-unknown-none` / `rv64imac` / `lp64` for minimal bare-metal
   probes and for the current, still-unaccepted LLVM evidence lane while its
   soft closure is made internally consistent.
2. Route the canonical QEMU desktop/display scenario through
   `riscv64gc-unknown-simpleos` / `rv64gc` / `lp64d`.

Propagate the selected profile from LLVM target selection through both the
bootstrap Rust linker and the active pure-Simple linker into every RV64
native-link input: emitted LLVM object target/data layout, entry assembly,
freestanding runtime, generated module-init caller, C stubs, and final linker
arguments.  Do not infer the ABI from an output filename and do not silently
coerce a soft object into LP64D at link time.

## Acceptance checks

- A unit/source-contract test proves each profile maps to its own triple,
  `-march`, and `-mabi`, and that `link_simpleos_riscv64()` consumes that
  contract for all auxiliary objects.
- The Cranelift host-GPU QEMU scenario builds the desktop guest with
  `riscv64gc-unknown-simpleos` rather than the legacy bare-metal selector.
- A separate LLVM desktop/display build reports a consistent hard-float ABI
  across emitted LLVM and auxiliary objects via `readelf -h`.
- The existing minimal `riscv64-unknown-none` QEMU/probe checks remain soft
  ABI and pass without gaining desktop-only dependencies.
- The QEMU display smoke reaches its existing render/exit oracle using the
  canonical Web/GUI DrawIR path, not a private fallback renderer.

## Current goal boundary

The shared multilingual GPU-font goal's current Stage2 artifact and RV64 LLVM
objects are valid soft-ABI inputs, but the goal is not accepted or complete:
its closure still mixes LP64D auxiliary inputs and has unresolved real
freestanding symbols.  The immediate work must first produce an internally
consistent LP64 closure and pass its evidence gate.  Switching that evidence
lane to the desktop hard-float profile before the profile split would conflate
two failures and invalidate the reproducible current lane.
