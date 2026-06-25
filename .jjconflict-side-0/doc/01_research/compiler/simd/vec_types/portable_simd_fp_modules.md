<!-- codex-research -->
# Local Research: portable_simd_fp_modules

## Existing Seams

- `src/compiler/30.types/simd_platform.spl` already models runtime SIMD detection for x86 SSE/AVX/AVX2/AVX-512 and ARM NEON/SVE.
- `src/compiler/50.mir/mir_types.spl` already carries fixed-width vector types: `Vec4f`, `Vec8f`, `Vec4d`, `Vec4i`, `Vec8i`.
- `src/compiler/50.mir/mir_instructions.spl` already reserves SIMD MIR instructions around 128-bit and 256-bit vector operations.
- `src/compiler/70.backend/target_presets.spl` already tracks coarse target FP availability through `float_support`.
- `src/compiler/70.backend/backend/riscv_target.spl` already models RISC-V Linux and bare-metal targets with `+f`/`+d` features and `lp64d`/`ilp32d` ABIs for the current RV64/RV32 contracts.
- `src/compiler/70.backend/backend/native/x86_64_simd.spl` already contains AVX2/SSE encoding helpers for packed f32, f64, and i32 operations.
- `src/compiler/70.backend/backend/native/isel_x86_64.spl` and `src/compiler/70.backend/backend/native/isel_riscv64.spl` currently lower scalar integer-heavy MIR; neither exposes a modular numeric-lowering registry yet.

## Constraints Found

- Current MIR vector types are fixed-width and AVX/SSE-shaped; there is no scalable-vector representation for RVV/SVE-style `vscale` semantics.
- Target presets do not currently expose numeric capability families such as `has_riscv_f`, `has_riscv_d`, `has_riscv_v`, `has_avx`, or `has_avx2`.
- Generic `x86_64` presets cannot safely assume AVX/AVX2 at compile time; runtime or host-feature probing is still required.
- RISC-V presets can express scalar FP intent today through `arch`/`abi` conventions (`rv64gc`, `lp64d`) but do not yet represent `V`.
- Existing SIMD codegen is backend-specific; removing one lowering path would currently risk ad hoc coupling because there is no central registry for feature-family enablement.

## Repo Direction

- The safest phase-1 change is a capability and lowering-selection layer that sits above existing target presets and below backend-specific SIMD/FP implementations.
- Phase 1 should treat:
  - `scalar_fp` as portable scalar `f32`/`f64`,
  - `vector_simd` as fixed-width portable vectors,
  - `target_lowering` as pluggable backend modules such as `x86_avx`, `riscv_fd`, `riscv_v`, and `scalar_fallback`.
- Full RVV-native scalable vectors should remain phase 2 unless MIR and backend IR gain scalable-vector support.

## Implementation Fit

- A new backend module can derive portable numeric capabilities from `TargetPreset` without changing the `TargetPreset` struct shape.
- That module can be exported through `src/compiler/70.backend/__init__.spl` and covered with a compiled unit test that exercises real imports through `bin/simple run`.
- This preserves add/remove ease while creating a stable place for later ISel and LLVM lowering integration.
