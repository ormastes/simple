<!-- codex-design -->
# Architecture: portable_simd_fp_modules

## Boundary

The portable numeric layer sits between coarse target presets and backend-specific FP/SIMD lowering code.

- Target presets remain the stable input contract.
- Portable numeric capability derivation converts preset facts into architecture-neutral feature-family facts.
- Lowering selection maps those facts to backend modules such as `x86_avx`, `riscv_fd`, `riscv_v`, and `scalar_fallback`.
- Backend ISel and encoders remain target-specific implementation details below this boundary.

## Feature Families

- `scalar_fp`: portable scalar `f32`/`f64` capability and diagnostics.
- `vector_simd`: portable fixed-width vector capability.
- `target_lowering`: backend module selection and fallback policy.

Each family must be independently toggleable.

## Target Model

- x86_64:
  - scalar FP is available,
  - portable vectors are allowed,
  - AVX/AVX2 require runtime probing and must not be assumed from the generic preset.
- RISC-V with `F`/`D` and no `V`:
  - scalar FP is available,
  - vector SIMD is unavailable,
  - `riscv_fd` lowering is valid.
- RISC-V with `V`:
  - vector SIMD becomes available,
  - `riscv_v` lowering becomes selectable,
  - full scalable-vector semantics remain gated on later MIR work.

## Phase Split

- Phase 1:
  - capability registry,
  - modular lowering selection,
  - fixed-width portable vector policy,
  - explicit RVV deferral.
- Phase 2:
  - scalable-vector MIR types,
  - RVV-native lowering,
  - broader parity across scalar, fixed-width, and scalable vector codegen paths.
