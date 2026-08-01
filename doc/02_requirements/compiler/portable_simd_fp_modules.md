<!-- codex-research -->
# Requirements: portable_simd_fp_modules

## Selected Option

Feature Option B: Portable Scalar FP + Fixed-Width SIMD Modules.

## Requirements

- REQ-PSFM-001: The compiler must represent scalar floating point as an independent feature family named `scalar_fp`.
- REQ-PSFM-002: The compiler must represent portable fixed-width vectors as an independent feature family named `vector_simd`.
- REQ-PSFM-003: The compiler must represent backend selection as a separate feature family named `target_lowering`.
- REQ-PSFM-004: The public capability surface must remain architecture-neutral and must not require users to select an AVX-only or RVV-only API as the primary source interface.
- REQ-PSFM-005: Target capability reporting must expose `has_scalar_fp`, `has_vector_simd`, `has_riscv_f`, `has_riscv_d`, `has_riscv_v`, `has_avx`, and `has_avx2`.
- REQ-PSFM-006: RISC-V targets with `F`/`D` but without `V` must remain eligible for scalar floating-point support.
- REQ-PSFM-007: x86_64 AVX/AVX2 lowering must be modeled as a target-specific lowering module rather than a separate language surface.
- REQ-PSFM-008: The target-lowering family must support at least `scalar_fallback`, `x86_avx`, `riscv_fd`, and `riscv_v` module identifiers.
- REQ-PSFM-009: Phase 1 must keep portable vector types fixed-width and treat RVV-native scalable vectors as deferred work unless MIR gains explicit scalable-vector representation.
- REQ-PSFM-010: Disabling `vector_simd` must not disable `scalar_fp`.
- REQ-PSFM-011: Targets without the requested vector capability must surface an explicit diagnostic or capability result instead of silently pretending support.
