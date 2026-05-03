# NFR Requirements: SIMD Auto-Application

Date: 2026-05-03

- NFR-001: Compiler correctness shall prefer scalar fallback or no-op matching over unsafe vectorization.
- NFR-002: Elementwise FP rewrites shall not require `fast_math` when they preserve exact scalar semantics.
- NFR-003: Capability selection logic shall be shared and queryable instead of copied into optimization passes.
- NFR-004: New idiom families shall be named centrally in MIR so backend lowering remains consistent across x86, AArch64, and RISC-V.
- NFR-005: Phase-1 changes shall be verifiable with focused compiler/backend unit specs before broader rollout into library kernels.
