<!-- codex-design -->
# Agent Tasks: portable_simd_fp_modules

## Current Status (2026-05-01)

- Startup/RSS evidence: PASS (`doc/09_report/verify/simd_startup_rss_evidence_2026-04-30.md`).
- Runtime perf evidence: WARN (`doc/09_report/verify/simd_runtime_perf_evidence_2026-04-30.md`).
- FR `simd_int_intrinsics_for_crypto_2026-05-01` Phase 1 IN PROGRESS (separate sstack agent — adds 10 bitwise/shift int intrinsics).

## Assumed Selection

Use Feature Option B and NFR Option B from the supplied plan.

## P0: Capability Registry

- Add a backend module that derives portable numeric capability facts from `TargetPreset`.
- Keep the surface architecture-neutral and family-oriented.
- Encode x86 runtime-probe requirements explicitly instead of assuming AVX from the generic preset.

## P0: Lowering Selection

- Add lowering-module selection for `scalar_fallback`, `x86_avx`, `riscv_fd`, and `riscv_v`.
- Ensure `scalar_fp`, `vector_simd`, and `target_lowering` are independently toggleable.
- Emit diagnostics when a requested family is unavailable.

## P1: Verification

- Add a compiled unit test that imports the real backend modules through `bin/simple run`.
- Cover x86_64, RV64 Linux, scalar-only RV64 Linux, and RV32 bare-metal integer-only cases.

## P2: Follow-On Work

- Integrate the registry into native and LLVM lowering entry points.
- Add scalable-vector MIR support before claiming RVV-native vector semantics.
