<!-- codex-design -->
# Agent Tasks: portable_simd_fp_modules

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
