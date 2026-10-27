# BUG-XC-CPU-FLAG-IGNORED: native-build --cpu=<level> is accepted and ignored; --cpu <level> fails admission

- Status: open
- Found: 2026-10-27 (cross-compile matrix lane)
- Spec: x86_64_v4_cross_spec.spl

Evidence binary: C:/dev/p3new/stage2.exe copied to C:/dev/xc/simple_xc.exe (phase-3 stage2, 2026-10-27), Windows 11 x86_64 host, clang/lld 23 (C:/msys64/clang64) + llvm-mingw 20260922 UCRT. Matrix: doc/03_plan/compiler/cross_compile_matrix_plan.md.

## Symptom
`SIMPLE_NATIVE_CPU=x86-64-v4` on `a << b` emits `shlx` (BMI2, so the level reaches LLVM); `--cpu=x86-64-v4` emits baseline `shlq` (byte-identical object to x86-64). `--cpu x86-64-v4` (space form) fails with `SCV-E-ADMISSION: source-inventory-scope-unsupported`.

## Cause / location
src/app/cli/bootstrap_main.spl:665 and native_build_output_plan.spl:17 only skip `--cpu` as a value flag; nothing maps it to SIMPLE_NATIVE_CPU / target_cpu. environment_variant_policy_sources_v1.spl records it as policy only. Coordinate with the SIMD tier lane (owns --cpu-tier; canonical names x86-64, x86-64-v2/v3/v4).

## Fix direction
Map --cpu (both forms) onto the same target_cpu input SIMPLE_NATIVE_CPU feeds, and keep it in the cache key.
