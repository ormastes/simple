# BUG-XC-BAREMETAL-SHARED-DIAG: --emit-shared for a -none- target fails inside lld-link instead of being rejected

- Status: open
- Found: 2026-10-27 (cross-compile matrix lane)
- Spec: riscv_baremetal_cross_spec.spl (dylib rows)

Evidence binary: C:/dev/p3new/stage2.exe copied to C:/dev/xc/simple_xc.exe (phase-3 stage2, 2026-10-27), Windows 11 x86_64 host, clang/lld 23 (C:/msys64/clang64) + llvm-mingw 20260922 UCRT. Matrix: doc/03_plan/compiler/cross_compile_matrix_plan.md.

## Symptom
`--emit-shared --target riscv64-unknown-none-elf` fails with the lld-link /DSPL_SHARED_LIBRARY error. Bare metal has no dynamic loader, so the driver should refuse up front with a clear diagnostic.

## Cause / location
native-build output-kind admission (src/app/cli/native_build_output_plan.spl) does not check the target OS.

## Fix direction
Reject shared output for *-none*/*-elf bare-metal triples: `shared libraries are unsupported for bare-metal target <t>`.
