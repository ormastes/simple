# BUG-XC-HOST-GNU-LINK: host x86_64-pc-windows-gnu exe link fails with llvm-mingw

- Status: open
- Found: 2026-10-27 (cross-compile matrix lane)
- Spec: x86_64_v4_cross_spec.spl (exe row)

Evidence binary: C:/dev/p3new/stage2.exe copied to C:/dev/xc/simple_xc.exe (phase-3 stage2, 2026-10-27), Windows 11 x86_64 host, clang/lld 23 (C:/msys64/clang64) + llvm-mingw 20260922 UCRT. Matrix: doc/03_plan/compiler/cross_compile_matrix_plan.md.

## Symptom
No CC: `Windows GNU linking requires bootstrap-owned clang through CC`. CC=llvm-mingw clang.exe: `ld.lld: error: could not open 'liboldnames.a'`. CC=x86_64-w64-mingw32-clang.exe: back to the CC-admission error. (CC=C:/msys64/clang64/bin/clang.exe: not present on this host.)

## Cause / location
Windows GNU link admission in the LLVM native link path accepts only a specific clang identity and doesn't pass the llvm-mingw sysroot/lib dir.

## Fix direction
Admit llvm-mingw's triple-prefixed clang (the repo's default Windows toolchain) or pass --sysroot/-L for plain clang.
