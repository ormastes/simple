# BUG-XC-CROSS-EXE-LINK: native-build refuses every cross-target executable on a Windows host

- Status: open
- Found: 2026-10-27 (cross-compile matrix lane)
- Spec: test/02_integration/compiler/cross/*_cross_spec.spl (exe rows)

Evidence binary: C:/dev/p3new/stage2.exe copied to C:/dev/xc/simple_xc.exe (phase-3 stage2, 2026-10-27), Windows 11 x86_64 host, clang/lld 23 (C:/msys64/clang64) + llvm-mingw 20260922 UCRT. Matrix: doc/03_plan/compiler/cross_compile_matrix_plan.md.

## Symptom
`native-build hello.spl --target aarch64-pc-windows-gnu -o x.exe` -> `LLVM native linking failed: host C runtime/entry compilation unsupported: target 'aarch64-pc-windows-gnu' on host 'x86_64-windows'`. Same for i686-pc-windows-gnu, i686-unknown-linux-gnu, riscv64-unknown-none-elf, riscv64-unknown-simpleos. Objects and archives for the same targets build fine.

## Cause / location
`hosted_c_compiler_plan` (src/compiler/70.backend/backend/runtime_compiler.spl:225) only admits cross plans for linux->mingw and linux->aarch64/riscv64, and the linux plans name `aarch64-linux-gnu-gcc` / `riscv64-linux-gnu-gcc` (violates the no-GCC rule). Refusal raised at llvm_native_link_orchestrator.spl:215. riscv64-unknown-none-elf/simpleos also fall to the hosted path because `is_simpleos_riscv64_link` did not claim them.

## Fix direction
Plan cross targets as `clang --target=<triple>` (+ llvm-mingw sysroot for *-w64-mingw32 / *-pc-windows-gnu), cross-compile the C runtime per triple, link with ld.lld/lld-link. Replace the gcc command names with clang --target.
