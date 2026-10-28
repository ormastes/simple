# BUG-XC-SHARED-LINK-DFLAG: --emit-shared passes /DSPL_SHARED_LIBRARY to lld-link and routes every target to the MSVC arm

- Status: open
- Found: 2026-10-27 (cross-compile matrix lane)
- Spec: aarch64_windows / i686 / x86_64_v4 / riscv_simpleos dylib rows

Evidence binary: C:/dev/p3new/stage2.exe copied to C:/dev/xc/simple_xc.exe (phase-3 stage2, 2026-10-27), Windows 11 x86_64 host, clang/lld 23 (C:/msys64/clang64) + llvm-mingw 20260922 UCRT. Matrix: doc/03_plan/compiler/cross_compile_matrix_plan.md.

## Symptom
Every `--emit-shared` on the Windows host fails: `lld-link: error: could not open '/DSPL_SHARED_LIBRARY': No such file or directory`, including ELF targets (riscv*, i686-linux) and *-pc-windows-gnu targets.

## Cause / location
src/compiler/70.backend/linker/_LinkerWrapper/shared_linking.spl:304 pushes the C preprocessor define `/DSPL_SHARED_LIBRARY` into MsvcConfig.extra_args (linker args). Separately, :199 dispatches on `host_os()` instead of the target, so ELF targets on a Windows host take `_link_shared_windows`, and the gnu flavor is not selected for *-pc-windows-gnu (target triple not reaching `windows_link_flavor_for_config`).

## Fix direction
Drop the define from the link args (it belongs on the runtime compile, where :221/:372 already add it); dispatch on the target triple's OS. Backend-dylib lane (plugin loading) owns provider/plugin gaps, not this.
