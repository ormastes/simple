# gnu stub link: clang-cl stub object embeds /DEFAULTLIB libcmt, oldnames

READY FOR OPUS REVIEW. Severity P2. Status: fix-implemented-verification-pending.

Repro: any windows-gnu native-build with unresolved rt_* reaching the stub retry (linker.rs ~2752). compile_coff_gc_parity_stubs (native_project/stubs.rs:1805) compiles _gc_parity_stubs.c with clang-cl; the .obj carries /DEFAULTLIB:libcmt and oldnames.
Observed: 'ld.lld: error: could not open liblibcmt.a / liboldnames.a'.
Workaround WA-s2n9: add /Zl to the clang-cl args (uncommitted in stage2-rel). Real fix: land /Zl (or use clang --target gnu) with a spec for the gnu stub path.

## Fix (2026-11-09, PR work/gnu-link-gc-parity)

`compile_coff_gc_parity_stubs` now takes a `CoffStubToolchain`: `Msvc` keeps
clang-cl; `Gnu` compiles `_gc_parity_stubs.c` with the lane's own clang
(`--target=x86_64-w64-windows-gnu -c -O1 -ffunction-sections -fdata-sections
-fno-stack-protector -fno-asynchronous-unwind-tables`). No `/DEFAULTLIB`
directive and no `__security_check_cookie` can appear, so `/Zl` and `/GS-`
(WA-s2n9, WA-s2n9b) are unnecessary. Unit test
`gnu_parity_stubs_compile_with_gnu_clang_not_clang_cl` pins the arg spelling.
