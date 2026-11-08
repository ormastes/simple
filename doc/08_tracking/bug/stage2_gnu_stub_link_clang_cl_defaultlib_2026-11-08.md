# gnu stub link: clang-cl stub object embeds /DEFAULTLIB libcmt, oldnames

READY FOR OPUS REVIEW. Severity P2. Status: open.

Repro: any windows-gnu native-build with unresolved rt_* reaching the stub retry (linker.rs ~2752). compile_coff_gc_parity_stubs (native_project/stubs.rs:1805) compiles _gc_parity_stubs.c with clang-cl; the .obj carries /DEFAULTLIB:libcmt and oldnames.
Observed: 'ld.lld: error: could not open liblibcmt.a / liboldnames.a'.
Workaround WA-s2n9: add /Zl to the clang-cl args (uncommitted in stage2-rel). Real fix: land /Zl (or use clang --target gnu) with a spec for the gnu stub path.
