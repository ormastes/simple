# TODO: seed native-build link step picks MSVC clang for i686 Windows

**Filed:** 2026-11-23 | **Area:** compiler/linker (seed native_project) | **Type:** toolchain selection
**Status:** OPEN

## Gap
`simple native-build --target i686-pc-windows-gnu` compiles objects, but its
own link step uses the llvm-msvc clang that the Windows LLVM activation
(`~/.simple/toolchains/activation/windows-llvm-23.1.1.shs`) puts first on PATH.
That toolchain has no i686 `libclang_rt.builtins`, so every i686 link fails
there.

## Workaround in use
Both i686 lanes (lld and Pure Simple linker) export
`CC=$HOME/.simple/toolchains/llvm-mingw-*-ucrt-x86_64/bin/i686-w64-mingw32-clang.exe`
and put that `bin` first on PATH before native-build, or link the kept
objects by hand.

## Fix
For a `*-windows-gnu` target, pick the llvm-mingw `<triple>-clang` driver
(matching the target arch) over a PATH clang, and never an MSVC-flavoured
driver. Same root as
`doc/08_tracking/bug/windows_llvm_activation_msvc_clang_shadows_llvm_mingw_i686_2026-11-22.md`,
which is about the activation script ordering; this item is about the seed's
selection not checking the target's environment.

## Acceptance
`native-build --target i686-pc-windows-gnu` links hello with no `CC`
override in a shell where the activation script has run.
