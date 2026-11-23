# TODO: seed native-build link step picks MSVC clang for i686 Windows

**Filed:** 2026-11-23 | **Area:** compiler/linker (seed native_project) | **Type:** toolchain selection
**Status:** FIXED (Rust unit verified; Windows link runtime pending)

## Gap
`simple native-build --target i686-pc-windows-gnu` compiles objects, but its
own link step uses the llvm-msvc clang that the Windows LLVM activation
(`~/.simple/toolchains/activation/windows-llvm-23.1.1.shs`) puts first on PATH.
That toolchain has no i686 `libclang_rt.builtins`, so every i686 link fails
there.

## Root Cause
1. `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`
   (`target_c_compiler`) short-circuited `TargetOS::Windows && LinkerFlavor::Gnu`
   to bare `"clang"` whenever `CC` was unset instead of delegating to
   `simple_common::platform::cc_detect::detect_c_compiler_for_target`.
2. `src/compiler_rust/common/src/platform/cc_detect.rs` only returned bare
   `<arch>-w64-mingw32-clang` without searching `PATH`, `LLVM_MINGW_ROOT`,
   `SIMPLE_LLVM_MINGW_ROOT`, or `$HOME/.simple/toolchains/llvm-mingw-*/bin`, and
   still fell back to bare `"clang"` on native GNU Windows hosts (allowing an
   MSVC-target `clang` ahead on `PATH` to be selected).
3. `src/compiler_rust/compiler/src/pipeline/native_project/inline_asm_emit.rs`
   (`compile_inline_asm_c` when `target.is_none()`) called `find_c_compiler()`
   instead of `target_c_compiler(effective_target())`.

## Fix Applied
For a `*-windows-gnu` target without explicit `CC`/`CXX`:
- `detect_c_compiler_for_target` / `detect_cxx_compiler_for_target` (and
  `target_c_compiler` / `target_cxx_compiler`) search `PATH`, then
  `LLVM_MINGW_ROOT` / `SIMPLE_LLVM_MINGW_ROOT`, then
  `$HOME/.simple/toolchains/llvm-mingw-*/bin` (newest first) for the
  arch-matching `<arch>-w64-mingw32-clang` (`clang++`).
- Any fallback to plain `clang`/`clang++` skips executables that fail
  `!is_msvc_target(cc)` (via `--print-effective-triple` / `-dumpmachine`) or, on
  generic `PATH`, do not report a `windows-gnu`/`mingw`/`windows-gnullvm`
  triple, and fails closed with `<arch>-w64-mingw32-clang` rather than bare
  `"clang"` (never invoking MSVC-target `clang`).
- `windows_gnu_target_flag` emits `--target=<arch>-w64-windows-gnu` (including
  `armv7`, `aarch64`, `i686`, `x86_64`) for GNU clang drivers (both plain and
  triple-prefixed) while excluding GCC and `clang-cl`/`cl.exe`.

Same related context as
`doc/08_tracking/bug/windows_llvm_activation_msvc_clang_shadows_llvm_mingw_i686_2026-11-22.md`
(no in-repo generator exists for `~/.simple/toolchains/activation/windows-llvm-23.1.1.shs`).

## Acceptance
- Unit tests in `simple-common` (`cc_detect`) and `simple-compiler`
  (`native_project`) pass for `i686-pc-windows-gnu`, `x86_64-pc-windows-gnu`,
  `aarch64-pc-windows-gnu`, and rejecting MSVC-target `clang` ahead of
  `i686-w64-mingw32-clang` on `PATH`.
- `native-build --target i686-pc-windows-gnu` linking hello on Windows with no
  `CC` override in an activated shell: pending Windows host verification.
