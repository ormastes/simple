# Windows ARM64 llvm-mingw cross-compile configuration gaps

REQ-WIN-ARM64-MINGW-001: `--target aarch64-pc-windows-gnullvm` (and
`aarch64-w64-mingw32`) from a Windows x86_64 host must select the ARM64
llvm-mingw UCRT toolchain end to end and emit an ARM64 PE.

Status: verification-pending (landed fix is not verified by a native run until
the PE check recorded in the PR passes on the deployed seed).

Gaps found at release/1.0.0 (f593c7123ca):

1. `Target::parse` (Rust seed, `common/src/target.rs`) did not set the GNU
   linker flavor for `-gnullvm` / `-mingw32` suffixes and mapped the `w64`
   vendor spelling (`aarch64-w64-mingw32`) to `TargetOS::Any`.
2. `windows_gnu_target_flag` (`native_project/tools.rs`) hardcoded
   `--target=x86_64-w64-windows-gnu`, so every C compile/link step of an
   aarch64 Windows GNU build ran against the x86_64 sysroot. The
   `-print-file-name` library probe in `native_project/linker.rs` had the same
   hardcode.
3. Pure-Simple `hosted_c_target_is_mingw` (`runtime_compiler.spl`) did not
   recognise `-pc-windows-gnullvm`; the Linux->mingw plan and the compile
   `--target` selection only matched `-pc-windows-gnu`.
4. `native_relocatable_link.spl` had no ARM64 COFF branch (`-m arm64pe`,
   `aarch64-w64-mingw32-ld` prefix off Windows).
5. Cranelift AOT used `is_pic=true` for Windows ARM64 and panicked with
   `Aarch64AdrGotPage21 is not supported for this file format` (COFF has no GOT).

6. `src/compiler_rust/lib/build.rs` hardcoded the x86_64 triple for the native
   term library and required the compiler to be exactly `clang`; it now follows
   `CARGO_CFG_TARGET_ARCH` and accepts `<triple>-clang` (llvm-mingw drivers).
7. `check-cross-compile-matrix.shs` `mingw_bin()` only globbed ubuntu llvm-mingw
   directory names; it now also finds `llvm-mingw-*-ucrt-x86_64` (Windows host).

Evidence (Windows host, seed built with
`cargo build --release --bin simple --target x86_64-pc-windows-gnullvm`, llvm-mingw
UCRT clang/lld only): `native-build --target aarch64-pc-windows-gnullvm` on a
hello .spl produced a PE for which `llvm-readobj --file-headers` reports
`Format: COFF-ARM64`, `Arch: aarch64`, `Machine: IMAGE_FILE_MACHINE_ARM64 (0xAA64)`.
Link took 658 s for a 536 KB binary: a perf regression, tracked as remaining work.

Known stale assertion (separate bug):
`hosted_c_target_guard_spec_stale_orchestrator_assertion_2026-11-17.md`.

Tests: `parse_windows_arm64_mingw_triples_select_gnu_flavor`,
`test_windows_gnu_target_flag_follows_target_arch`,
`aot_windows_arm64_is_not_pic` (Rust), and
`plans Windows ARM64 llvm-mingw gnullvm and w64-mingw32 targets`
(`test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl`).
