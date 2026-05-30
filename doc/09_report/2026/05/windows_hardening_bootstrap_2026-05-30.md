# Windows Bootstrap Hardening Report - 2026-05-30

## Scope

Bootstrap/native-build hardening on Windows after MCP, SPipe, and Vulkan fixes.

## Fixes Applied

- `simple build bootstrap` now recognizes `.exe` Rust seed paths.
- Bootstrap child compilers clear `_SIMPLE_STACK_SET` so the Rust driver restores its large-stack worker thread.
- Bootstrap native-build stages use `--threads 1 --timeout 180` to avoid uncontrolled process fan-out on Windows.
- Bootstrap output hashes are computed in Rust instead of shelling out to `sha256sum`.
- MinGW native project links now use `windows_mingw()` link libraries and avoid unavailable `vcruntime`.
- Windows runtime C fixes:
  - `pread`/`pwrite` replaced with `_lseeki64` + `read`/`write`.
  - `mkdir(path, 0777)` replaced with `mkdir(path)` on Windows.
  - `posix_memalign` replaced with `_aligned_malloc/_aligned_free` for hosted DMA fallback.
  - `memmem` replaced with a portable scalar search fallback.
- Windows system-symbol filtering covers CRT/math/WinAPI symbols without classifying Simple symbols such as `Copy` as system APIs.
- Empty Windows stub generation now uses the detected C compiler instead of hardcoded `clang`.
- PE/COFF vtable data is emitted as explicit zero bytes before relocations, avoiding relocations in contentless `.bss`.
- UI access files were updated to current struct fields so native-build no longer skips those modules.
- Added `test/smoke/windows_native_hello.spl` as a minimal native Windows executable smoke.

## Verified

- `cargo build --manifest-path src\compiler_rust\Cargo.toml -p simple-driver --bin simple` passes.
- `simple.exe check` passes for updated UI access files.
- `simple.exe native-build --source test\smoke --entry test\smoke\windows_native_hello.spl --entry-closure --threads 1 --timeout 20` builds.
- `build\windows-hardening\bootstrap\windows_native_hello.exe` prints `windows native hello` and exits `0`.
- `cargo build --manifest-path src\compiler_rust\Cargo.toml -p simple-native-all --target x86_64-pc-windows-gnu` passes.

## Remaining Bootstrap Blockers

- Full `simple build bootstrap` still does not complete on Windows.
- Incremental full compiler native-build reaches link, but 12 files still fail HIR lowering and the linker receives hundreds of Simple stub symbols.
- A clean full compiler native-build exceeded the local command timeout and needs either more time or finer-grained cache/progress diagnostics.
- Current failing HIR files include:
  - `src/app/cli/theme_sync.spl`
  - `src/app/io/cli_commands_part1.spl`
  - `src/app/ui.web/taskbar_runtime_part1.spl`
  - `src/app/ui.web/tls_serve_loop.spl`
  - `src/compiler/90.tools/fix/main.spl`
  - `src/compiler/90.tools/lint/main_part4.spl`
  - `src/lib/common/json/builder.spl`
  - `src/lib/common/privilege/authority_token.spl`
  - `src/lib/common/ui/ios_css.spl`
  - `src/lib/nogc_async_mut/database/test.spl`
  - `src/lib/nogc_sync_mut/simd/wave2_dispatch.spl`
  - `src/os/services/vfs/vfs_service.spl`

