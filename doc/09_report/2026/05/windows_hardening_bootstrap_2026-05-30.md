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
- Native HIR hardening cleared the Windows full compiler native-build skip list by adding missing token metadata fields, replacing stale SIMD lane-field access with current `FixedVec` constructors/accessors, and adding explicit imported-type annotations where the native pass previously saw `ANY`.
- Windows native-build stub filtering now treats additional WinAPI/COM/WSA imports as system symbols and gates `declare_globals` fallback diagnostics behind the existing trace flag.
- `simple build bootstrap` now writes and hashes `simple_stageN.exe` on Windows instead of checking extensionless stage paths.
- Bootstrap Rust-driver stages now pass `native-build --strip` so bootstrap compares release-like Windows executables without COFF symbol tables.
- Native project linking now preserves discovered source order across cached and freshly compiled objects instead of grouping all cache hits before fresh outputs.
- Added an explicit `GemmAddFusion` annotation in the Cranelift adapter so the Windows bootstrap native pass no longer sees the fusion plan as `ANY`.

## Verified

- `cargo build --manifest-path src\compiler_rust\Cargo.toml -p simple-driver --bin simple` passes.
- `simple.exe check` passes for updated UI access files.
- `simple.exe native-build --source test\smoke --entry test\smoke\windows_native_hello.spl --entry-closure --threads 1 --timeout 20` builds.
- `build\windows-hardening\bootstrap\windows_native_hello.exe` prints `windows native hello` and exits `0`.
- `cargo build --manifest-path src\compiler_rust\Cargo.toml -p simple-native-all --target x86_64-pc-windows-gnu` passes.
- After syncing to `fad060e49c87`, full compiler native-build probe:
  - Command: `simple.exe native-build --source src\compiler --source src\lib --source src\app --entry src\app\cli\main.spl --entry-closure --threads 1 --timeout 45 -o build\windows-hardening\bootstrap\stage_probe_zero_skip.exe --verbose`
  - Result: `Compiled: 970/970 (893 cached, 77 fresh, 0 failed)` and linked `stage_probe_zero_skip.exe`.
  - Stub fallback remains enabled; generated stubs dropped from 1081 in the clean baseline to 957 after this pass.
- After syncing to `c1d1cddd7119`, full bootstrap reaches all three Windows stages:
  - Command: `src\compiler_rust\target\debug\simple.exe build bootstrap --seed=src\compiler_rust\target\debug\simple.exe --output=build\windows-hardening\bootstrap\simple-build-strip2`
  - Stage 1: `77 compiled, 895 cached, 0 failed`, `77374976` bytes.
  - Stage 2: `77 compiled, 895 cached, 0 failed`, `77374976` bytes.
  - Stage 3: `77 compiled, 895 cached, 0 failed`, `77378048` bytes.
  - Result: `Bootstrap MISMATCH: outputs differ between stages`.
- Repeated direct stripped native-build still reproduces the mismatch:
  - `native-strip-det1.exe`: `77374464` bytes, SHA256 `224231619fdb0c5481b17e3db53db3f7c4892469ff2db23c0eb5d11dc43a6557`.
  - `native-strip-det2.exe`: `77378048` bytes, SHA256 `64edd5edb5fe1f95dcd8124e58e346869501b53fe04ccca82acf4bb609032e49`.

## Remaining Bootstrap Blockers

- Full `simple build bootstrap` completes all stage compile/link work on Windows, but fails the final deterministic hash comparison.
- The remaining blocker is native output nondeterminism in repeated stripped Windows native-build outputs. PE inspection shows the mismatch is not only timestamp/checksum metadata; `.text` size/content can differ by about 3 KB.
- Full compiler native-build still relies on 957 generated stub symbols. The next bootstrap slice should reduce internal stubs and continue isolating nondeterministic codegen/link inputs.
- A clean full compiler native-build still needs a longer verification pass after the incremental zero-skip and three-stage bootstrap probes.
