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
- Native project object-cache bypass now detects likely real inline-assembly sidecars instead of rejecting any source text that merely mentions `asm`.
- Stripped Windows native links normalize PE `TimeDateStamp` and `CheckSum` fields after linking so repeated release-like builds hash reproducibly.
- After rebasing onto the current Windows-valid tree, the Cranelift adapter imports and annotates `GemmAddFusion` explicitly at the `detect_gemm_add_pair(...).unwrap()` use site, clearing the current `ANY.dest` native HIR failure.
- Windows safe-mode test child processes now clear `_SIMPLE_STACK_SET` before spawning `simple run <spec>`, so each child re-enters the 64 MB stack trampoline instead of inheriting the parent's marker and running on the default Windows stack.

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
- After syncing to `c1d1cddd7119`, full bootstrap reached all three Windows stages but still exposed a deterministic hash mismatch:
  - Command: `src\compiler_rust\target\debug\simple.exe build bootstrap --seed=src\compiler_rust\target\debug\simple.exe --output=build\windows-hardening\bootstrap\simple-build-strip2`
  - Stage 1: `77 compiled, 895 cached, 0 failed`, `77374976` bytes.
  - Stage 2: `77 compiled, 895 cached, 0 failed`, `77374976` bytes.
  - Stage 3: `77 compiled, 895 cached, 0 failed`, `77378048` bytes.
  - Result: `Bootstrap MISMATCH: outputs differ between stages`.
- Repeated direct stripped native-build reproduced that pre-fix mismatch:
  - `native-strip-det1.exe`: `77374464` bytes, SHA256 `224231619fdb0c5481b17e3db53db3f7c4892469ff2db23c0eb5d11dc43a6557`.
  - `native-strip-det2.exe`: `77378048` bytes, SHA256 `64edd5edb5fe1f95dcd8124e58e346869501b53fe04ccca82acf4bb609032e49`.
- After the inline-assembly cache guard fix and stripped PE metadata normalization, repeated direct stripped native-build is reproducible:
  - Command: `src\compiler_rust\target\debug\simple.exe native-build --source src\compiler --source src\lib --source src\app --entry src\app\cli\main.spl --entry-closure --strip --threads 1 --timeout 180`
  - `native-pe-normal1.exe`: `77390336` bytes, SHA256 `07048667d367af87d55710bcdf092392541d9d95bd8592960612879bb7bc6f7a`.
  - `native-pe-normal2.exe`: `77390336` bytes, SHA256 `07048667d367af87d55710bcdf092392541d9d95bd8592960612879bb7bc6f7a`.
- Full Windows bootstrap now verifies all three stages:
  - Command: `src\compiler_rust\target\debug\simple.exe build bootstrap --seed=src\compiler_rust\target\debug\simple.exe --output=build\windows-hardening\bootstrap\simple-build-normalized`
  - Stage 1: `2 compiled, 971 cached, 0 failed`, `77390336` bytes, SHA256 `07048667d367af87d55710bcdf092392541d9d95bd8592960612879bb7bc6f7a`.
  - Stage 2: `2 compiled, 971 cached, 0 failed`, `77390336` bytes, SHA256 `07048667d367af87d55710bcdf092392541d9d95bd8592960612879bb7bc6f7a`.
  - Stage 3: `2 compiled, 971 cached, 0 failed`, `77390336` bytes, SHA256 `07048667d367af87d55710bcdf092392541d9d95bd8592960612879bb7bc6f7a`.
  - Result: `Bootstrap VERIFIED: All 3 stages produce identical output`.
- After removing the Windows-invalid `:memory:` path from the remote tree and rebasing this slice onto `0985afca`, the current full bootstrap also verifies:
  - Command: `src\compiler_rust\target\debug\simple.exe build bootstrap --seed=src\compiler_rust\target\debug\simple.exe --output=build\windows-hardening\bootstrap\simple-build-current3`
  - Stage 1: `3 compiled, 970 cached, 0 failed`, `77392384` bytes, SHA256 `d2ce615c216818df0eafa5438b7891d8aa82fafa425d7f9343cf9082785186ca`.
  - Stage 2: `2 compiled, 971 cached, 0 failed`, `77392384` bytes, SHA256 `d2ce615c216818df0eafa5438b7891d8aa82fafa425d7f9343cf9082785186ca`.
  - Stage 3: `2 compiled, 971 cached, 0 failed`, `77392384` bytes, SHA256 `d2ce615c216818df0eafa5438b7891d8aa82fafa425d7f9343cf9082785186ca`.
  - Result: `Bootstrap VERIFIED: All 3 stages produce identical output`.

## Remaining Bootstrap Blockers

- Full `simple build bootstrap` now passes the Windows three-stage deterministic hash comparison.
- Full compiler native-build still relies on 959 generated stub symbols on the current rebased tree. The next bootstrap slice should reduce internal stubs before treating the native compiler lane as production-clean.

## Whole-Test Gate

- Initial broad command: `src\compiler_rust\target\debug\simple.exe test --fail-fast`
  - Stopped manually after hundreds of failures because parallel execution did not stop on the first failure.
  - Representative artifacts showed specs passing their examples and then child processes ending with `thread 'main' has overflowed its stack`.
- Fixed the safe-mode child stack marker inheritance and rebuilt `simple-driver`.
- Representative uncached reruns now pass:
  - `simple.exe test test\unit\app\branch_coverage_8_spec.spl --fail-fast --no-cache`
  - `simple.exe test test\feature\usage\di_lock_feature_spec.spl --fail-fast --no-cache`
- Follow-up broad command: `src\compiler_rust\target\debug\simple.exe test --fail-fast --no-cache`
  - Stopped manually after the failure profile changed to real test failures rather than stack overflows.
  - Current first failure classes include code-quality CLI expectation failures, type-inference substitution behavior, AOP pointcut matching, Windows/Wine kernel32 expectations, WebGPU/DXVK availability, and several hardware/QEMU preflight specs.
  - `--fail-fast` does not currently stop already scheduled parallel safe-mode tests, so isolated reruns are required for actionable triage.
