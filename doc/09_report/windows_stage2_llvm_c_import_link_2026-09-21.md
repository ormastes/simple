# Windows Stage2 LLVM C import link probe

- Base: PR #1258 head `9eb6e06aebdb1935294df08e3fe599e9e852a5e9`.
- Failure: strict Stage2 `native-build` reached `lld-link`, which reported 20 distinct unresolved `LLVM*` symbols from `simple_native_all.lib`, including `LLVMAddGlobalInAddressSpace` and `LLVMBuildIntToPtr`. Source log: `D:/wk-stage3-entry-budget/.simple/storage/build/bootstrap/logs/x86_64-pc-windows-msvc/stage2-native-build.log`.
- Selected package: `LLVM_SYS_231_PREFIX=C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`; `llvm-config --version` returned `23.1.1`. The Stage2 command transcript pins this prefix and puts its `bin` directory on `PATH`. The bootstrap authority records the exact import-library and DLL hashes.
- Import library: `lib/LLVM-C.lib`, SHA-256 `f8b52031f1e5b547bb94c7ef7d6a0b00893bcde5ea72cc7bc124ab934d2acad6`.
- Runtime DLL: `bin/LLVM-C.dll`, SHA-256 `1286e894afc98486963246a3f786459b63efb8bd3e4a00193530013fe46aa1fe`.
- The import library defines all 20 logged missing `LLVM*` symbols according to `llvm-nm`; `llvm-readobj --coff-exports` confirms both representative symbols in the DLL. The package is dynamic on Windows: the `.lib` resolves link-time imports, and `LLVM-C.dll` must remain available at runtime. Stage2's admitted `PATH` provides it.

## Bounded link probe

A C-only object calling `LLVMAddGlobalInAddressSpace` and `LLVMBuildIntToPtr` was compiled with LLVM 23.1.1 `clang-cl.exe`. `clang-cl -###` showed the selected `lld-link` and the explicit `LLVM-C.lib` argument. Direct `lld-link` calls used `/NODEFAULTLIB /ENTRY:main /SUBSYSTEM:CONSOLE`; the only changed argument was the import-library path.

| Probe | Exit | Wall time | Sampled peak RSS | Result |
| --- | ---: | ---: | ---: | --- |
| RED, no import library | 1 | 35 ms | 12.8 MB | Both LLVM symbols unresolved |
| GREEN, selected import library | 0 | 36 ms | 20.3 MB | Executable linked |

Probe source, command arguments, and output are retained locally at `D:/wk-stage2-llvm-c-link/.simple/llvm-c-link-probe/`. The probe calls LLVM with null handles and is link-only; its executable was not run. These small-link timings and RSS samples do not establish Stage2 bootstrap performance.

Focused Rust test attempt: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler --release --features llvm --lib llvm_c_import_uses_selected_prefix_and_requires_runtime_dll -- --exact` stopped during dependency resolution because locked `inkwell 0.9.0` lacks the existing manifest's `llvm23-1-force-static` feature. No test binary ran. Full bootstrap remains on hold for review.
