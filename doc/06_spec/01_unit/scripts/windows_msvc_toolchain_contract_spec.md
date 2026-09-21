# Windows LLVM23.1 C-only toolchain contract

The executable source is test/01_unit/scripts/windows_msvc_toolchain_contract_spec.spl.

It checks the Windows shell selection and CXX clearing, Cargo's explicit MSVC link.exe with the Windows GNU override absent, and CMake's admitted clang-cl prefix/version validation without C++ configuration.

Executable shell behavior is covered separately by scripts/check/check-windows-msvc-toolchain-contract.shs. Real C/CMake and Rust linker execution use isolated native probes.

Self-hosted SSpec execution and generated-doc verification are pending. This manual records intended assertions and does not claim a generated-doc or SSpec PASS.
