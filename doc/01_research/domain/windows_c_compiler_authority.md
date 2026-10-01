# Windows C authority references

The official LLVM23.1.1 release publishes the Windows x86_64 MSVC archive and its SHA-256. The companion Windows workflow pins that asset and verifies the digest before extraction: https://github.com/llvm/llvm-project/releases/tag/llvmorg-23.1.1 .

Cargo's target linker setting selects the linker supplied to rustc. It is distinct from the C compiler consumed by runtime build scripts: https://doc.rust-lang.org/cargo/reference/config.html#targettriplelinker .

The Rust MSVC target uses the MSVC ABI and requires the Windows native link environment: https://doc.rust-lang.org/rustc/platform-support/windows-msvc.html .
