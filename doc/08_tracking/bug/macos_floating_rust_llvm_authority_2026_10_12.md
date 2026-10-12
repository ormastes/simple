# macOS floating Rust LLVM authority

Status: OPEN pending native macOS identity and bootstrap execution.

Native macOS run 38152835609 passed Cargo pin-forwarding checks, installed external LLVM/Clang/LLD 23.1.1, then rejected rustc LLVM 23.1.3. Its floating nightly resolved rustc 1.101.0-nightly (6f5da406b 2026-10-10). The exact LLVM guard correctly rejected it.

Fix: pin compiler_rust/rust-toolchain.toml to nightly-2026-09-15 and supply that same explicit toolchain in macos-phase23-evidence.yml. Preserve the exact 23.1.1 guard. The focused policy regression rejects floating explicit nightly and absent explicit toolchain.

Actual local identity: rustc +nightly-2026-09-15 --version --verbose reports 1.100.0-nightly, commit 574ff7d98bd6d037e5236a8453029173b32631fd, commit date 2026-09-14, host x86_64-unknown-linux-gnu, LLVM version 23.1.1. Components rustfmt/clippy installed. This is Linux toolchain identity evidence, not macOS bootstrap PASS.

Upstream authority: https://github.com/rust-lang/rust/commit/b37140eee42b updates LLVM to 23.1.1; exact selected Rust commit references LLVM submodule 1b9c0d5ff9bbe7634aead059efe6b11a7eeba145.

Required remaining verification: native macOS rustc verbose identity and existing exact toolchain gate, then admitted Phase2/3 bootstrap. No bootstrap rerun performed by this repair lane. No LLVM version override or relaxed comparison.
