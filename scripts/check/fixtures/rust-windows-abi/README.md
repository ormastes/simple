# Focused Rust Windows ABI regression

Run from the repository root on x86_64-pc-windows-msvc:

```powershell
$env:CARGO_TARGET_DIR = "$PWD/build/rust-windows-abi"
cargo run --locked --manifest-path scripts/check/fixtures/rust-windows-abi/Cargo.toml --bin windows-abi-regression
cargo run --locked --manifest-path scripts/check/fixtures/rust-windows-abi/Cargo.toml --bin windows-runtime-abi-regression
```

Add `--release` for the optimized profile. The fixture denies clashing extern
declarations and links real Windows APIs. It directly includes production
compiler adapters and runtime RSS modules. `build.rs` selects unchanged source
slices of the canonical runtime PTY owner and host wrappers, avoiding unrelated
heap/collection exports. Interpreter value/error transport is narrowed locally;
heap serialization hooks panic if reached. There are no substituted OS APIs.
The two binaries preserve compiler/runtime crate boundaries, since unrelated
private raw extern declarations can differ between these separate crates.

Assertions cover 64-bit SDK layouts; host and process memory; child RSS;
CreateProcessW success, returned handles and exit status; a nonexistent executable
failure; live compiler PTY delegation through ConPTY. This is focused native Rust
ABI evidence, not seed product testing or bootstrap qualification.

At base 576f847f83cd7033a5d687051eb719d9a8f14dec,
`git grep -n 'windows_impl::\|pty::windows_impl' HEAD -- src/compiler_rust/compiler/src`
returned zero references. The deleted compiler `windows_impl` was private and
contained no exports or no_mangle functions. Every live Windows pty_*_impl
already delegated to simple_runtime::value::pty::host_pty_* (seven wrappers).
The fixture compiles those unchanged live adapters and executes their transport.
