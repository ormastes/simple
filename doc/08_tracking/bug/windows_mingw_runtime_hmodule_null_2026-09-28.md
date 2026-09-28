# Windows MinGW seed runtime rejects HMODULE null comparison

- Status: FIXED pending protected integration
- Date: 2026-09-28
- Severity: RC Windows bootstrap blocker
- Source: `release/1.0` PR #2021 CI, Build Binaries (Linux + MinGW), run `36406269411`

The Windows MinGW seed failed before producing an artifact because
`GetModuleHandleW` now yields an `HMODULE` pointer while
`spl_dlsym_process_checked` compared it with integer `0` at
`src/compiler_rust/runtime/src/value/wsffi_native.rs:286`. The compiler
reported `expected *mut c_void, found usize`. This is a target-specific Rust
runtime type error; no pure-Simple call path can correct it. The adjacent
Windows process loader in `src/compiler_rust/runtime/src/loader/settlement/native.rs`
already uses `handle.is_null()` for the same API return type.

The repair uses `process.is_null()` and retains the existing status `3` and
zeroed output on failure. A local exact-target `cargo check -p simple-runtime
--lib --target x86_64-pc-windows-gnu --offline` was attempted but stopped in a
C build script because this host lacks `x86_64-w64-mingw32-gcc`; it did not
reach this Rust module. Full Windows bootstrap and artifact admission require
a protected CI run on the integrated source revision.
