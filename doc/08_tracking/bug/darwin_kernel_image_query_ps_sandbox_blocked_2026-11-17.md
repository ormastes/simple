# Darwin kernel image discovery depends on setuid `/bin/ps` blocked under macOS sandboxes

Status: FIXED (verified locally inside Seatbelt sandbox on aarch64-apple-darwin).

## Root Cause

On macOS (`host_os() == "macos"`), `cli_kernel_executable_path()`, `_cli_self_exe_via_pid_query()`, and `_cli_current_exe_path()` in `src/app/io/cli_ops.spl` (plus sibling self-exe queries in `src/app/cli/native_build_main.spl` and `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`) had no in-process image owner analogous to `windows_image_owner.spl` or Linux `/proc/self/exe`.

Instead, Darwin fell back to spawning `/bin/ps -o comm= -p <pid>`. Because `/bin/ps` on macOS is setuid-root, macOS Seatbelt / sandbox profiles deny or strip its execution (`posix_spawn` / `setuid` restriction), causing `cli_kernel_executable_path()` and `native-build` producer resolution to return `""` inside sandboxed environments.

## Fix

1. Added `src/lib/nogc_sync_mut/io/darwin_image_owner.spl` mirroring `windows_image_owner.spl`:
   - Under `@when(os="macos"):`, declares `_NSGetExecutablePath(buffer: i64, bufsize: i64) -> i32` with `@unsafe(..., capabilities: [ffi, raw_ptr])`.
   - `darwin_image_path_with_capacity(capacity)` validates `1..=32768`, allocates private buffers with `malloc`, initializes the `u32` capacity cell via `volatile_write_u32`, invokes `_NSGetExecutablePath`, resolves symlinks via `realpath(buffer, 0)`, scans bounded bytes up to `capacity` using `volatile_read_u8`, frees all heap allocations, validates UTF-8 via `validated_utf8_bytes_to_text_linear`, and rejects empty, relative, or `.spl` paths.
   - Non-macOS targets compile the `@else:` stub returning `Err("Darwin image query unavailable on this platform")`.
   - `darwin_image_path()` queries with capacity `32768`.
2. Updated `src/app/io/cli_ops.spl`:
   - `cli_kernel_executable_path()` resolves macOS strictly via `darwin_image_path()` (and `_cli_resolve_symlink`) without ever spawning `/bin/ps`.
   - `_cli_self_exe_via_pid_query()` and `_cli_current_exe_path()` query `darwin_image_path()` first on macOS and fall back to `/bin/ps` only if `darwin_image_path()` returns `Err(_)` (backwards compatibility with older un-updated seed interpreters).
3. Updated `src/app/cli/native_build_main.spl` (`self_exe()`) and `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` (`_self_exe_via_pid_query()`) to prefer the in-process Darwin query on macOS before spawning `readlink` or `ps`.
4. Registered `_NSGetExecutablePath` in `src/compiler_rust/compiler/src/interpreter_extern/posix_abi.rs` under `#[cfg(target_os = "macos")]` (`MACOS_NAMES`) with null/negative/alignment pointer validation and `extern_drift_tests.rs` + `cfg_import_target_cache.rs` coverage.
5. Added regression unit spec `test/01_unit/lib/darwin_kernel_image_spec.spl`.

## Verification (2026-11-17, aarch64-apple-darwin, Seatbelt sandbox)

- `cargo test --locked --offline --profile bootstrap --target aarch64-apple-darwin -j 8 -p simple-compiler --lib posix_abi`: 9 passed, 0 failed.
- `cargo test --locked --offline --profile bootstrap --target aarch64-apple-darwin -j 8 -p simple-compiler --lib extern_drift`: 3 passed, 0 failed.
- `cargo test --locked --offline --profile bootstrap --target aarch64-apple-darwin -j 8 -p simple-compiler --lib cfg_strip`: 6 passed, 0 failed.
- `cargo test --locked --offline --profile bootstrap --target aarch64-apple-darwin -j 8 -p simple-compiler --test cfg_import_target_cache`: 4 passed, 0 failed.
- `cargo build --locked --offline --profile bootstrap --target aarch64-apple-darwin -j 8 -p simple-driver --features llvm`: built cleanly.
- `test/01_unit/lib/darwin_kernel_image_spec.spl --mode=interpreter` (newly built driver + test runner): 2 examples, 0 failures (`outcome=OK`).
- `test/01_unit/lib/io/path_identity_interp_posix_abi_spec.spl --mode=interpreter`: 4 passed, 0 failed (`outcome=OK`).
- Native Mach-O `native-build --backend llvm` probe built with both the newly built driver (`83 compiled, 0 failed`, 7.4s) and `seed/runtime/simple` (`83 compiled, 0 failed`, 7.0s); executed directly, under `env -i PATH=/nonexistent`, and via symlink — all printed `NATIVE_DARWIN_IMAGE_PROBE_PASS` with matching `darwin_image_path()`, `cli_kernel_executable_path()`, and `cli_current_exe_path()`.
- `simple check` on modified `src/` files and `simple lint src/lib/nogc_sync_mut/io/darwin_image_owner.spl`: 0 errors.
