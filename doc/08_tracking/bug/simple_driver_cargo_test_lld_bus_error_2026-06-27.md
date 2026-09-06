# simple-driver cargo test linker bus error

Status: open
Severity: P2 resource/toolchain
Date: 2026-06-27

## Symptom

A focused Rust test command for `simple-driver` failed during test-binary linking with `rust-lld`/`cc` signal 7 bus errors. After the linker failures, the cargo process did not exit promptly and had to be interrupted.

## Evidence

- Command: `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-driver test_baremetal_target_enables_gc_boundary_errors`
- Failure: `collect2: fatal error: ld terminated with signal 7 [Bus error]`
- Affected link targets included unrelated test binaries such as `os_cli_dispatch_tests`, `native_compile_size_reporting`, `interpreter_async_tests`, and `capability_tests`.
- Backtrace pointed into `rust-lld` / LLVM output section writing.
- Recovery: sent Ctrl-C to the still-running cargo session; exit status was `130`.

## Impact

Even a filtered `cargo test` can attempt to link many test binaries for `simple-driver`, causing high memory/resource pressure and leaving a long-running process after linker crashes. This is not suitable as an unattended Codex verification step on this host.

## Expected Behavior

Filtered Rust tests should either avoid linking unrelated test binaries or fail cleanly when the linker crashes. Verification guidance should prefer `cargo check --lib` or a narrower test target on this host unless the environment has enough resources.

## Follow-Up

- Prefer `CARGO_BUILD_JOBS=1 cargo check --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --lib` for compile verification of driver-library changes.
- Investigate whether `simple-driver` integration tests can be split or filtered to avoid linking all heavy test binaries for a single unit-test filter.
- Capture host memory and linker parallelism settings before retrying full Rust test linking.
