# Simple Core Loaded libm Gap

Date: 2026-05-27

## Summary

The startup/size audit now records loaded dynamic libraries. Current C counter
binaries load only:

- `libc.so.6`
- `/lib64/ld-linux-x86-64.so.2`

Resolved: current Simple core audit rows now load the same shared library set as
the C counters.

## Evidence

Run:

```sh
SIMPLE_BINARY=src/compiler_rust/target/debug/simple RUNS=20 sh scripts/check-startup-size-performance-audit.shs
```

`doc/09_report/startup_size_performance_audit_2026-05-27.md` now shows Simple
hello, standalone TUI, mmap preload, TCP, UDP, plain HTTP, and the full TUI app
loading only:

- `libc.so.6`
- `/lib64/ld-linux-x86-64.so.2`

## Current Work

`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` wraps
Linux platform libraries with `-Wl,--as-needed` in the native-project linker
path so unused platform libraries can be dropped from `DT_NEEDED` in generated
native binaries.

The Linux core-lane linker path also omits `-lm` unless entry objects directly
reference libm symbols or Simple runtime math wrappers. Dormant math code in the
core runtime archive no longer forces `libm` into hello/TUI/network binaries.

## Verification

- `cargo test -q -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml linker_tests::link_inputs_require_libm_detects_math_symbols_only_when_referenced`: PASS
- `cargo build -q --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple`: PASS
- `SIMPLE_BINARY=src/compiler_rust/target/debug/simple RUNS=20 sh scripts/check-startup-size-performance-audit.shs`: PASS

The focused hello verbose probe linked without `-lm`, and `ldd` showed only
`libc.so.6` and the dynamic loader.

## Remaining Size Gap

Loaded-library parity is resolved, but file-size parity is not. Simple hello and
standalone TUI remain 26864 bytes versus the 14472-byte C counters, and the
Simple mmap preload row remains 34968 bytes versus the 14472-byte C baseline.
