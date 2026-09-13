## Closed 2026-09-13 — policy superseded, libm now deliberately kept

Status: CLOSED — resolved then superseded (reviewed 2026-09-13). The size/DT_NEEDED parity was already recorded resolved in the body with Linux measurements. It could NOT be re-measured here: this host is Windows x86_64, and the whole repro (`ldd`, `libc.so.6`, `/lib64/ld-linux-x86-64.so.2`, the audit script) is Linux-only — so the closure below is STATIC/INFERRED, not measured. Static state at `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`: `-Wl,--as-needed` is still emitted (2 sites), but the named verification test `linker_tests::link_inputs_require_libm_detects_math_symbols_only_when_referenced` NO LONGER EXISTS — it was replaced by `core_lane_keeps_platform_libm` (linker.rs:3167), which asserts the opposite policy: `should_omit_platform_library("m", true, true) == false`, i.e. the core lane now deliberately KEEPS libm and only drops `unwind`/`sqlite3`. The "omit -lm unless math symbols are referenced" mechanism this entry describes as Current Work has therefore been superseded by a later design decision. Nothing here is actionable; closing rather than reopening against a policy that was changed on purpose.

---

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
SIMPLE_BINARY=src/compiler_rust/target/debug/simple RUNS=20 sh scripts/check/check-startup-size-performance-audit.shs
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
- `SIMPLE_BINARY=src/compiler_rust/target/debug/simple RUNS=20 sh scripts/check/check-startup-size-performance-audit.shs`: PASS

The focused hello verbose probe linked without `-lm`, and `ldd` showed only
`libc.so.6` and the dynamic loader.

## Size Gap Resolution

File-size parity is also resolved. Current audit results from
`doc/09_report/startup_size_performance_audit_2026-05-27.md`:

- Simple hello core-c-bootstrap: **14336** bytes (C baseline: 14472 bytes)
- Simple mmap preload argparse: **14400** bytes (C baseline: 14472 bytes)
- Simple TCP connect: **14328** bytes (C baseline: 14472 bytes)
- Simple UDP send: **14328** bytes (C baseline: 14472 bytes)
- Simple HTTP plain connect: **14336** bytes (C baseline: 14472 bytes)

All Simple core-lane binaries are now at or below the corresponding C counter
sizes. The previous 26864-byte hello and 34968-byte mmap preload figures were
from before the core-C startup lane and `--gc-sections` / `--as-needed` fixes
landed. Separate tracking bugs for each lane are resolved:
`simple_mmap_preload_size_gap_2026-05-27.md`,
`simple_network_size_gap_2026-05-27.md`,
`simple_https_size_lane_missing_2026-05-27.md`.
