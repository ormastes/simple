# GUI SMF dynlib hot-call runtime missing

Date: 2026-06-01

## Summary

The pure GUI SMF/dynlib performance probe can open and resolve dynamic-library
symbols through the existing `DynLibKind` facade, but it cannot yet execute the
resolved hot symbol because the runtime does not implement the declared
`rt_dyncall_*` externs.

## Evidence

`src/os/posix/dynlib_sffi.spl` declares:

```simple
extern fn rt_dyncall_0(fn_ptr: i64) -> i64
extern fn rt_dyncall_1(fn_ptr: i64, arg0: i64) -> i64
...
extern fn rt_dyncall_6(fn_ptr: i64, arg0: i64, arg1: i64, arg2: i64, arg3: i64, arg4: i64, arg5: i64) -> i64
```

A repository search for `rt_dyncall` outside that declaration only finds the
wrapper calls in the same file. No Rust/runtime SFFI implementation is present
under `src/compiler_rust`, `src/runtime`, `src/os`, or `src/compiler`.

## Current Probe Behavior

`src/app/gui_perf/smf_dynlib_probe.spl` now emits a machine-readable
`GUI_DYNLIB_PERF` row, but it fails closed while the dynlib hot call is missing.
Without an artifact configured, the current host reports:

```text
GUI_DYNLIB_PERF artifact= loader=direct_simple symbol=gui_dispatch_events call_source=direct_simple samples=128 warmup=16 p50_us=719 p95_us=764 p99_us=859 max_us=918 threshold_us=1000 pass=false error=missing-artifact-path
```

Even when symbol resolution is added, direct in-process fallback samples must
remain `pass=false` until the measured path uses
`call_source=dynlib_symbol_call`.

## Impact

This blocks completion of the macOS arm64 acceptance gate:

- load pure GUI as SMF/dynlib,
- resolve `gui_dispatch_events`,
- call the resolved symbol in the measured hot path,
- prove p99 response is below 1000 us without fallback.

## Required Fix

Implement and verify native/runtime support for `rt_dyncall_0` through
`rt_dyncall_6`, or replace the declared bridge with an equivalent SMF dynlib
symbol invocation API. Then update `src/app/gui_perf/smf_dynlib_probe_core.spl`
to collect samples from the real dynlib call path and report
`call_source=dynlib_symbol_call`.

## Update: 2026-06-01

`src/compiler_rust/runtime/src/value/sffi/dyncall.rs` now implements
`rt_dyncall_0` through `rt_dyncall_6` for the existing i64 ABI bridge, and
`src/app/gui_perf/smf_dynlib_probe_core.spl` now uses `dynlib_call_1` when an
SMF/dynlib artifact resolves the configured hot symbol.

The default hot symbol is now `gui_dynlib_hot_probe_tick`, an i64-only pure GUI
entry in `src/lib/gui/pure_core.spl`.

Focused verification:

```bash
cargo check -j1 -p simple-runtime
SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/lib/gui src/app/gui_perf/smf_dynlib_probe_core.spl src/app/gui_perf/smf_dynlib_probe.spl test/unit/app/gui_perf/smf_dynlib_probe_spec.spl test/unit/lib/gui/pure_core_spec.spl test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter --no-cache
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gui/pure_core_spec.spl --mode=interpreter --no-cache
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl --mode=interpreter --no-cache
```

Remaining gap: there is still no configured macOS arm64 SMF/dynlib artifact in
the current evidence run, so the CLI correctly reports `pass=false` with
`error=missing-artifact-path`.

Attempted Rust unit-test command:

```bash
cargo test -j1 -p simple-runtime dyncall --lib
```

That test build is blocked before reaching the dyncall tests by an unrelated
existing compile error in `runtime/src/value/pty.rs`:

```text
cannot find function `rt_pty_write` in this scope
```
