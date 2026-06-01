# GUI SMF dynlib executable mapping missing

Date: 2026-06-01

## Summary

The pure GUI SMF/dynlib performance probe can open and resolve dynamic-library
symbols through the existing `DynLibKind` facade, and the Rust runtime now has
the declared `rt_dyncall_*` externs. The remaining blocker is that current SMF
registry symbol resolution does not prove the resolved address is mapped into
the host process as executable code.

## Evidence

`src/os/posix/dynlib_sffi.spl` declares:

```simple
extern fn rt_dyncall_0(fn_ptr: i64) -> i64
extern fn rt_dyncall_1(fn_ptr: i64, arg0: i64) -> i64
...
extern fn rt_dyncall_6(fn_ptr: i64, arg0: i64, arg1: i64, arg2: i64, arg3: i64, arg4: i64, arg5: i64) -> i64
```

`src/compiler_rust/runtime/src/value/sffi/dyncall.rs` now implements these
externs for process-callable `i64` ABI functions. The SMF registry path still
needs executable mapping evidence before the GUI probe can use those function
pointers safely.

## Current Probe Behavior

`src/app/gui_perf/smf_dynlib_probe.spl` emits a machine-readable
`GUI_DYNLIB_PERF` row, but it fails closed while SMF executable mapping is
missing.
Without an artifact configured, the current host reports:

```text
GUI_DYNLIB_PERF artifact= loader=direct_simple symbol=gui_dynlib_hot_probe_tick call_source=direct_simple samples=128 warmup=16 p50_us=738 p95_us=1007 p99_us=1134 max_us=1233 threshold_us=1000 pass=false error=missing-artifact-path
```

When SMF registry symbol resolution succeeds without executable mapping
evidence, the probe must report `call_source=registry_symbol_only` and remain
`pass=false` until the measured path uses `call_source=dynlib_symbol_call`.

## Impact

This blocks completion of the macOS arm64 acceptance gate:

- load pure GUI as SMF/dynlib,
- resolve `gui_dispatch_events`,
- call the resolved symbol in the measured hot path,
- prove p99 response is below 1000 us without fallback.

## Required Fix

Implement and verify true SMF executable mapping for the pure GUI SMF artifact,
or replace the registry path with an equivalent SMF dynlib symbol invocation API
that returns process-callable function pointers. Then update
`src/app/gui_perf/smf_dynlib_probe_core.spl` to collect samples from the real
dynlib call path and report `call_source=dynlib_symbol_call`.

## Update: 2026-06-01

`src/compiler_rust/runtime/src/value/sffi/dyncall.rs` now implements
`rt_dyncall_0` through `rt_dyncall_6` for the existing i64 ABI bridge. The GUI
probe intentionally does not call the SMF registry address yet; resolved SMF
registry symbols are classified as `call_source=registry_symbol_only` and fail
closed.

## Update: 2026-06-01 loader evidence API

`src/os/kernel/loader/dylib_registry.spl`,
`src/os/posix/dylib_async.spl`, and `src/os/posix/dynlib.spl` now expose a
process-callability query for resolved symbols. The current registry
implementation returns false because it has byte storage plus ELF virtual
addresses, not executable host mappings. `src/app/gui_perf/smf_dynlib_probe_core.spl`
uses that query before it can report `call_source=dynlib_symbol_call`.

## Update: 2026-06-01 host dynlib diagnostic

`src/app/gui_perf/pure_gui_hot_dynlib_export.spl` builds as a host shared
library and exports `gui_dynlib_hot_probe_tick`. On the current Linux host:

```bash
mkdir -p build/gui
SIMPLE_LIB=src src/compiler_rust/target/debug/simple compile src/app/gui_perf/pure_gui_hot_dynlib_export.spl --native --shared --strip -o build/gui/libpure_gui_hot.so
SIMPLE_LIB=src SIMPLE_GUI_DYNLIB_ARTIFACT=build/gui/libpure_gui_hot.so src/compiler_rust/target/debug/simple run src/app/gui_perf/smf_dynlib_probe.spl
```

The probe measured `loader=host_dynlib call_source=dynlib_symbol_call
p99_us=26`, then correctly rejected the row with `error=not-smf-dynlib`. This
proves the hot symbol ABI and dynlib call overhead; it does not close the SMF
artifact requirement.

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
