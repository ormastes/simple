# GUI macOS SMF dynlib hot-call evidence missing

Date: 2026-06-01
Status: open (triaged 2026-06-11, macOS arm64 evidence still missing per body)

## Summary

The pure GUI SMF/dynlib performance probe now has a host SMF envelope path:
wrap a native shared library as a role-2 SMF artifact, extract the embedded
native library outside the hot loop, open it with the host dynlib loader, and
measure direct symbol calls. Linux host evidence passes below the 1 ms target.
The remaining blocker is macOS arm64 evidence for the same path with a `.dylib`
artifact.

## Evidence

Earlier investigation looked at `src/os/posix/dynlib_sffi.spl` declarations:

```simple
extern fn rt_dyncall_0(fn_ptr: i64) -> i64
extern fn rt_dyncall_1(fn_ptr: i64, arg0: i64) -> i64
...
extern fn rt_dyncall_6(fn_ptr: i64, arg0: i64, arg1: i64, arg2: i64, arg3: i64, arg4: i64, arg5: i64) -> i64
```

Those `rt_dyncall_*` externs are not the GUI release-lane solution. Current
release evidence uses the Simple SFFI dynamic API (`spl_dlopen`, `spl_dlsym`,
`spl_dlclose`, `spl_wffi_call_i64`) from the probe path. The SMF registry path
still needs executable mapping evidence before registry virtual addresses can be
used directly, so registry-only symbols remain non-acceptance evidence.

## Current Probe Behavior

`src/app/gui_perf/smf_dynlib_probe.spl` emits a machine-readable
`GUI_DYNLIB_PERF` row. It fails closed without an artifact or when extraction /
symbol resolution fails.
Without an artifact configured, the current host reports:

```text
GUI_DYNLIB_PERF artifact= loader=direct_simple symbol=gui_dynlib_hot_probe_tick call_source=direct_simple samples=128 warmup=16 p50_us=738 p95_us=1007 p99_us=1134 max_us=1233 threshold_us=1000 pass=false error=missing-artifact-path
```

The accepted row must report `loader=smf_dynlib`,
`call_source=dynlib_symbol_call`, `fallback_used=false`, and `p99_us < 1000`.

## Impact

This still blocks completion of the macOS arm64 acceptance gate:

- load pure GUI as SMF/dynlib,
- resolve the pure GUI hot ABI symbol,
- call the resolved symbol in the measured hot path,
- prove p99 response is below 1000 us without fallback.

## Required Fix

Run the new host SMF wrapper/probe flow on macOS arm64 with a `.dylib` built
from `src/app/gui_perf/pure_gui_hot_dynlib_export.spl`, then record the
`GUI_DYNLIB_PERF` row as macOS evidence.

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
SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/lib/gui src/app/gui_perf/smf_dynlib_probe_core.spl src/app/gui_perf/smf_dynlib_probe.spl test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl test/01_unit/lib/gui/pure_core_spec.spl test/01_unit/lib/gui/pure_smf_dynlib_perf_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/app/gui_perf/smf_dynlib_probe_spec.spl --mode=interpreter --no-cache
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/gui/pure_core_spec.spl --mode=interpreter --no-cache
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/lib/gui/pure_smf_dynlib_perf_spec.spl --mode=interpreter --no-cache
```

## Update: 2026-06-01 SMF-wrapped host dynlib path

The probe now supports a real SMF artifact path on the host:

- `src/app/gui_perf/smf_wrap_host_dynlib.spl` wraps a host `.so`/`.dylib` in a
  role-2 SMF envelope using Simple code in
  `src/app/gui_perf/smf_dynlib_artifact.spl`.
- `src/app/gui_perf/smf_dynlib_probe_core.spl` extracts the native library stub
  from the SMF envelope using Simple parsing/copying, writes a verified cache
  file, opens it with `spl_dlopen`, resolves `gui_dynlib_hot_probe_tick`, and
  samples `spl_wffi_call_i64` in the hot loop.

Current Linux host evidence:

```text
GUI_DYNLIB_PERF artifact=build/gui/pure_gui_hot.smf loader=smf_dynlib symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 warmup=16 p50_us=1 p95_us=1 p99_us=1 max_us=1 threshold_us=1000 pass=true error=
```

Remaining gap: there is still no macOS arm64 `.dylib`-backed SMF evidence row
from a mac host.

Attempted Rust unit-test command:

```bash
cargo test -j1 -p simple-runtime dyncall --lib
```

That test build is blocked before reaching the dyncall tests by an unrelated
existing compile error in `runtime/src/value/pty.rs`:

```text
cannot find function `rt_pty_write` in this scope
```

## Update: 2026-06-02 release-lane evidence state

Linux now has repeatable e2e evidence through
`src/app/gui_perf/linux_smf_dynlib_e2e_gate.spl` and
`test/03_system/gui/linux_smf_dynlib_e2e_gate_system_spec.spl`. The gate builds
`build/gui/libpure_gui_hot.so`, wraps it into `build/gui/pure_gui_hot.smf`,
extracts the SMF payload, calls it through SFFI, and requires:

```text
loader=smf_dynlib dynload=smf_dynlib host_dynload=sffi call_source=dynlib_symbol_call pass=true threshold_us=1000
```

The Linux gate is regression evidence for the pure Simple SMF wrap/extract/SFFI
path. It does not close this bug because the acceptance target is macOS arm64.

`test/03_system/gui/macos_smf_dynlib_release_gate_system_spec.spl` now runs the
macOS release gate as system evidence. On macOS it requires
`GUI_MAC_SMF_DYNLIB_RELEASE_GATE status=pass`; on non-mac hosts it accepts only
the explicit `requires-macos-arm64` skip/fail output so Linux CI cannot claim
mac release evidence.

`test/01_unit/lib/gui/pure_gui_release_lane_spec.spl` guards the mac and Linux SMF
evidence entrypoints against WM, Simple Web, BrowserWindow, WebRenderer,
WebRenderRequest, HostCompositor, native GUI runtime externs, legacy
`rt_file_wrap_smf_dynlib` / `rt_file_extract_smf_dynlib`, and `rt_dyncall`.

Remaining blocker: run the macOS release gate on real macOS arm64 and record a
passing transcript whose `GUI_DYNLIB_PERF` row reports the SMF/SFFI hot-call
path with `p99_us < 1000`.
