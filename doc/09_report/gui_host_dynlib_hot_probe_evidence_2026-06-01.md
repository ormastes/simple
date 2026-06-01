# GUI Host Dynlib Hot Probe Evidence

Date: 2026-06-01

## Scope

Diagnostic evidence for the pure GUI hot symbol as a callable host dynamic
library. This is not SMF acceptance evidence.

## Build

```bash
mkdir -p build/gui
SIMPLE_LIB=src src/compiler_rust/target/debug/simple compile src/app/gui_perf/pure_gui_hot_dynlib_export.spl --native --shared --strip -o build/gui/libpure_gui_hot.so
```

Result:

```text
Compiled src/app/gui_perf/pure_gui_hot_dynlib_export.spl -> build/gui/libpure_gui_hot.so (5891832 bytes, opt-level=aggressive)
```

## Probe

```bash
SIMPLE_LIB=src SIMPLE_GUI_DYNLIB_ARTIFACT=build/gui/libpure_gui_hot.so src/compiler_rust/target/debug/simple run src/app/gui_perf/smf_dynlib_probe.spl
```

Result:

```text
GUI_DYNLIB_PERF artifact=build/gui/libpure_gui_hot.so loader=host_dynlib symbol=gui_dynlib_hot_probe_tick call_source=dynlib_symbol_call samples=128 warmup=16 p50_us=17 p95_us=19 p99_us=26 max_us=27 threshold_us=1000 pass=false error=not-smf-dynlib
```

## Interpretation

The pure GUI i64 hot symbol is callable through a real host dynlib and is well
below the 1000 us p99 target. The row correctly fails because the requested
acceptance loader is `smf_dynlib`, not `host_dynlib`.
