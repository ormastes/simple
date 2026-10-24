# Seed-interp Windows memory probe: GetProcessHeap-family externs unresolved (2026-10-24)

Bug id: `seed_interp_windows_memory_probe_2026_10_24`

## Symptom

`native-build --entry-closure` for `src/app/devhub/main.spl` and
`src/app/llm_caret/main.spl` (phase-2/seed compiler, Windows) aborts within
~30 s:

```
ERROR simple_compiler::interpreter_sffi: rt_interp_call: function not found: GetProcessHeap
error: extern `GetProcessHeap` (argc=0) is declared in Simple but backed by no
implementation; refusing to substitute nil for an unresolved extern.
```

`bootstrap-from-scratch.sh --full-bootstrap` preflight aborts at the memory
admission with `available: 0 via unknown` and
`host RAM: ... via proc-meminfo` (a POSIX probe path selected on Windows).

## Root cause

`std.nogc_sync_mut.io.windows_process_owner.windows_available_memory_headroom_v1`
takes a MEMORYSTATUSEX snapshot through raw kernel32 heap externs
(`GetProcessHeap`/`HeapAlloc`/`GlobalMemoryStatusEx`/`HeapFree`). Under the
pure interpreter (no JIT splice), raw Windows API externs have no registered
implementation: `rt_interp_call` falls back to
"function not found" (`runtime_native.c` rt_interp_call default). The probe's
`Err` then makes the native-build / preflight memory admission degrade to
"unknown", i.e. `available: 0`, and the admission refuses the build. The
p2_add-style repros never hit this because their small closures never sampled
the admission path the same way (and historical repros set
SIMPLE_NATIVE_BUILD_FORCE_WORKER=0 while also not requesting a memory-policy
sample).

## Fix (landed with this doc)

Runtime-C wrapper `rt_host_memory_headroom_bytes_v1()`
(`runtime_native.c`): the same snapshot in registered runtime C, returning
`min(ullAvailPhys, ullAvailPageFile)` (mirroring
`windows_capacity_headroom_v1`), 0 on failure / non-Windows. The Simple probe
now tries the wrapper FIRST (resolves under the seed interpreter) and falls
back to the extern path (full AOT fidelity, existing diagnostics).

## Remaining gap

`app.bootstrap_builder.native_group_windows_main.native_group_windows_commit_headroom_v1`
still uses the raw heap externs (K32GetPerformanceInfo). It only runs on the
grouped-native spawn path, degrades to a graceful `Err`, and was not part of
the failing flows; left unchanged in this fix.
