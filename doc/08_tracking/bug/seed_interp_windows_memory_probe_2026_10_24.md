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

## Follow-up: interpreter registration and commit layout (2026-10-24)

The initial fix's statement that the wrappers resolve under the seed
interpreter was premature: none of the three `rt_host_*_headroom_bytes_v1`
names was in `interpreter_extern/mod.rs`. The native C export alone does not
register a Rust interpreter handler, and the disk wrapper accepts native
tagged text rather than the interpreter's managed string representation.

Typed `host_capacity` adapters now register memory, commit and disk snapshots.
Their Win32 implementations query the host directly and decode interpreter
text before UTF-16 conversion. Unsupported hosts and failed queries return
zero, matching the native wrappers; invalid disk argument types are errors.

The native commit wrapper also read `PageSize` at offset 88 of Win64
`PERFORMANCE_INFORMATION`; the correct offset is 80. Offset 88 contains
`HandleCount` and `ProcessCount`, producing a potentially enormous fabricated
commit capacity. The native wrapper now uses the SDK's
`PERFORMANCE_INFORMATION` type instead of numeric offsets.

Bounded Windows validation:

```
python scripts/check/check-windows-host-capacity.py --cc C:/dev/tool/llvm-mingw-20260908-ucrt-x86_64/bin/clang.exe --output build/headroom-registration/sdk-negative-control
```

The fixture extracts the actual production C commit function, compiles it
against Win32 headers and compares its result with surrounding SDK snapshots
(page alignment and a bounded allowance for concurrent allocation). It passed
with 22,036,328,448 bytes and a 4096-byte page size. A negative control
reinserting the original offset-88 read failed the same oracle with status 2,
proving this check rejects the reported defect. The Rust platform module
was built with 24 codegen units and executed with `--test-threads=24`:
three tests passed, covering real memory/commit/disk capacity, Unicode paths,
and invalid paths. The ambient MSYS2 clang failed to start with DLL status
3221225781; the explicit pinned LLVM-MinGW compiler above succeeded.

A dispatch-level regression in `interpreter_extern/mod.rs` checks all three
registered handlers, real Windows capacity and disk argument validation.
The focused compiler-crate dispatch test subsequently passed: `cargo test
--profile release --package simple-compiler --lib
host_capacity_externs_dispatch_typed_snapshots --jobs 24 -- --test-threads=24`
executed one test, with one pass and zero failures. The broader `cargo check
--tests` encountered an existing type mismatch at
`compiler/tests/interpreter_shared_empty_global_bindings.rs:45`: the test
supplies `Arc<HashMap>` where `CowEnv::with_base` requires `Arc<LayeredEnv>`.

Independent review found the same offset-88 read in the Simple grouped-build
fallback. It now reads offset 80. The SDK fixture's `--layout-only` mode
checks seven actual Simple layout constants against SDK `sizeof`/`offsetof`.
It failed on the original PageSize constant and passed after the correction;
this is source-layout evidence rather than execution of the Simple fallback.

These host ABI and dispatch results do not admit a rebuilt seed or either
bootstrap phase; new compiler bytes and their phase checks remain separate
requirements.
