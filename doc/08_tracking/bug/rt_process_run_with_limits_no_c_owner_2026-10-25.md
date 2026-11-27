# rt_process_run_with_limits has no C runtime owner

Status: OPEN (P2)

## Summary

`rt_process_run_with_limits(cmd, args, timeout_ms, memory_bytes, cpu_seconds,
max_fds, max_procs) -> (text, text, i32)` is implemented only in the Rust
runtime (`src/compiler_rust/runtime/src/value/sffi/env_process.rs`). No C
owner exists under `src/runtime/`, so a binary linked against the
`core-c-bootstrap` runtime bundle (the bootstrap Stage 2/Stage 3 lane) has
nothing to back the extern.

It also shares the tuple-result defect fixed for the other process owners on
`work/p3fix-spawn4` (b73279a29a7, 87361501e3a, 99146622f97): the Rust owner
returns a registered runtime tuple, while the pure-Simple Cranelift/LLVM lanes
destructure a tuple result by loading words 0/8/16 of the returned handle. No
`*_tuple` raw-block facade or backend remap exists for it. MIR already splits
its `cmd` to (ptr, len) (`text_extern_abi.spl`).

## Scope

Only caller: `src/lib/nogc_sync_mut/sffi/system_hosted_extras.spl:8,13`. Not in
the Stage 3 compiler/CLI closure (no symbol in the phase3-ref Stage 3 binary),
so it does not block the bootstrap.

## Fix direction (owner decision)

Either implement a C owner in `runtime_process.c` (setrlimit for
memory/cpu/fds/procs around the existing `posix_process_run_capture`) plus a
`rt_process_run_with_limits_tuple` facade with a Rust twin and both backend
remaps, or retire the extern if no native consumer needs it.
