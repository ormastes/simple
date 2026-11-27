# PipedProcessRefV1 externs existed only in the C runtime

Status: FIXED 2026-11-14. Host: macOS 26.5 arm64, release/1.0.0 `f998bc43600`.

## Defect

`test/03_system/app/llm_caret/feature/smux_runtime_terminal_transport_spec.spl`
(0/1) died with `semantic: unknown extern function:
rt_process_spawn_piped_generation_v1` (called from
`src/lib/nogc_sync_mut/io/process_ops.spl:2314`). The whole
`rt_process_*_ref_v1` family (`process_ops.spl:2122-2137`) was implemented
only in `src/runtime/runtime_process.c`; the interpreter extern table had none.

## Fix

`src/compiler_rust/compiler/src/interpreter_extern/system.rs` extends the
existing `PIPED_PROCESSES` registry with a `generation` field (0 = legacy
pid-only spawn) and adds the eight externs with the C sentinels:
spawn (C input validation: exact length, no NUL, <= 64 args) -> generation;
`pid_for_generation` (-2 unknown); `read_stdout_ref` ("" stale);
`stdout_state_ref` / `validate_piped_ref` / `write_stdin_some_ref` (-2 stale);
`is_piped_alive_ref` and `close_piped_ref` answer -3 ("POSIX unsupported") for
a live reference and never signal or reap, exactly like the C owner. Registered
in `interpreter_extern/mod.rs`. The compiled lane still links the C symbols
(no Rust runtime definition was added, avoiding a duplicate symbol).

## Specs

Reproducing: `smux_runtime_terminal_transport_spec.spl` 0/1 -> 1/1 (new seed).
It also covers the generalization (stale-generation close rejected without
invalidating either owner; unsupported close retains the slot; output drained
to EOF).

BSD: pure registry logic over `std::process`; same on FreeBSD.
