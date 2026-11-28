# extern_shape_evpoll_spec readiness cases fail on Windows (2026-11-28)

Status: open (found in review of PR #12418)

`test/01_unit/runtime/extern_shape_evpoll_spec.spl` cases "reports fd, Read and the
registered token ..." and "reports Write readiness ..." expect one (fd, ready, token)
triple. On Windows the interpreter backend (`interpreter_event_loop.rs`, non-unix
`mod platform`), the Rust runtime `rt_event_loop_poll` (`#[cfg(not(unix))]` returns 0)
and the C fallback branch of `runtime_native.c` all report no events, so `ready.len()`
is 0, not 3.

Required fix (not a skip, not a weakened assert): implement the Windows backend
(IOCP/WSAPoll) so the cases pass, or, until then, pin the exact per-platform
expectation the way `test/02_integration/ui/event_backend_matrix_spec.spl` does with
`rt_platform_name`: on Windows assert `len() == 0` with a pointer to this bug, on every
other platform assert the triple. Also confirm the Linux interpreter backend returns
ready == 1 for a socket that is only writable.

Repro: `bin/simple test test/01_unit/runtime/extern_shape_evpoll_spec.spl` on Windows.
Prevention: the same spec doubles as the coverage at the bug site.
