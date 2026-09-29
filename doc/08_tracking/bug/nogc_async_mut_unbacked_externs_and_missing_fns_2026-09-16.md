# nogc_async_mut specs pin lib functions that do not exist (or have no rt_ backing)

Date: 2026-09-16
Status: OPEN

## Observed

Worklist specs fail on symbols with no implementation anywhere in `src/lib`
(or with externs lacking runtime backing):

- `concurrent/multicore_green_try_spawn_contract_spec.spl` — `semantic: function 'multicore_green_try_spawn' not found`.
- `http_server/tls_record_capability_spec.spl` — `tls_record_path_admits_min_version` missing.
- `io/driver_write_completion_spec.spl` — `io_write_completion_has_progress_v1` missing.
- `quic/quic_udp_initial_spec.spl` — `build_unprotected_initial_shape` missing.
- `sosix/posix_spec.spl` — `unknown extern function rt_fd_pread` (declared, no runtime backing).

## Impact

The five specs cannot execute; the contracts they pin (green-thread try-spawn
semantics, TLS record floor admission, io_uring write-completion progress,
QUIC initial-packet shape, positional pread) have no runnable implementation
to verify against.

## Expectation

Each named function exists in `src/lib` with the semantics its spec documents,
and `rt_fd_pread` has a real runtime implementation.

## Unblock condition

Implement the four missing lib functions and back `rt_fd_pread` in the runtime
(or retire the specs with owner sign-off). Not spec-side fixable.
