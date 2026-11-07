# Piped process generation reference V1 scenarios

Source: `test/01_unit/lib/io/piped_process_ref_v1_spec.spl`.
Oracles: `test/fixtures/piped_process_ref_v1.spl`.
Status: **AWAITING_VERIFICATION**; authored manual, no execution/docgen PASS.

| Requirement | Scenario | Required evidence |
|---|---|---|
| PPIPE-01/03 | Zero PID/generation or missing generation across read/write/alive/close/validate | invalid_process_reference before native effects |
| PPIPE-02 | Empty/relative command, internal NUL,65 arguments | Exact admission error; no spawn |
| PPIPE-03 | Copied reference with current PID and wrong generation | All actions stale; validation stale; current stream/child unaffected |
| PPIPE-04 | Child prints prefix then waits for three UTF-8 bytes | Deferred read remains nil; writes advance at most one byte per call; exact payload echoed |
| PPIPE-04 | Child exits after incomplete UTF-8 tail | Windows liveness false retains bytes; POSIX liveness unsupported; tail replacement emitted before observed EOF |
| PPIPE-05 | Windows checked close, duplicate and subsequent operations | First close succeeds; later read/write/alive/close/validate stale |
| PPIPE-05 | POSIX lifecycle while live and after EOF | process_close_unsupported / process_liveness_unsupported; no wait or signal; bounded slot retained until the owning host/fixture process exits |
| PPIPE-03 | Validate current/exited/drained registry reference | Success without I/O, wait or signal; stream bytes unchanged |

Additional native boundary source:
`src/runtime/test/piped_process_ref_v1_selfcheck.c`. It uses the actual registry
and reader, real native child/pipes, deterministic same-PID coexistence and
replacement, exact-generation selector checks, stale cross-operation refusal,
forced full-pipe zero progress, invalid write ranges, separate legacy
PID spawn/read/write/liveness/close, INT64_MAX admission and counted NUL/argv
rejection. Signal interception observes
and forwards actual signal/wait calls; POSIX Ref paths must emit none, including
stale leader-reaped metadata pointing at a reused child PID. Only the explicit
native test harness reaps its known child after EOF. White-box fixture
retirement is explicitly test-only, not a supported production fallback.

The native/SSpec fixture must fail if its real child executable is absent. No
optional-provider success, placeholder body, raw PID cleanup fallback, actual OS
PID-reuse execution or POSIX group-incarnation guarantee is claimed.
