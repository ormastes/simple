# Async identity-owned process lease — TLDR

Purpose: let `QemuRunner` interact with a live QEMU process without exposing
raw PID authority or creating a second lifecycle owner.

Decision: extend `src/runtime/runtime_process_owned.c` with a Linux-only async
lease. Start returns a nonenumerable opaque capability backed by a random
128-bit token and a private registry binding. The registry retains
slot/generation/PID/PGID/pidfd/start identity internally. Poll and wait drain
bounded pipes. Cancel owner-serializes process-group TERM, bounded grace,
KILL, exact reap, final drain, token revocation, and slot release.

The existing synchronous owned-process call becomes a compatibility wrapper
over `start -> wait -> result -> collect`. PID-only cancellation remains
fail-closed. Windows and non-pidfd platforms return unsupported before spawn.

Primary implementation paths:

- `src/runtime/runtime_process_owned.c`
- `src/runtime/runtime.h`
- `src/lib/nogc_sync_mut/io/process_ops.spl`
- compiler runtime-symbol/SFFI registration files
- existing owned-process C and Simple contract tests

QemuRunner consumes the lease later through
`src/os/_QemuRunner/vm_adapter.spl`; it does not own another process registry.
