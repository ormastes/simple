# SOSIX/POSIX read/write compatibility audit

**Date:** 2026-08-11  
**Scope:** routing, open-file-description offsets, errno, partial progress, and
notification waiting  
**Nature:** static audit and bounded implementation recommendations; no runtime
claim and no modification to `src/os/sosix/io_rw.spl`

## Verdict

The current path is not yet a conforming POSIX compatibility layer over the new
typed SOSIX operation core. The typed operation/completion and wait-set modules
are useful foundations, but the live `posix_read`/`posix_write` path still uses
the legacy raw-slot implementation. That implementation performs a blocking IPC
receive inside functions named `async`, conflates distinct submission errors,
cannot retain an error together with partial progress, and updates shared file
offsets outside any open-file-description serialization.

## Findings

### P0 — socket routing is internally contradictory

`fd_io_read_route` and `fd_io_write_route` classify type 4 as a socket and
`posix_read`/`posix_write` forward it to `sync_read`/`sync_write`
(`src/os/kernel/fd_io.spl:84-106,193-195,292-294`). The receiving SOSIX router
only owns types 1 and 6 (`src/os/sosix/io_state.spl:27-33`), so a valid socket is
reported as the same sentinel used for an invalid descriptor and becomes
`-EBADF`. Route sockets directly to the socket compatibility owner, or add a
real socket SOSIX backend; do not send them through the file/serial owner.

### P0 — the asynchronous contract blocks and lacks correlation

Both VFS submissions immediately execute syscall 21 receive
(`src/os/sosix/io_rw.spl:69-89,129-146`). The request table's fd and method
columns are reset but never populated by this path
(`src/os/sosix/io_state.spl:20-25,47-59`). Multiple outstanding requests cannot
be correlated. This also depends on the unresolved syscall-21 ABI documented in
`doc/08_tracking/bug/sosix_vfs_ipc_receive_abi_mismatch_2026-08-11.md`.

Freeze the receive ABI and correlation token first. Submission must stop after
enqueue/send. A completion worker must validate `(slot,generation)`, API ID,
reply length, and capability before publishing one typed completion.

### P0 — offset updates are not atomic open-file-description operations

The fd table correctly stores offsets on the shared open-file description
(`src/os/kernel/fd_table.spl:691-711`), so dup aliases share state. However, a
request snapshots an offset, later reads the *current* offset again, and stores
`current + transferred` (`src/os/sosix/io_rw.spl:61-66,83-89,117-122,144-146`).
Two concurrent operations on one open-file description can issue the same
offset and then double-advance, lose an advance, or associate returned bytes
with the wrong logical range.

Add an open-file-description I/O sequencer. A POSIX `read`/`write` reserves and
commits one offset transition in submission order; a canonical `read_at` or
`write_at` takes an explicit offset and never changes shared position. Commit
only successfully transferred bytes. `O_APPEND` must choose EOF and perform the
write atomically in the backend, not via client-side stat-plus-write.

### P0 — reply sizes and transferred counts are not validated

The read reply buffer is 4096 bytes but payload copying starts at byte 12. A
reported `bytes_read > 4084` indexes past the reply even though the destination
loop is capped only by requested count (`src/os/sosix/io_rw.spl:73-88`). Both
read and write accept a backend count greater than the request and advance the
offset by it. The completion worker must reject truncated headers, oversized
counts, `transferred > requested`, and read payloads shorter than transferred.

### P1 — access modes and zero-length semantics are incomplete

Normal `posix_read` does not reject `O_WRONLY`, and normal `posix_write` does not
reject `O_RDONLY`; only the exact-read helper checks write-only mode
(`src/os/kernel/fd_io.spl:173-204,209-221,272-300`). A zero-length serial read
still reads a UART byte and writes one byte to the caller buffer
(`src/os/sosix/io_rw.spl:43-50`). Validate descriptor and access mode, then
return zero for a zero-length operation without touching the buffer or backend.

### P1 — errno domains are collapsed

Allocation exhaustion, unsupported fd type, and invalid fd all return raw slot
sentinel 128, which synchronous wrappers translate to `-EBADF`
(`src/os/sosix/io_rw.spl:39-54,97-110,153-157,178-182`). IPC failures are
unconditionally `-EIO`. Replace the sentinel with a typed submit result:

| Condition | Compatibility result |
|---|---:|
| invalid fd / wrong access mode | `-EBADF` |
| queue full or nonblocking operation would wait | `-EAGAIN` |
| unsupported operation/backend | `-ENOSYS` or `-ENOTSUP` (freeze one) |
| invalid user buffer | `-EFAULT` |
| malformed/corrupt transport reply | `-EIO` |
| backend negative errno | preserve unchanged |

### P1 — partial progress is lost

The typed `SosixCompletion` can carry both status and transferred bytes, but the
legacy request pool stores one `i64` result. Freeze the POSIX projection: when a
terminal completion reports nonzero transferred bytes, `read`/`write` returns
that positive count; a simultaneous error is retained on the operation receipt
for audit/retry policy. With zero progress, return the negative errno. Never
advance the shared offset by more than the returned positive count.

### P1 — synchronous waiting is one-shot and ignores wait failure

The wrappers check once, call notification wait once, ignore its return value,
check once more, and return `-EAGAIN` if still pending
(`src/os/sosix/io_rw.spl:158-172,183-197`). A spurious/unrelated wake therefore
turns a blocking call into an error; cancellation/deadline races have no
defined precedence. Use `SosixWaitSet` as the state owner and an OS adapter loop:

1. register exact `(slot,generation)` before submission;
2. recheck ready state before sleeping (lost-wake guard);
3. sleep through the notification facade;
4. drain all ready completions and match API ID;
5. retry spurious wakes; stop only on a matching terminal completion, deadline,
   cancellation, or a real wait syscall error;
6. unregister and destroy notification state on every exit path.

`SosixWaitSet.notify` already rejects unwatched generations and duplicate ready
records (`src/os/sosix/core/wait_set.spl:36-63`), but it is not wired into the
live POSIX path.

### P2 — `pread_exact` mutates shared state temporarily

`posix_pread_exact_bytes` implements positional I/O by replacing the shared
offset, repeatedly calling ordinary read, and restoring it
(`src/os/kernel/fd_io.spl:227-270`). Concurrent users and dup aliases can observe
the temporary offset. Lower it to canonical `read_at` operations instead.

## Bounded implementation order

1. Freeze and test syscall-21 reply/correlation ABI.
2. Add typed `SosixSubmitResult` and a completion worker; keep legacy exports as
   adapters only.
3. Correct socket routing and access/zero-length validation.
4. Add per-open-file-description sequencer plus backend-atomic append.
5. Add the wait-set notification adapter and migrate sync wrappers.
6. Lower `pread_exact` directly to `read_at`; then remove duplicated legacy I/O
   state and the older `src/os/sosix/io.spl` implementation.

## Required focused evidence

- socket read/write reaches the socket owner, not `EBADF`;
- `O_RDONLY` write and `O_WRONLY` read return `EBADF`;
- zero-length serial/file operations perform no device or memory access;
- queue-full returns `EAGAIN`, distinct from invalid fd;
- backend errno survives unchanged;
- partial transfer plus error returns the count and advances by that count;
- two concurrent reads through dup aliases consume disjoint ranges and leave
  the shared offset at their sum;
- concurrent `O_APPEND` writes are whole and non-overlapping;
- `read_at`/`pread` never changes shared offset;
- malformed/oversized/truncated replies fail `EIO` without buffer or offset
  mutation;
- pre-completion, spurious wake, duplicate completion, stale generation,
  cancellation, timeout, and wait-syscall-error cases terminate exactly once.

These should be unit tests around pure state owners plus one real IPC
round-trip integration test. They must not mock a successful VFS reply by
writing directly into the completion table.
