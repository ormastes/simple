<!-- codex-architecture -->
# Async identity-owned process lease

## Status

Proposed design for the native runtime and `QemuRunner`. This design does not
claim implementation or platform evidence.

## Decision

`runtime_process_owned.c` remains the single process-lifecycle owner. Its
current synchronous capsule becomes a compatibility composition over a new
asynchronous lease state machine. Callers never receive a slot, generation,
PID, pidfd, start time, pointer, or registry index as authority. They receive a
random, nonzero, 128-bit `RtOwnedProcessTokenV2`; only the runtime registry can
resolve that token to the identity tuple.

The token is:

- minted from an operating-system CSPRNG after slot reservation;
- compared in constant time while holding `rt_owned_lock`;
- unique among live and quarantined slots;
- never derivable from PID, slot, generation, time, or command;
- invalidated before pidfd close and slot reuse;
- not enumerable through any public count/list/get-by-index operation.

The internal slot retains `slot + generation + pid + pgid + pidfd +
start_identity`. On Linux, a lease is publishable only after `setpgid`, pidfd
open, `/proc/<pid>/stat` start identity capture, nonblocking pipe setup, and
token binding all succeed. Failure before publication kills and reaps the child
and releases every descriptor. Generation exhaustion retires the slot; it never
wraps to an earlier generation.

## Ownership state machine

```text
Free -> Reserved -> Live -> ExitedUndrained -> Terminal -> Collected -> Free
                       |          ^
                       +-> CancellingTerm -> CancellingKill -+
                       +-> FailedCleanup --------------------+
```

Exactly one registry lock serializes state transitions and cancel requests.
Only the owner that possesses the token may poll, wait, request cancellation,
or collect the result. These operations do not expose an independently usable
PID or pidfd. Result receipts may report PID/PGID/start identity as evidence
only after terminal state; those values are never accepted as authority.

Cancellation is a request, not a raw signal operation:

1. validate token and bind the request to the live registry entry;
2. transition once to `CancellingTerm` and signal the entire process group;
3. continue draining bounded stdout/stderr during the grace interval;
4. if the group remains live, transition once to `CancellingKill` and send
   `SIGKILL` to the group;
5. retain the leader unreaped until descendant cleanup is complete, then
   `waitpid` the direct child exactly once;
6. drain for the bounded post-reap interval, close pipes, produce the immutable
   terminal result, unpublish the token, then close pidfd;
7. release the slot only after explicit result collection or bounded terminal
   retention expiry. Expiry performs no signalling because reaping is already
   complete.

Timeout follows the same owner-serialized path and records a distinct reason.
Repeated cancel is idempotent. Concurrent poll/wait/cancel cannot double-signal,
double-reap, close a reused descriptor, or release a slot early.

## Process group and pipe containment

The child is a new process-group leader before `exec`. The parent verifies
`pgid == pid`. Linux signalling requires the registry-held pidfd to remain
valid and the stored identity to match. The unreaped direct child pins the
group identity during descendant cleanup.

Stdout and stderr use separate nonblocking pipes. Each lease has one combined
retention budget, bounded per-call drain work, saturating `seen` counters, and
explicit truncation flags. `poll` may return newly retained chunks through
bounded caller buffers; the registry never allocates in proportion to child
output. EOF and the post-reap drain deadline close inherited-pipe attacks.

## Public Simple capability

`OwnedProcessLease` is opaque outside
`std.nogc_sync_mut.io.process_ops`. Its private token words cannot be read,
formatted, serialized, compared, cloned, or constructed by application code.
The facade binds each lease to a private capability-registry entry. Copying a
Simple value does not mint another owner: consumption or collection revokes
the registry entry for every alias. No `from_fields`, token getter, or raw
cancel overload is exported.

`src/app/io` may re-export the opaque facade for compatibility. It must not
declare another runtime ABI or reconstruct a token.

## Platform policy

Linux with pidfd support is v2 `Supported`. Other Unix systems and Windows
return a typed `UnsupportedPlatform` start error until they have an equivalent
non-reusable process identity, process-tree containment, owner-serialized
termination, and exact reaping implementation. Falling back to PID-only kill,
shell `timeout`, detached threads, Job-less Windows processes, or best-effort
process enumeration is forbidden.

## QemuRunner relationship

`src/os/_QemuRunner/vm_adapter.spl` consumes only the Simple lease interface.
It retains the lease while QMP and serial operations run, polls without losing
output, requests cancellation on failure/timeout, waits for a terminal result,
and collects exactly once. QEMU does not gain a second process registry.

## Compatibility and migration

`rt_process_run_owned_bounded[_value]` remains ABI v1 initially. Its
implementation becomes `start -> wait -> result -> collect`, preserving the
19-field receipt and existing output behavior. `rt_process_owned_cancel_value`
remains temporarily for already-compiled callers but can affect only v1
synchronous registrations; new code cannot obtain its tuple. The raw
`rt_process_owned_terminate(pid, identity)` tombstone continues to return
false. After all callers use v2, remove the tuple-authorized cancellation ABI
in a separate compatibility release.

## Invariants

- INV-PROC-001: authority is the opaque random token plus registry binding,
  never a public numeric identity tuple.
- INV-PROC-002: one live token resolves to exactly one live generation.
- INV-PROC-003: a stale, forged, copied-after-collection, or cross-registry
  token cannot observe, signal, wait, or collect another process.
- INV-PROC-004: every accepted start reaches exactly one reap before slot reuse.
- INV-PROC-005: cancellation targets the verified process group and follows
  TERM/grace/KILL/reap in owner-serialized order.
- INV-PROC-006: retained output and work per poll are bounded independently of
  child output volume.
- INV-PROC-007: unsupported platforms fail before spawning.
- INV-PROC-008: a terminal result is immutable and collectible once.

## Consequences

The design enables interactive QEMU/QMP operation without weakening the
existing process-safety boundary. It adds registry state and ABI surface, and
Linux remains the only initially supported live provider. A native runtime
thread may drive no lease implicitly: progress occurs through poll/wait/cancel
calls, keeping ownership and test scheduling deterministic.

## References

- `src/runtime/runtime_process_owned.c`
- `src/runtime/runtime.h`
- `src/lib/nogc_sync_mut/io/process_ops.spl`
- `src/os/_QemuRunner/vm_process_lifecycle.spl`
- `doc/04_architecture/sosix_parallel_qemu_refactor.md`

