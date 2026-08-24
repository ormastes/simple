# SimpleOS active FD context wiring blocker (2026-08-24)

The legacy `os.kernel.fd_table` stores one process-global active descriptor
mirror. Callers switch it with `fd_activate_task`, and fd/open/dup/close plus
backend helpers do not accept task lifecycle or dispatch authority. Concurrent
syscall dispatch can therefore observe or mutate another task's active table.

`active_fd_context_owner_v1.spl` now provides the bounded synchronized lease
contract, exact task/lifecycle/context generations, fork child binding, cleanup
reservation, and retry retention. It intentionally does not call the legacy
table or claim production integration.

Remaining production work must preserve all public C ABI signatures while
changing internal Simple adapters as one coherent cut:

1. Derive the exact lifecycle generation from the caller TCB at every file,
   process, pipe, socket, select/poll, and shim dispatch entry.
2. Begin one lease, activate/load the matching table under that held mutex, and
   pass the lease to every descriptor/open/dup/close/backend-close operation.
3. Persist the table and end the lease on every success and error return.
4. Bind fork inheritance to the child TCB lifecycle and exit cleanup to the
   existing scheduler cleanup reservation transaction.
5. Remove direct `fd_activate_task` and `fd_current_task` authorization uses.

Partial conversion is unsafe: an unleased legacy caller can still race the
single active mirror. No runtime verification was run by instruction.

## Production-migration audit (2026-08-24)

A follow-up static audit rejected a partial adapter migration.  The required
cut is wider than `fd_activate_task`: mutable descriptor operations are called
directly from `fd_io.spl`, `pipe_compat.spl`, `socket_compat.spl`,
`ipc/syscall_file.spl`, `ipc/syscall_process.spl`, and the exported file
syscall shim.  A lease held only by `syscall_handler` would therefore leave
the direct C leaves and scheduler cleanup path unleased, while a module-global
"current lease" would be another copyable ambient authority and would defeat
the owner contract.

The coherent migration must add an internal, package-private dispatch carrier
that contains the opaque `ActiveFdContextLeaseV1` and thread it explicitly
through all of the following operations:

- activation/load/persist of the legacy task table;
- descriptor lookup and offset/status/readiness mutation;
- open/allocation/set, pipe and socket publication;
- dup, dup2, fcntl duplication, close-on-exec, and fork inheritance;
- local close plus the VFS, pipe, and socket backend-close branches;
- task cleanup retry and final context retirement.

The public `spl_handle_*` C signatures remain unchanged.  Each exported
operation leaf must obtain the current TCB's exact nonzero lifecycle
generation, begin one dispatch lease, call a lease-bearing internal
implementation, and finish it on every return.  ARM64 currently invokes
`spl_shim_file_capability_check` and `spl_handle_file_*` as two separate
C-to-Simple calls.  Those calls cannot safely share a scoped lease.  Descriptor
authorization must therefore move into the operation leaf (leaving the
precheck path-only/non-descriptor), or the architecture dispatcher must call
one combined internal bridge.  Two independently leased calls do not close
the check/use race.

Fork also needs a transactional rollback that the current
`fd_prepare_fork_to_task(child_owner)` API cannot express.  The legacy
`fd_context_*` rows themselves are keyed only by task ID, so they first need a
nonzero lifecycle-generation column and exact-key lookup; protecting those
rows with a separately generation-keyed lease does not prevent reused-ID
aliasing.  Scheduler clone must then split into prepare and publish: reserve
the child owner/context with `{child.id, child.lifecycle_generation}`, copy and
increment aliases, and either commit both publications or abort the reserved
context and undo every open-file-description increment.  The existing
`active_fd_context_prepare_fork_v1` has no commit/abort receipt, and the current
scheduler publishes the child before FD inheritance, so neither existing API
can provide that transaction.

Exit/reap currently call `posix_close_task_fds_with_backends(task.id.id)` and
then independently transition the TCB to `Zombie`.  Production cleanup must
take the full lifecycle key and reserve cleanup while the TCB is still live.
The owner must issue an opaque generational cleanup receipt, consume it for
each retry or terminal retirement, and invalidate every copied receipt after
use.  The current `finish_cleanup(false) -> bool` plus
`resume_cleanup(key)` reconstructs authority from a bare key and is therefore
not sufficient.  A backend failure must retain cleanup-only retry authority
and leave the task explicitly non-Zombie.  Only successful terminal cleanup
may retire the active context and permit the Zombie transition.  Reaping may
consume the terminal receipt, but must never reconstruct authority from a
Zombie TCB.

Finally, `ActiveFdContextLeaseV1` is opaque but remains a value-copyable Simple
record.  Production dispatch needs owner-side single-use nonce consumption so
mutation, finish, or cancellation makes all copies stale.  A package-private
carrier does not itself establish linearity.

Safe prerequisite-only work can land before the coherent cut without changing
the production path: lifecycle-key the legacy rows; add owner-issued
fork prepare/commit/abort receipts and cleanup retry receipts; or consolidate
the C capability/operation bridge.  Such work must continue to describe the
legacy path as unsynchronized until every direct caller is migrated.

No source adapter was landed in this audit: without the complete signature
cut, any converted subset would misleadingly appear synchronized while legacy
callers could still race it.  No tests, builds, SPipe, benchmarks, optimizer,
bootstrap, or other verification were run by instruction.

## Owner primitive progress (unverified)

The bounded owner now has package-private single-call operation authorization
that rotates the dispatch nonce before returning, opaque fork
prepare/publish/abort receipts, and opaque cleanup retry receipts whose nonce is
consumed and rotated at resume. Prepared fork children cannot be dispatched,
and copied predecessor leases or receipts become stale owner-side.

This does not complete the production cut. The legacy `fd_context_*` storage is
still task-ID keyed, FD/OFD refcount copying still lacks rollback, and direct C
and internal callers still use ambient `fd_activate_task`. Those pieces must be
migrated together; wiring only these owner primitives would remain unsafe.
