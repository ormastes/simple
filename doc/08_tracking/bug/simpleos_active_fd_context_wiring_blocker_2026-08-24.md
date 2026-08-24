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
