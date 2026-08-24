# SimpleOS FD compatibility runtime wiring blockers

## Requested invariant

The canonical `fd_compat_owner_v1` facade must own descriptor mutation for the
current `{task_id, lifecycle_generation}`. Legacy `fd_table` arrays may remain
temporarily for backend I/O, but only as derived mirrors. Fork must reserve FD
inheritance before publishing a child TCB, and dup2, exec, and exit must retain
and discharge every opaque backend-close receipt.

## Current blockers

1. Most scheduler task constructors publish `lifecycle_generation: 0`; the
   canonical `FdTaskLifecycleKeyV1` deliberately rejects generation zero.
   `sched_exec_image_impl` also resets an existing task generation to zero.
2. The canonical facade has no operation for installing an opened file, pipe,
   socket, device, FAT32 object, or other backend-bound descriptor, and it has
   no ordinary close operation. Only the three synthetic serial descriptors
   can currently be represented through the facade.
3. `FdDescriptorSnapshotV1` omits the generational backend binding and legacy
   routing fields needed to derive `fd_types`, `fd_ports`, and `fd_objects`.
   Rebuilding the arrays from this snapshot would silently turn non-stdio
   descriptors into unusable or incorrectly routed descriptors.
4. Legacy read/write/seek paths mutate legacy offset and status storage. Until
   a mirror publication API exists, routing dup/fcntl through the canonical
   facade would create two independently mutable representations immediately.
5. Scheduler fork currently publishes the child TCB before
   `fd_prepare_fork_to_task` runs, ignores FD-inheritance failure, and has no
   descriptor rollback path. Canonical fork requires reserve-before-publication
   followed by exact commit or rollback.
6. Exec and exit currently close descriptors through backend-aware legacy loops;
   scheduler exit can close them a second time. The canonical opaque close
   receipts cannot be correlated with those closes or completed honestly yet.
7. Syscall dup/fcntl helpers derive only an ambient numeric `fd_current_task()`;
   they do not receive the scheduler-authoritative lifecycle generation.

## Required safe sequence

1. Allocate a nonzero lifecycle generation for every TCB before publication;
   preserve it across exec and expose one scheduler-authoritative current key.
2. Add canonical open-install and ordinary-close transactions carrying a real
   generational backend binding for every supported descriptor kind.
3. Add a bounded mirror snapshot that includes immutable backend routing plus
   canonical shared offset/status, and publish it atomically into the active
   legacy table without resetting unrelated task contexts.
4. Route open/close and offset/status mutations through the canonical owner;
   keep legacy backend I/O as a consumer of the derived mirror only.
5. Change fork to reserve canonical inheritance before child publication,
   commit after all other prepublication owners succeed, and roll back all
   reservations on failure.
6. Add one close-receipt dispatcher that resolves the exact backend, performs
   at most one legacy backend close, then commits or marks the canonical close
   indeterminate. Use it for dup2, exec, and exit.
7. Only then switch dup/dup2/fcntl/exec/fork/exit syscall entrypoints to require
   the explicit current lifecycle key and remove ambient task-id mutation.

## Unsafe draft decision

No runtime wiring was applied. Falling back to the legacy owner for descriptors
missing from the canonical context would violate the single-owner invariant;
failing those operations would regress existing file/pipe/socket behavior.
Both outcomes are rejected.
