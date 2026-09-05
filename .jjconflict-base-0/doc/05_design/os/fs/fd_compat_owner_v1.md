<!-- codex-design -->
# Canonical FD Compatibility Owner V1

## Scope

`os.kernel.fs.fd_compat_owner_v1` is the only planned compatibility boundary
above `FdTableDescriptorOwnerV1` and `OpenFileDescriptionOwnerV1`. This phase
owns boot initialization, explicit lifecycle-key binding, stdio, snapshots,
flags/status, dup/dup2, and fork/exec/exit transactions. It deliberately does
not call the legacy FD table, syscalls, scheduler, VFS, FAT32 side tables, or
backend I/O.

## Ownership and lock order

The facade owns its checked mutex, canonical bound-key list, and 64 lifecycle
transaction slots. Its lock order is strictly:

```text
FD compatibility owner -> descriptor owner -> OFD owner
```

Backend dispatch and scheduler mutation occur only after a returned receipt,
when every owner lock is released. No lower owner calls back into the facade.
Unlock failure or an ownership inconsistency permanently quarantines the
facade. A committed mutation/lifecycle result still returns its receipt if the
final facade unlock fails, marked incomplete with `facade-unlock-failed`, so
opaque backend-close ownership is never replaced by a plain error. A prepare
unlock failure cancels the just-created facade reservation while the failing
mutex contract still leaves the current thread as owner; fork also rolls back
its lower descriptor reservation. Failure of that rollback quarantines and is
reported as an ownership failure.
Lower owners obey the same committed-unknown rule: post-mutation OFD unlock,
descriptor unlock, reservation cleanup, and context-destroy failures return
all close-begin receipts. Exit also forwards those receipts if bound-key
removal fails after the descriptor context has been destroyed.

## Boot and stdio capacity

Boot initialization is one-way and idempotent after success; there is no reset.
The immutable boot context is `{task_id: 0, lifecycle_generation: 1}`. It owns
three distinct serial OFDs: fd 0 is read-only, while fd 1 and fd 2 are
write-only. Every bound task is created by a descriptor-owner fork of this
template and therefore retains the same three OFDs rather than allocating
three more OFD slots.
Consequently serial status flags are shared by all initially bound tasks, just
as they are across fork aliases; serial cursor state is not path/file data.

At the fixed 256-context limit, stdio consumes exactly three OFD slots and at
most 256 references per stdio OFD. This stays far below the u32 reference-count
limit and leaves 253 OFD slots for later opened objects. The boot key is never
mutable or destructible through the facade. Task zero with any other lifecycle
generation is rejected.

## Explicit task authority

Every operation carries `FdTaskLifecycleKeyV1`; there is no process-global
active task. The facade records each key it bound. A descriptor-owner context
that exists without a matching facade binding is an ownership collision and
quarantines initialization/binding rather than being adopted. Numeric task-ID
reuse is harmless because the u64 lifecycle generation participates in every
identity check.

An ambiguous lower-owner post-mutation unlock failure also quarantines the
facade. The lower descriptor owner is already permanently quarantined by that
condition, so a possibly published but unbound context can never be adopted or
used; the system leaks bounded authority rather than guessing publication.

## Transactions

- Dup and dup2 reserve and commit through the descriptor owner under one facade
  call. Dup2 returns any displaced close-begin receipt.
- Fork prepare reserves the complete parent descriptor snapshot. Commit
  publishes the child context and bound key; rollback releases all retains.
- Exec prepare freezes the context mutation generation and CLOEXEC descriptor
  numbers while marking the task lifecycle reserved. Commit revalidates the
  generation and closes only those aliases. Partial failure returns every
  issued close receipt, marks the result incomplete, and quarantines.
- Exit prepare reserves the task lifecycle. Commit destroys and unbinds the
  context, forwarding complete or partial owner receipts. Rollback simply
  releases the lifecycle reservation.

Facade mutations reject while their task participates in a lifecycle
transaction. Direct calls to lower package-private owners are forbidden once
the adapter is wired.

## Deferred wiring

The next phase may adapt legacy fd-table/syscall entrypoints only after it can
consume every returned close receipt outside owner locks and validate real
generational backend bindings. This phase makes no runtime or backend-close
claim.

Sidecar lanes: N/A; this is one canonical mutation owner. Merge owner: root.
Final reviewer: independent normal/highest-capability static review.
