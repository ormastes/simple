# Kernel execution owner: canonical boot-transfer blocker

Status: blocked at the construction boundary; no production capsule is landed.

## Why phase 1 was reverted

A package-private constructor taking `Scheduler`, `MountTable`, and
`ExecutableAuthorityRegistryV1` values cannot by itself prove unique ownership.
A process-wide “already initialized” flag prevents a second capsule, but it
does not invalidate Scheduler or MountTable aliases retained by the boot caller.
Calling such a capsule canonical would therefore be stronger than the actual
Simple ownership semantics.

The capsule must land together with the production boot transfer. The boot
root that currently creates and retains the scheduler and mounted filesystem
must move those exact live values into the capsule and stop using or storing
the originals. No SSH, web, database, loader helper, syscall shim, interrupt
owner, or fixture may create a replacement `Scheduler.new*`, `MountTable.new`,
or reopen the loader registry to service a launch.

## Required owner and port protocol

`KernelExecutionOwnerV1` is the sole mutable owner of:

- the canonical live `Scheduler`;
- the canonical mounted `MountTable`;
- the already-initialized `ExecutableAuthorityRegistryV1` coordinate;
- a bounded service-port table and all future launch transactions.

Construction is a boot-only transfer operation, not a generally callable
factory. The boot composition must return a replacement root state containing
the capsule instead of returning the three inputs alongside it. Review must
inspect every post-transfer use and prove that no old scheduler/table binding
remains reachable.

Services receive only `KernelExecutionServicePortV1`. A port is an opaque
`{owner_epoch, slot, generation, nonce}` coordinate whose private owner slot
also binds service kind and nonzero service-instance identity. It is routing
authority only: it cannot contain or mint an executable token, pathname,
Scheduler, MountTable, registry owner, verifier result, or caller assertion.

The table is fixed-capacity and generational. Issue, snapshot, revoke, reuse,
drain, and stale rejection execute in one named serialization domain. Either
capture and enforce the canonical boot OS-thread identity or use a checked
mutex with poison-on-unlock failure; do not leave the choice implicit. A scan
retires generation-exhausted slots and continues looking for later reusable
slots. Drain revokes every active port before publishing terminal owner state.

Every future execution operation is a mutable method on the retained capsule.
Early rejection, loader reservation failure, mapping rollback, scheduler
publication, and close-quarantine branches must all leave the mutated Scheduler
and MountTable in that same capsule. No operation returns those owners for a
caller to accidentally discard.

## Exact resume files

Inspect and update the actual architecture boot composition that owns the
selected live scheduler and mounted table; do not choose a fixture merely
because it is easier to construct. Start from:

- `src/os/kernel/scheduler/scheduler_types.spl`
- `src/os/kernel/scheduler/scheduler.spl`
- `src/lib/nogc_async_mut/fs_driver/mount_table.spl`
- `src/os/kernel/loader/executable_authority_registry.spl`
- `src/os/kernel/loader/executable_admission_pipeline.spl`
- `src/os/kernel/abi/syscall_shim.spl`
- `src/os/kernel/arch/arm64/` and the ARM64 production boot entry selected by
  the repository's current boot composition
- `src/os/apps/sshd/sshd.spl`
- `src/os/apps/sshd/ssh_session.spl`
- `src/os/apps/sshd/ssh_session_lifecycle.spl`
- `src/os/apps/sshd/arm64_ssh_request_context_owner.spl`
- `src/os/kernel/loader/arm64_ssh_joint_launch_validation.spl`
- `src/os/kernel/scheduler/scheduler_executable_adoption.spl`

New implementation files, once the boot transfer is proven:

- `src/os/kernel/execution/kernel_execution_owner.spl`
- `test/01_unit/os/kernel/execution/kernel_execution_owner_lifecycle_spec.spl`
- an ARM64 production boot integration spec beside the selected boot entry
- `doc/05_design/os/kernel_execution_owner_v1.md`

## Resume order and acceptance evidence

1. Identify the one production ARM64 root that simultaneously owns the live
   scheduler and mounted table. Record all aliases and consumers.
2. Change its result/state shape so construction consumes those owners and the
   root retains only `KernelExecutionOwnerV1`. Remove every post-transfer use
   of the original bindings in the same change.
3. Initialize the loader registry once at boot and transfer only that exact
   coordinate. Repeated initialization or configuration mismatch must fail.
4. Add the bounded serialized port owner. Cover actual issue → snapshot →
   revoke → stale rejection → reuse with a higher generation, duplicate service
   identity, full capacity, exhausted-slot skip, cross-domain rejection or
   mutex poisoning, drain, and second-capsule rejection.
5. Review the boot diff for alias survival before adding any launch API. Static
   search is supporting evidence; the authoritative evidence is the boot state
   type and call graph showing that only the capsule remains reachable.
6. Only after that review passes, add the two-phase ARM64 SSH prepare/commit
   protocol. Do not combine phase 1 with a path-only compatibility launcher.

Resume is blocked if the active ARM64 boot path does not yet converge scheduler
and MountTable ownership. In that case, first refactor boot composition; do not
simulate uniqueness with a singleton boolean, a new bootstrap scheduler, an
empty mount table, a fixture, or copied returned ownership.

This handoff is design/tracking only and carries no runtime verification claim.
