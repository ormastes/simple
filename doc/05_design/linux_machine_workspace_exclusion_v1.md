# Borrowed Linux workspace exclusion v1

Status: **AUTHORED_NOT_RUN**. Source only; no ABI, native, runtime, Podman,
SPipe/docgen, fault-injection, latency, RSS or release qualification.

The selected contract is a typed factory in
`std.nogc_sync_mut.io.linux_machine_workspace_exclusion_v1`:
`linux_machine_workspace_exclusion_open_v1(storage, lease)` accepts an actual
`LinuxMachineStorageV1` and `WorkspaceStorageLeaseV1`. It exposes no caller
path, machine-writer reacquisition, raw store/lock getter or new runtime export.
The accepted installed-policy/storage files need no extension or circular
import. This new owner imports their existing typed port.

The caller retains the original storage and quota lease on every outcome.
Ready and CleanupRequired owners privately retain those same borrowed owners
and the actual native `FileLockOwnerV2`. This owner never closes machine
storage, releases or forgets the native quota lease, deletes workspace data,
changes administrative policy, or starts a provider process. Rejected means
no exclusion resource remains owned by this factory; callers still own their
original arguments.

Before every private registry entry, including close, use the genuine
process-lifetime Linux origin guard. It rejects inherited PID-namespace
collisions before reading copied registry state or releasing any inherited
flock. The source supports the same actual process leader thread and service
UID as its borrowed machine-storage owner. Fork, namespace changes or callback
reentry within one synchronous operation are unsupported; there are no hooks
or subprocesses in this owner.

## Native identity and fixed exclusion

`storage.policy_bytes_v1()` validates the actual private machine writer,
storage generation, administrative ancestry, service credentials, retained
process/namespace context and exact installed policy. Call it before and after
each native workspace probe, and on both sides of lock acquisition.
`workspace_storage_observe_v1(lease)` rederives actual native XFS project quota
identity and validates every immutable request field against that native lease.
Require a retained Linux XFS lease with its policy digest equal to the actual
machine policy and its full binding equal to the original typed request.

The existing native XFS receipt spells workspace identity as
`inode:<st_dev>:<st_ino>:<unsigned FS_IOC_GETVERSION generation>:<st_uid>`.
Parse that exact canonical shape with checked unsigned decimal bounds.
The lock identity hashes kind, actual device, inode and generation. Exclude
pool mount ID, UID, policy, quota number, hard-byte budget, path and guest mount
target: aliases of the same physical root must contend even if those other
metadata values differ. Keep full native lease binding separately and reject
changes during subsequent current checks. Unsupported native identity spelling
refuses; neither missing generation nor an unverified path becomes identity.

Use only `/var/lib/simple/container/workspace-<physical identity digest>.lock`,
under the same already validated private service-owned machine-state root.
The existing generation-bearing lock owner opens it with a zero wait and
retains partial acquisition resources. The machine writer is borrowed and
never reacquired. A fresh opaque slot/generation retains the lock before any
later fallible probe. Bound active exclusions to 32 and total process
generations to 4096; never reuse a canonical generation.

This is same-root exclusion among cooperating users of this exact canonical
lock. It is not all-mutator absence, migration continuity, workspace readiness,
quota release, an installed-profile proof, containment, an execution grant or
permission to launch. The higher provider owner must retain and recheck its
actual profile, parent, quota, containment and other admission capabilities.
A diagnostic snapshot cannot construct an exclusion owner or any grant.

## Current and cleanup contract

`current_v1()` returns only `machine_policy_digest`, `lease_binding_digest`
and `workspace_identity_digest`. It rereads the actual parent and native lease,
checks the actual lock generation is held, and compares against canonical
state. Failed current checks make the exclusion cleanup-only; they do not
silently refresh it to another policy or workspace.

`close_v1()` returns `{owner, closed, error}`. Only native Released or
ConsumedError clears the actual lock. ConsumedError is closed with a retained
diagnostic; it must never cause a numeric descriptor retry. Unknown, Retained
or Stale keeps the original exact lock owner and borrowed parents in the
cleanup capsule. A canonical record that already closed returns idempotent
closed state and its saved diagnostic, without touching a later generation.
Borrowed parents may be closed through their own aliases by their actual owner;
then `current_v1()` refuses, while this capsule still owns its workspace lock
and can retire only that lock. No cleanup result proves workspace absence.

Native probes are bounded admission checks, not per-byte IO or a recursive
workspace scan. They deliberately revalidate mutable native authority; no
pathname cache, unbounded retry, tree scan, subprocess or additional journal is
introduced. Cost and performance remain unmeasured and unqualified.

## Authored verification

The actual fixture spec reads the two fixed administrator profiles, obtains a
real XFS project quota lease, and borrows the actual fixed state writer. It
checks native lease/policy correlation, real competing lock rejection,
borrowed-parent and quota preservation, and an old closed alias leaving a new
canonical generation locked. The quota lease remains retained for ordinary
reconciliation; the fixture does not delete data or claim native release.

Native bind-mount alias fixtures, process/fork/namespace faults, mutation during
acquisition, stale/unknown releases, and forced numeric descriptor reuse remain
**NOT_RUN / NOT_COVERED**. The manual is authored, not generated evidence.
