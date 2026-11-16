# Installed Linux machine policy and storage

Status: **AUTHORED_NOT_RUN**. No compiler, linker, native fixture, Podman,
SPipe/docgen, performance, release or deployment qualification is claimed.
The admitted self-hosted runtime is absent and the existing execution budget
is exhausted. This lane adds only new Simple library leaves and authored specs.

## Scope and trust

`linux_machine_policy_open_v1()` has no caller parameters. The first supported
deployment uses one administrator-configured nonroot service UID for the
physical machine budget and its rootless Podman engine. The actual real and
effective UID must match and be positive. Saved and filesystem UIDs/GIDs must
match those observed credentials, and permitted, effective, inheritable and
ambient capability sets must be zero. Root callers and elevated or ambiguous
credentials refuse. Other service UIDs do not get private fallback ledgers.

The administrator installs root-owned `/etc/simple/container` ancestry and
`machine-policy.sdn` with exact regular-file mode `0644` or `0444`. Every
ancestor, including `/`, is root-owned and lacks group/world write permission;
symlink components refuse. The administrator separately delegates
`/var/lib/simple/container` to the actual service UID with exact mode `0700`.
Its ancestors through `/var/lib/simple` remain protected and root-owned.
The fixed `database-wal` and `objects` children must already exist, be real
directories and have that same service ownership and `0700` mode. No owner
installs directories, changes ownership, elevates or repairs provisioning.

Root and privileged host administrators remain trusted. Compromise of the
dedicated service UID on the host is outside this first deployment model;
contained agents must not access this parent process, policy tree or state
tree. A hostile same-UID isolation boundary is not claimed. The authority
consumer must decode the selected protected Linux provider policy and compare
its existing `expected_uid` pin to `actual_linux_process_context_v1()` before
transferring the reader. IO imports no async provider codec. Exact policy bytes,
including mode, provider identities, physical identity and budget, bind the
single fixed ledger; an existing different binding refuses without replacement.

## Native process and namespace provenance

Only Linux x86_64/aarch64 libc ABI layouts are authored. The actual process
leader thread (`gettid() == getpid()`) is required before mutable owner state
is touched. Every later operation requires that same PID/TID and UID/GID.
Fork-inherited owners and worker-thread calls refuse; there is no reinitializing
an inherited owner table or broad thread support claim. Active owners are
bounded to 32, and generation slots are never reused within the process.

The small `linux_machine_process_origin_v1` owner retains one genuine procfs
descriptor and 1024 bytes for the entire process lifetime, including after all
policy/storage capsules close. Every registry entry, factory and close checks
that descriptor's filesystem/mount identity and actual `self` and `thread-self`
links against libc PID/TID. The magic links themselves must be procfs symlinks
on the same device and returned mount ID; bind-mounted substitutes refuse.
This detects fork into a nested PID namespace even when its numeric PID/TID
coincide with the parent. Origin resources remain owned by the process guard
until kernel process teardown; no closed descriptor number is reused as origin
evidence. Failure permanently quarantines this bounded guard and prevents
later factories or cleanup from reviving inherited registry state.

Open `/proc` as a retained no-follow directory and verify `PROC_SUPER_MAGIC`.
Its `self` link must name the actual libc PID. Numeric process, task, current
thread, namespace directory, maps, status, stat and boot-ID children must have
the same actual procfs device and returned `STATX_MNT_ID`. Missing mount-ID
mask bits refuse; zero-initialized output is never treated as evidence.
This rejects bind-mounted foreign-task map substitutions. The current thread's
UID and GID maps must each contain exactly one full identity mapping
`0 0 4294967295`. These checks reject unprivileged nested user namespaces.
Identity namespaces created by a privileged host administrator remain within
the explicitly trusted administrator boundary; an `ioctl` permission error is
never interpreted as initial-user-namespace proof.

Retain current-thread `ns/user`, `ns/mnt` and `ns/pid` handles after opening
through the verified no-follow namespace directory. Verify NSFS filesystem
kind and each `NS_GET_NSTYPE`. Retain the `NS_GET_USERNS` returned descriptor
before validation and require its identity to equal the pinned user namespace.
All handles and their named ancestry are rechecked before and after admitted
IO. Actual process and task start ticks and genuine procfs kernel boot ID bind
the diagnostic identity digest together with credentials and namespace
identities. Snapshots are data and cannot construct any owner or principal.
The canonical principal string is `linux:uid:<decimal>`.

## Existing storage and ownership

The implementation reuses `retained_directory_open_trusted_v1` and retained
regular-file reads for bounded unchanged-file verification. Its additional
private descriptor chain strengthens the generic root/euid walk into strict
root-owned ancestry and retains every administrative ancestor. Every opened fd
is stored in its cleanup capsule before another fallible check.

`MachinePolicyOwnerV1` and `MachineStorageOwnerV1` select their platform inside
the library. Their private variants expose no raw store, root, descriptor or
native owner getter. The policy reader exposes bounded bytes, current Linux
context/principal data, selected backend, one transfer and close. Rejected
transfer retains the reader. Ready or CleanupRequired transfer consumes it
into storage. Transferred reader aliases cannot read, mint principal snapshots
or close resources behind the storage owner.

The storage ports are `policy_bytes_v1`, `physical_capacity_v1`,
`bind_policy_v1`, `wal_head_v1`, `wal_revision_v1`, `wal_segment_v1`,
`wal_commit_v1` and `close_v1`. Physical capacity samples checked libc online
CPU and physical-page totals. It is hardware observation, not reservation
evidence or cgroup availability. The authority must separately match the real
provider observation and impose its installed budget on that physical scope.

Hold the existing generation-bearing `FileLockOwnerV2` at the fixed
`machine-writer.lock` for the entire storage lifetime. Root-protected ancestry,
private service-owned children, the trusted service UID and exact retained
ancestry rechecks surround the existing `wal_segmented` nil-store path. The
shared WAL's immutable objects, canonical revisions and compare/publish remain
unchanged; this is not a new journal or a Windows store disguised as Linux.
Path operations are admitted only within this documented same-UID trust model.

A missing `CURRENT` may be observed as an empty head. It never proves previous
charge absence. `wal_commit_v1` refuses an empty parent with
`machine-container-migration-fence-unavailable`; no initial or replacement
machine charge is authorized by this storage owner. The separate authority and
supervisor migration-fence owner must establish real continuity before any
future new-charge path. Mutation failure quarantines the capsule and retains
its writer and backing handles until cleanup.

Close preserves unknown or retained lock owners and their backing directories.
For Linux descriptor closes, the slot is consumed before one native close call;
even `EINTR` must not retry a numeric fd that the kernel could reuse. After all
resources are consumed, any observed close error returns `consumed-error`,
distinct from `released`; a copied closed alias returns `stale`. No caller may
interpret `retained` as permission to drop the capsule.

## Fixed supervisor profile extension

`read_supervisor_profile_v1()` lazily reads only
`/etc/simple/container/supervisor-profile.sdn` through the same policy reader.
The child descriptor is retained before validation, has the same strict
root-owner/file-mode/size rules, and pins exact unchanged bytes. Policy,
process, namespace and ancestor checks surround each read. An absent profile
does not block ordinary policy readers; requesting an absent or invalid profile
quarantines that reader. The supervisor worker retains the actual opaque
reader through its lifetime. Profile bytes alone are closed administrative
activation metadata and cannot grant a supervisor owner or migration fence.

The likewise zero-argument `read_workspace_profile_v1()` lazily reads only
`/etc/simple/container/workspace-profile.sdn` using the same retained child,
root-owner/mode, process, ancestry and exact hash rules. IO does not decode
provider workspace policy. The actual provider workspace owner retains this
opaque reader; copied profile bytes alone cannot authorize workspace access,
quotas, a descriptor handoff or any provider effect. Missing profiles do not
block an ordinary policy reader unless their specific port is invoked.

## Authored verification and limits

`test/03_system/tools/linux_machine_storage_v1_spec.spl` requires a disposable,
administrator-prepared actual installation. It checks actual identity/provider
UID correlation, reader transfer, exact bytes binding, competing native writer
rejection, hardware totals, migration refusal without head mutation and closed
aliases. Its manual is authored, not generated. Native negative fixtures for
bind-mounted foreign maps, context/fork changes, unsafe ancestry, unknown lock
release, short writes and close-error descriptor reuse remain **NOT_RUN**.
Libc symbol/link admission, genuine OS behavior, generated manual quality,
startup latency, RSS, and production execution are unqualified.
