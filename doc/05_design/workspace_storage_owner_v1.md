# Native workspace storage owner

Status: source checkpoint with one focused Linux negative native check (73
checks, build/run exit 0). Positive quota enforcement, Windows execution, Simple
SSpec, generated manuals, and full host integration remain unqualified.
This is the storage-provider part of the existing orchestrator requirement. The
host remains the sole writer of reservation state in its existing V2 operation
journal; this module adds no journal and cannot discharge a host reservation.

## Boundary agreed with the host owner

`std.nogc_sync_mut.storage_roots.workspace_storage_owner_v1` owns native leases.
`WorkspaceStorageRequestV1` binds a provider kind, protected parent, one workspace
leaf, expected native pool and workspace identities, quota identity, requested
hard bytes and the host policy digest. `WorkspaceStorageReceiptV1` reports those
identities, actual enforced bytes, measured usage, and a canonical binding digest.
Observed inode usage is not a promised inode limit.

The operations are admission, observation, recovery, and release-if-absent.
Recovery reobserves an existing native lease or performs fresh native admission;
copied receipts are never capabilities. A recovered lease retains cleanup
authority even when observation fails; callers must obtain a successful current
observation before treating it as readiness. Admission pins directory/volume handles before
returning a generation-bearing lease. A bounded in-process registry is handle
ownership, not another capacity ledger. Host restart uses its retained request
and native re-observation, not stale process-local tokens. Recovery after process
restart when the workspace has already disappeared is conservatively pending:
this checkpoint cannot reconstruct an exact released native owner in that case.

Before admission the host must persist the immutable request and capacity charge
under its existing operation writer. Missing capability or mismatched identity
rejects before workload launch. Every writable surface charged to the request
must be contained by the admitted storage scope; a workspace quota does not bound
container image layers, another mount, logs outside the scope, or host metadata.

## Linux

The first concrete capability is an administrator-provisioned XFS project quota.
Read the project ID and inheritance flag with `FS_IOC_FSGETXATTR`; use
`quotactl_fd` with `Q_XGETQSTATV` and `Q_XGETQUOTA` on the pinned filesystem.
Require project accounting **and enforcement**, an exact nonzero hard limit,
and the expected project identity. XFS quota block values are 512-byte units.
Unsupported kernels, filesystems, permissions, or disabled enforcement reject.
No quota-setting, mount, chmod, or shell operation is performed by this owner.

The trusted administrator exclusively assigns the quota project to the workspace
and provisions inheritance throughout any existing tree. Workload policy must
deny quota/ownership reconfiguration and access to uncharged writable scopes.
Project quotas constrain charged allocated blocks; the host must not describe
this as a logical-file-length or arbitrary metadata quota.

Pool identity includes the actual filesystem/device/mount instance; workspace
identity includes that pool and native inode identity. Host boot/provider fences
remain required because mount/inode numbers alone are not timeless identities.

## Windows

Windows is a separate capability, not an emulation of Linux project quotas.
The implemented admission capability is an administrator-provisioned dedicated volume,
identified by its actual volume GUID and file identity, with its native length
read through `IOCTL_DISK_GET_LENGTH_INFO`. Requested capacity must match that
fixed volume envelope; free space is a separate observation. Host policy must
bind exclusive use of this volume and forbid workload volume-management rights.
Native NTFS allocated-cluster usage is reported; inode usage is explicitly `-1`
(unavailable), never zero. The provider checks a protected root DACL and exact
workspace file identity. These are snapshots under the installed administrator
policy, not proof against an administrator concurrently changing that policy.

Windows release currently returns unsupported and retains all handles and host
charges. Workspace absence or locking the volume cannot prove that renamed,
recycled, or other dirty data is gone. The required next lifecycle slice must
consume explicit host retention/deletion authority and verify exact immutable
volume identity before any disposal or independently proved empty-volume release.
No destructive disposal route is implemented or qualified by this checkpoint.

NTFS per-user quota bytes count logical user streams and exclude some metadata;
they are not substituted for a physical volume bound. `GetDiskFreeSpaceEx` or a
recursive directory byte count is never evidence of a hard quota.

## Cleanup and retained charges

The initial owner performs no destructive workspace cleanup. There is currently
no native-verifiable host cleanup-authorization token to consume; inventing a
copied `absence=true` flag would not supply one. A separately authorized host
cleanup must prove workload absence and remove only its exact owned scope.

Linux `release_if_absent` independently checks disappearance of the pinned exact
inode, closes only that already-unlinked descriptor, and requires actual project
block and inode usage both zero before closing the remaining ownership handles.
It returns evidence for the host's correlated journal transition, never a ledger
mutation. Existing, dirty, replaced, nonempty, unreadable, or uncertain scopes
remain charged. TTL expiry, process exit, unlink success alone, and increased
free space cannot discharge storage. Administrative quota settings remain intact.

## Required evidence

Focused negative tests must use real native paths and verify no mutations on
unsupported filesystems, symlink/replacement, identity/limit mismatch, and stale
tokens. Positive Linux acceptance requires a real admin-provisioned enforced XFS
project, independent limit readback, a write that reaches the real quota boundary,
dirty preservation, and retained-charge cleanup/recovery. Windows needs its own
protected-volume identity, over-capacity and cleanup evidence. Missing facilities
are BLOCKED/NOT_RUN, never passing skips. Simple specs and mirrored authored
manuals remain distinct from actual native execution and generated docgen.

## Interface sources

- [Linux quota UAPI](https://github.com/torvalds/linux/blob/master/include/uapi/linux/dqblk_xfs.h)
- [Linux quota operations](https://github.com/torvalds/linux/blob/master/fs/quota/quota.c)
- [Windows volume length control](https://learn.microsoft.com/en-us/windows/win32/api/winioctl/ni-winioctl-ioctl_disk_get_length_info)
- [Windows disk quota accounting](https://learn.microsoft.com/en-us/windows/win32/fileio/disk-quota-limits)
