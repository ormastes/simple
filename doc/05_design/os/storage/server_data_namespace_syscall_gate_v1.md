# Server-data namespace syscall gate V1

## Outcome

The production C ABI already routes `open` and `rename` through SimpleOS
syscalls 30 and 44. The canonical file handlers now recognize the protected
`/srv/data` namespace after copying and normalizing each userspace path once.
They derive authorization only from the scheduler's current TCB and an Active
namespace-owner row whose DBFS root seal still revalidates. No PID, lifecycle,
lease, path policy, or mount identity is accepted from userspace.

Only `/srv/data/web` and `/srv/data/db` are grantable. Rename requires both
paths in the same exact subtree. Unauthorized access returns `EPERM`.
Authorized protected opens and renames currently return `ENOSYS` rather than
falling through to the direct FAT32 backend: MountTable positioned I/O can own
a DBFS virtual object, but the production fd table does not yet bind that
object to the landed OFD and transactional descriptor owners.

ABI 79 now returns the canonical global DBFS capability code only when the
current TCB has an exact Active namespace row and current mount facts. Other
tasks receive `Unavailable` even if DBFS is globally mounted.
The capability owner serializes a monotonic, never-wrapped publication epoch.
ABI 79 snapshots `(code, epoch)`, performs current-task/mount-seal validation,
then requires a second identical mounted snapshot. Clear/remount/publish ABA
therefore changes the epoch and returns unavailable. Checked-lock or epoch
exhaustion quarantines publication and also returns unavailable.

## Ordering and performance

Path bytes are copied and normalized once before capability and namespace
checks. Managed-path detection and fixed subtree policy are O(path bytes).
Current-task lookup and owner lookup are bounded scans; the owner has at most
64 rows. Mount-seal revalidation is serialized by the canonical VFS owner and
occurs without holding the namespace mutex. No payload or file data is copied
by this gate.

## Deferred descriptor binding

A later phase must atomically bind `g_vfs_positioned_open`'s virtual object to
an `OpenFileDescriptionRefV1`, publish that alias into the exact
`FdTaskLifecycleKeyV1` context, route read/write/sync/close through MountTable,
and revoke/close aliases before namespace and launch-grant teardown. Until all
rollback and close ambiguity paths are owned, protected opens remain fail
closed and no direct DBD DBFS adapter is authorized.
