# Fail-closed executable byte reads

Requirement: REQ-VFS-EXEC-READ-001. Executable source:
`test/01_unit/os/kernel/security/executable_read_spec.spl`.

Status: executable scenarios authored; admitted runner and QEMU evidence are
pending. This manual is maintained prose, not a generated execution receipt.

1. Reject every nonboot read without an exact mounted-object binding. Missing
   contexts and kernel sentinels do not bypass this unavailable interface.
   Only the explicitly separate boot predicate accepts the kernel context.
2. Give a task FileRead and FileExec only for `/bin/simple`. Requests using that
   spelling, `.smf`, `/sys/apps/simple` and FAT32 spellings must all return the
   object-binding-required error without backend/cache access. This closes the
   reviewed alias-identity mismatch; it does not authorize any nonboot object.
3. Keep the same denial for a tokenless ambient-full compatibility pouch.
4. Plan PATH names without querying VFS and filter hostile components.
5. Pin production wiring: the public nonboot seam delegates only to the
   explicit unavailable result; neither policy nor shell planner imports a
   byte backend. The removed callerless API must remain absent.

The scenarios do not prove a successful nonboot read, mounted filesystems,
executable caches, authenticated scheduler adoption or guest PATH isolation.
Correct nonboot reads require a future mounted-object binding throughout
authorization and reading. Admitted unit and SimpleOS QEMU acceptance remain
required before closing the bug.
