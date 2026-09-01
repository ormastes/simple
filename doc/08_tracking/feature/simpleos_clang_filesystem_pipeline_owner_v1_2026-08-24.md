# SimpleOS Clang filesystem pipeline owner v1

Status: IN PROGRESS — static implementation only; unverified by explicit user direction.

Implemented a bounded pre-launch reservation owner that binds authenticated
installed Clang/LLD records, exact x86_64/AArch64/RV64 target identity, one
filesystem root, a declared task lifecycle identity, and an exact eight-token,
non-delegable source/CWD/object/output pouch. It explicitly does not establish
current-TCB liveness. A dispatched operation has no success-release path in v1,
so its slot remains unavailable; an explicit unknown-outcome transition retires
the slot permanently while retaining its output-path exclusion.
DBFS and NVFS are structurally admitted. FAT32 remains rejected until the FAT
owner provides a canonical object/name identity that closes case, short-name,
and Unicode alias collisions.

Still required before completion:

1. Wire live MountTable/OFD-derived capabilities into the owner rather than a
   caller-created compatibility pouch.
2. Connect dispatch to the guest process executor without PATH lookup or host
   fallback.
3. Consume authenticated compile and link acknowledgements, then the loader's
   execution receipt, with exact artifact digest continuity.
4. Retain per-target QEMU evidence for compile, link, filesystem reopen, run,
   `Hello World\n`, exit zero, bounded output, and teardown.

No runtime, target, build, test, SPipe, benchmark, optimizer, or bootstrap
claim is made by this change.
