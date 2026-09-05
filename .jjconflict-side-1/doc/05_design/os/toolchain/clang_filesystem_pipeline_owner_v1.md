# Clang filesystem pipeline owner v1

Status: implemented production prerequisite; runtime wiring and execution evidence remain open.

The owner in `src/os/kernel/loader/clang_filesystem_pipeline_owner_v1.spl`
prepares one guest-native Clang/LLD pipeline on x86_64, AArch64, or RV64. It
does not run a compiler and cannot promote a hello-world result.

## Authority boundary

- `/usr/bin/clang` and `/usr/bin/ld.lld` must resolve through the sealed,
  signature-verified installed-artifact catalog for the exact platform target.
- The structural request carries a nonzero task lifecycle/exec identity and
  every supplied capability token must name that task. Current-TCB liveness is
  deliberately not inferred and remains a scheduler integration requirement.
- The pledged, non-delegable pouch must contain exactly eight grants: exact
  clang/LLD executable paths, exact source and working-directory reads, and
  exact create/write paths for object and final executable. Broader prefixes
  and unrelated surplus authority fail closed.
- Source, object, executable, and working directory remain within one selected
  DBFS or NVFS root. Textual path checks reject traversal. FAT32 is deliberately
  refused until its owner supplies a backend-canonical object/name key that
  collapses case, 8.3, and Unicode aliases.

## Lifecycle and performance

The owner has 32 preallocated logical slots and a free-slot stack. Lifecycle
transitions are O(1); reservation adds one fixed 32-slot path-conflict scan,
and catalog lookup remains bounded by the catalog's fixed key table. No file or
artifact bytes are copied into a slot.
Each slot stores only exact paths, two authenticated digests, target identity,
and task identity. Generation and nonce checks reject stale copies. Dispatch is
consume-once and cancellation advances the generation. There is intentionally
no success-release API until an authenticated backend completion receipt
exists. A dispatched slot remains unavailable; marking its outcome unknown
permanently retires it and keeps its possibly mutated output paths excluded.

## Remaining integration

The filesystem syscall owner must mint the task's exact path capabilities from
live mount/OFD authority, derive the task identity from the current scheduler
TCB, invoke the package-private reservation/dispatch boundary, and bind backend
compile/link acknowledgements plus loader execution evidence.
Until that exists, this module is a safe prerequisite, not evidence that Clang
ran in SimpleOS or that hello world executed on any architecture.
