# SCV Workspace Restore Mutation Owner

**Status:** design only; blocked on a safe native provider. No mutation API is
implemented by this document.

**Requirement context:** `REQ-004` in
[`scv_full_phase2_2026-10-27.md`](../02_requirements/feature/scv_full_phase2_2026-10-27.md).

## Current boundary

`scv_restore_preflight` validates immutable target data and checks obvious
workspace hazards. It is advisory: it neither anchors the later writes nor
guarantees that the workspace stayed unchanged after preflight. The existing
`scv_restore_op` still writes and removes entries through path-based helpers.
`app.io` exposes path-based delete/rename/write operations, while
`read_only_file_view` is read-only. The hosted safe-artifact owner is
installer-specific: named publication assumes a private destination parent,
and its bundle interface does not provide workspace rename/quarantine.

Therefore no current API can safely implement restore in a shared worktree.
Do not use `fstatat` followed by `unlinkat` as an identity compare-and-swap;
the directory entry may be replaced between those syscalls. An SCV advisory
flock does not exclude an editor or another same-user process.

## Proposed ownership boundary

SCV should own restore policy, target validation, journal schema, and recovery
decisions in Simple. A shared native host-I/O owner should own retained root
and parent directory descriptors, no-follow path resolution, atomic entry
movement, no-replace publication, and directory synchronization. SCV must not
call path-based mutators for restore after this owner is admitted.

The native provider must be a shared I/O capability, not an SCV-specific
syscall shim. Its contract must state platform support explicitly and return
`unsupported` when its required primitive is absent. Initial support should be
limited to a platform with a verified descriptor-relative no-replace rename
and durability path. Do not infer macOS support from the read-only descriptor
walker or from ordinary `rename`.

## Recoverable transaction protocol

The operation is a journaled, recoverable group, not an atomic multi-path
filesystem snapshot. It must preserve uncertain state for operator recovery.

1. Resolve the repository root once to a retained directory handle. Resolve
   each parent beneath that handle without following links or crossing the
   declared root boundary. Reject invalid relative paths and special cases
   before staging.
2. Build and validate the complete target plan. Create a unique transaction
   record and same-filesystem quarantine location through the same root owner.
   Durable intent binds the operation ID, root and parent identities, source
   relative leaf, expected content and metadata identity, unique quarantine
   name, desired output, and expected current operation head. Retain source
   parent and quarantine directory handles for the transaction. Persist and
   synchronize the complete intent before the first workspace rename.
3. For each existing leaf, atomically move the directory entry to a unique
   quarantine name using a no-replace rename. Synchronize both affected
   directories. Inspect the moved entry only after the rename. If it differs
   from the intent identity, retain it in quarantine and stop with a
   concurrent-change result; never unlink, overwrite, or silently restore it.
   A raced-in symlink or directory is still preserved as an opaque entry.
4. Before every forward publication, revalidate the current root-to-parent
   path binding against the retained handles. A changed or detached parent
   cannot be treated as the active workspace; preserve every moved object and
   stop for recovery. Publish each replacement with a no-replace operation
   from owner-controlled staging, synchronizing file data before publication
   and the containing directory afterward. If an editor repopulates the
   destination, keep both the new entry and the staged/quarantined data and
   return a conflict.
5. Persist transaction progress after each durable filesystem boundary. On
   restart, reconcile the intent, destination, quarantine entry, and progress
   record. Any ambiguous identity or missing evidence stops recovery without
   deleting data.
6. Rollback may restore a quarantine entry only when the destination is
   absent, using no-replace semantics. Revalidate the current path binding
   against the retained parent; a detached or replaced parent cannot count as
   workspace success. If the destination exists, keep the quarantined entry
   and report recovery required. Before final admission, revalidate the root
   and all affected parent bindings again. Cleanup may remove a transaction
   record only after the journal proves every archived object is accounted
   for and the user-visible operation is committed.

Quarantine is a recovery location, not an immutable snapshot. A process may
hold an open descriptor to a moved inode, and hard links can expose the same
bytes elsewhere. Hash or `fstat` equality alone does not prove the archived
bytes cannot change. Keep the archive and report an incomplete restore when
identity/evidence changes; do not claim a fixed archival copy without a
separate immutable-copy protocol.

The eventual SCV restore should create a new descendant operation after
workspace publication rather than rewinding the operation head before the
workspace transaction is durable. Its head update must use a common
expected-generation compare-and-swap or lease authority shared by every
mutator. A reread followed by a path-based write, a journal flock, or the
current WAL foreign-head heuristic is not sufficient. A foreign-head change
must preserve workspace objects and return conflict/recovery-required.

The transaction intent, quarantine, staged replacements, before-images, and
target closure must remain pinned as retention roots until the transaction is
committed and recovery evidence is durably closed. They must not be treated as
unreachable cache objects or become eligible for GC while recovery is
possible.

## Admission gates

- A shared native owner provides retained-root, no-follow, descriptor-relative
  rename-to-quarantine and no-replace publication, with documented platform
  coverage.
- The owner returns distinct outcomes for unsupported, conflict, durable
  success, visible-but-durability-uncertain, and recovery-required states.
- Crash recovery handles a crash before/after each rename, each directory
  sync, each journal update, and final operation publication without deleting
  unaccounted data.
- Editors and non-cooperating writers remain in the threat model. A lock is
  coordination only; correctness depends on atomic no-replace operations and
  preserving uncertain entries.
- A new provider export requires ABI/build admission across the native owner
  inclusion in `runtime_native.c`, text argument lowering in
  `text_extern_abi.spl`, and the compiler/runtime symbol registries. An
  `extern fn` declaration alone does not establish a callable production
  provider or unsupported behavior in the interpreter.
- Existing callers of `scv_restore_op` in `network_remote.spl`,
  `public_remote.spl`, and `pack.spl` must propagate refusal/recovery errors
  without reporting import or sync success. Imported immutable objects may
  remain as unreachable draft data after a refused worktree publication.
- Until these gates pass, `scv_restore_preflight` remains advisory and restore
  mutation must not be described as concurrency-safe or crash-safe.
