# SimpleOS positioned FD bridge has unresolved owner contracts

**Status:** open release blocker for platform unification REQ-009/010/012/018.
**Observed:** source inspection on 2026-09-27, branch
`feature/simpleos-live-positioned-owner-20260927` at `6b5a4f6ee8e`.
This is a missing-definition finding, not a completed compiler run.

## Failure surface

`src/os/kernel/fs/positioned_fd_owner_v1.spl` imports and calls twelve names
without definitions in the respective source owners:

| Owner | Missing names |
|---|---|
| `src/os/services/vfs/vfs_positioned_ops.spl` | `g_vfs_positioned_open_binding_v1`, `g_vfs_positioned_binding_close_v1`, `g_vfs_positioned_binding_read_at_v1`, `g_vfs_positioned_binding_write_at_v1` |
| `src/os/kernel/fs/fd_table_descriptor_owner_v1.spl` | `fd_descriptor_reserve_install_lowest_v1`, `fd_descriptor_commit_install_v1`, `fd_descriptor_positioned_snapshot_v1`, `fd_descriptor_pin_positioned_io_v1`, `fd_descriptor_reserve_positioned_close_v1` |
| `src/os/kernel/fs/open_file_description_owner_v1.spl` | `open_file_description_create_positioned_v1`, `open_file_description_complete_io_indeterminate_v1`, `open_file_description_cancel_undispatched_io_v1` |

The bridge also accesses `dispatch.backend.positioned`, while
`OpenFileDescriptionBackendBindingV1` currently has only
`file_object_id`, `file_object_generation`, and `backend_kind`. There is no
production caller of the bridge. Kernel syscall 30 continues to open FAT32;
the managed `/srv/data` path fails ENOSYS instead of publishing an unowned FD.

## Progress after initial inspection

`open_file_description_complete_io_indeterminate_v1` and
`open_file_description_cancel_undispatched_io_v1` now have owner
implementations and a package-scoped behavior spec. They are **unverified**:
the isolated macOS Stage 2 bootstrap first stopped at the Cocoa runtime
owner preflight. The repaired Cocoa gate passed on retry, but Stage 2
then failed on an empty CXX assignment before admitting a runtime. See
`macos_stage2_empty_cxx_after_cocoa_owner_2026-09-27.md`. Ten originally
missing definitions and the backend-binding mismatch remain.

The owner now rejects ordinary close reservations for an OFD quarantined
after indeterminate I/O, retaining its descriptor number. Task-context
teardown releases those aliases with an incomplete receipt while retaining
the uncertain backend binding; it does not poison the descriptor owner.
This path has a package-scoped spec but remains unverified until Stage 2
admission supplies a self-hosted runtime.

## Required fix

Define one exact MountTable virtual-object binding with generation and kind.
`src/lib/nogc_async_mut/fs_driver/mount_table.spl` reuses slots after close
and encodes the generation into the virtual handle; binding only a slot or
hardcoding generation one would accept stale aliases after reuse. Then
complete transactional descriptor reserve/install/close and OFD
pin/complete/indeterminate operations in their existing owners. A failed
open must roll back its reserved FD and close the exact MountTable object.
Copyout failure must not falsely commit shared-cursor progress; close failure
must quarantine the binding until a terminal owner receipt. Test capacity,
stale generation, wrong task, duplicate close, backend error, and rollback.
Then derive lifecycle authority from the scheduler and route public file
syscalls through the qualified bridge as a single migration.

## Resume and admission

Prerequisite: an admitted self-hosted Simple runtime with provenance and
receipt; this worktree has no such candidate. With that runtime, first run
`<admitted-runtime> check src/os/kernel/fs` and the focused owner specs. Fix
the first real compiler error, then run the qualified owner suite and the
SimpleOS guest file/persistence path. Do not use the Rust seed as product
verification. The exact implementation sequence is in
`doc/03_plan/os/simpleos_nvfs_root_owner_cutover.md`.

Owner: SimpleOS VFS/kernel file owner. Final reviewer: independent
normal/highest-capability reviewer. Sidecar lanes: N/A until the binding
interface, test helper names, and fail-fast placeholders are fixed.
