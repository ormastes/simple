# Positioned filesystem installation audit

Source: immutable revision `267b99c8c17`. Follow-up to draft PR #1988.
Status: BLOCKED; no production change, bootstrap, or QEMU run.

## Exact missing producer

Tracked-source search found only definitions/exports, and no callers, for all three functions:

- `src/os/kernel/abi/syscall_shim_positioned.spl:57`: `shim_positioned_install_owner_v1`.
- `src/os/sosix/fs/registry_lifecycle_v1.spl:57`: `sosix_fs_registry_register_capability_v1`.
- `src/os/sosix/fs/service_buffer_registry_v1.spl:80`: `sosix_fs_service_register_owned_buffer_v1`.

The missing producer must derive service endpoint/generation and operation identity from a real service lifecycle, derive caller identity from authenticated IPC/syscalls, bind file capabilities to live VFS objects, register owned buffer bytes, and publish each returned registry into the same retained shim owner used by syscalls 134/135. No current production integration performs these operations. Restart/replacement must advance service and operation generations and retire stale capabilities/buffers; the existing installer checks generation advancement but does not supply that lifecycle.

## Observed boot and service paths

- `os.kernel.boot.os_main.os_main` initializes services, then checks `vfs_is_ready`; when false it calls `boot_fs_mount_freestanding_production`.
- `boot_fs_mount_freestanding_production` requires a provisioned pure NVMe lease device and enters the pure mount path. NVFS root transaction stages the mounted driver, installs `SosixPositionedBackendKindV1.Nvfs`, then commits the root. DBFS has a corresponding route installation. These calls select a backend, not an authenticated registry owner.
- `syscall_shim.shim_init` stores scheduler/IPC/log state and calls `shim_positioned_reset_v1`, which clears the registry installation and restores the FAT32 backend default. The source includes explicit calls from ARM64 filesystem launch preparation and reset; mounting a route therefore cannot by itself establish durable positioned authority across shim reinitialization.
- Trap leaves `spl_handle_fs_pread_registered_v1` / `spl_handle_fs_pwrite_registered_v1` use scheduler caller identity and dispatch through `g_shim_positioned_state`. Its uninstalled state returns `-95` before registry dispatch.
- The real catalogue payload `vfs_service_main` acquires its assigned device grant, creates a task-local NVMe/FAT32 driver and VFS manager, then calls `VfsService.start_catalogue_owned`. `init_port` creates named IPC port `vfs`; the service loop receives owned messages. This task-local service does not populate the kernel shim registry or connect its endpoint lifecycle to that registry. Its handles must not be assumed interchangeable with the kernel-global backend's handles.
- `positioned_acceptance_route_v1.spl` explicitly constructs a private test-shaped owner with fixed identities. Its own documentation says it proves neither live shim installation nor production capability/buffer registration. It is not a production authority source.

## Scope and next implementation boundary

Selected `simpleos_filesystem_toolchain_servers.md` REQ-006/007 requires real mounted-file execution and rejects fake substitution. A boot call with invented nonzero IDs would satisfy the installer's readiness predicate but leave every real caller without registered capabilities/buffers. It would misrepresent completion.

Implement an authenticated control-plane adapter between real VFS endpoint/open/close/buffer-registration lifecycle and the retained positioned shim state, including recovery and backend namespace binding, before adding the boot installer. Prove a genuine caller registration, positioned read/write, wrong-owner rejection, stale-generation rejection after recovery, and no dispatch before installation. Preserve pending F1/F2 pwrite policy.

Evidence was static source inspection only; no runtime PASS is claimed. The temporary sparse worktree was removed after inspection, restoring its disk allocation; no shared caches or unrelated files were deleted.
