# SimpleOS Process-Backed Apps Plan

## Status

- QEMU desktop smoke boots to `TEST PASSED` with NVMe FAT32 attached.
- Browser Demo, Hello World, and Editor shortcuts create WM-owned windows.
- The active app path still falls back to resident manifest windows after syscall 13 returns `-ENOSYS`.
- This is not yet the target model where apps are loaded from the filesystem as separate OS-managed processes.

## Target Model

- Drivers may keep baremetal assumptions and direct hardware bridges.
- Apps must behave like normal host-OS applications:
  - loaded through VFS from filesystem paths;
  - represented by process IDs owned by the kernel scheduler;
  - isolated through the user-process image/loader path;
  - communicating with WM/compositor through IPC instead of direct baremetal calls.

## Remaining Work

1. Restore syscall 13 direct-spawn dispatch after fixing its return-path fault.
2. Make `g_vfs_read_file_bytes()` return stable Simple-owned executable bytes for packaged FAT32 apps without C array lifetime corruption.
3. Finish ELF/user-process image construction for `/sys/apps/*`, including stack, auxv, entry point, and user memory mappings.
4. Re-enable scheduler enqueue for filesystem-backed user tasks and verify task lookup/reaping through launcher process records.
5. Replace resident manifest fallback assertions with process-backed assertions: PID exists in scheduler, app path matches VFS path, and WM windows are registered by process IPC.
6. Re-enable real editor save/readback through the filesystem after the process-backed launch path is stable.

## Verification Gate

- `simpleos_desktop_e2e_32.elf` must still emit:
  - `[desktop-e2e] desktop-ready`
  - `[desktop-e2e] shortcut:ok`
  - `[desktop-e2e] remote-grouping:ok`
  - `[desktop-e2e] editor-shortcut:ok`
  - `TEST PASSED`
- Additional required marker before closing this plan:
  - `[launcher] process-backed app_id=/sys/apps/... pid=...`
  - no `[syscall13] installed direct bridge deferred`
  - no `resident-manifest` fallback for packaged apps.
