# SimpleOS Process-Backed Apps Plan

> Status: CODE COMPLETE — process_record, app_manifest, syscall_result, wm_window_handle modules implemented (zero stubs, 20-test spec). Runtime blockers: syscall 13 return-path fault, VFS C array lifetime. Updated 2026-05-19.

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

## Additional Required Subsystems

| Subsystem | Why It Is Needed |
| --- | --- |
| Syscall/trap return correctness | Apps cannot trust the OS API until syscall entry, dispatch, return values, and fault recovery are stable. |
| Process lifecycle | Normal apps need `exec`, `exit`, `wait`, PID ownership, zombie cleanup, exit codes, crash classification, and reaping. |
| IPC/window protocol | GUI apps must create/update windows through WM/compositor IPC, not direct framebuffer or resident shell fallback. |
| App runtime startup | Each app needs a `crt0`-style startup path: heap init, argv/envp, stdio, TLS if supported, panic handling, and call into app `main`. |
| User/kernel ABI boundary | Kernel must validate user pointers and buffers, define errno/result rules, and preserve ABI compatibility. |
| Filesystem namespace | Stable paths such as `/bin`, `/sys/apps`, `/lib`, `/etc`, `/home`, and `/tmp` are needed for normal app behavior. |
| Timers and preemption | Apps need sleep/timeouts and fair scheduling, backed by timer interrupts or equivalent wakeups. |
| Stdio, terminal, and pipes | CLI and GUI helper apps need stdin/stdout/stderr, terminal sessions, logs, and eventually pipes. |
| Permissions or capabilities | Apps should not access all files, devices, or windows by default. A capability model fits SimpleOS better than full Unix permissions. |
| Networking API | Not required for first GUI proof, but normal host-style apps eventually need socket or network-service APIs. |
| App manifest/package system | Manifests should describe app id, executable path, icon, permissions, args, dependencies, and GUI/CLI/service mode. |
| Debuggability | Process list, syscall trace, crash dumps, kernel logs, and fault decoding are required to debug process-backed apps. |

## Priority Order

1. Fix syscall/trap correctness, especially syscall 13 direct spawn return behavior.
2. Make VFS return stable executable bytes for packaged FAT32 apps without C array lifetime corruption.
3. Finish filesystem-backed ELF launch into a scheduler-owned `UserProcessImage`; segment, stack, entry point, auxv, and syscall-level argv/envp materialization exist, but the FAT32 app ELF handoff still faults before resident fallback can be removed.
4. Complete user address spaces and process isolation, including CR3/page-table switching and safe user pointer validation.
5. Re-enable scheduler-backed user task creation, launch, reaping, and launcher PID tracking.
6. Build the app-facing userlib/runtime around the stable syscall ABI.
7. Add dynamic library loading only after static filesystem-loaded app execution is reliable.

## Async-First Native API Doctrine TODO

SimpleOS provides POSIX/libc compatibility for ported software, but native
SimpleOS drivers, services, and apps must use the native SimpleOS API. The
canonical doctrine is recorded in
`doc/04_architecture/os/simpleos_architecture.md`.

The OS architecture target is async-first: native file, pipe, TTY, process,
timer, socket, device, and window operations define async behavior first, and
sync APIs block on top of those async completions.

Required follow-up work:

- Audit sync-first paths in POSIX fd I/O, pipe compatibility, shell builtins,
  terminal/TTY, process wait/spawn, timers, sockets, and libc stdio.
- POSIX pipe fd read/write/close now route to the native pipe backend instead
  of the generic VFS async compatibility path; keep extending this pattern to
  TTY, socket, timer, and stdio descriptors.
- POSIX regular file read/write now block on `async_io` as the native owner for
  VFS-backed descriptor completion instead of duplicating VFS IPC completion
  logic in the POSIX layer.
- Promote native async APIs for fd/VFS, pipe, TTY/PTY, process lifecycle,
  timers, sockets, and window/event operations before adding or extending sync
  wrappers.
- Convert POSIX/libc sync operations into wrappers over native async services
  rather than independent state owners.
- Add MDSOC architecture checks or tests that reject POSIX/libc dependencies
  from `src/os/kernel`, `src/os/drivers`, and native app/service code when a
  native API exists.
- Document every temporary sync-first or POSIX-first path with an owner, a
  native async replacement, and a removal condition.

## Capability-Backed Storage And Device Queue TODO

SimpleOS should expose POSIX-compatible directories and files, but native
storage authority should be capability-backed. The architecture target is
recorded in
`doc/04_architecture/os/simpleos_exokernel_storage_architecture.md`.

Required follow-up work:

- Replace current single-namespace NVMe assumptions with active namespace
  enumeration and explicit NSID on every read, write, flush, and identify path.
- Reserve NVMe queue `0` for admin commands and queue `1` for system I/O.
  App/service data queues start at queue `2`.
- Add a queue manager that owns hardware queue allocation, command IDs,
  completion routing, queue depth, timeout/cancel, and fairness.
- Add canonical block-device identity and geometry types above NVMe, then add
  `PartitionBlockDevice` with GPT/MBR scan and LBA remapping.
- Register `/dev/nvme0nX` namespace devices and `/dev/nvme0nXpY` partition
  devices in devfs.
- Enforce `BlockDevice`, `StorageNamespace`, `StoragePartition`, `StorageExtent`,
  `Mount`, and `IoQueue` capabilities before exposing storage objects to apps.
- Replace broad `PortIO(0,0)` and `Mmio(0,0)` device syscall gates with
  object-specific `DeviceEnumerate`, `DeviceGrant`, `DeviceBarMap`,
  `DeviceDma`, and `IommuDomain` capabilities.
- Require IOMMU-backed DMA handles or trusted bounce buffers before direct queue
  fast paths are exposed outside trusted driver/storage capsules.
