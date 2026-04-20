# SimpleOS Missing OS Subsystems Report

## Purpose

This report records what SimpleOS still needs before GUI apps can behave like
normal host-OS applications. Drivers may keep baremetal assumptions and direct
hardware knowledge, but apps must run through filesystem, process, memory,
syscall, IPC, and scheduler services owned by the OS.

Related plan: `doc/03_plan/agent_tasks/simpleos_process_apps_plan.md`.

Detailed feature requests:
`doc/02_requirements/feature/simpleos_os_subsystem_feature_requests.md`.

## Current Status

| Subsystem | Status | Current State | Concrete Blocker |
| --- | --- | --- | --- |
| File I/O | Partial | FAT32, VFS, and direct NVMe/FAT bridges exist; desktop smoke can find packaged app names. | App executable reads still depend on special fallback bridges instead of a stable generic VFS byte stream. |
| Scheduler | Partial | Scheduler/task types and launch scaffolding exist. | Filesystem-loaded apps are not yet reliably enqueued and run as scheduler-owned user tasks. |
| Process isolation | Blocked | User-process image and page-table work exists as scaffolding. | Per-process address spaces, safe user/kernel transitions, and reliable page fault handling are not complete. |
| System memory allocator | Partial | Kernel heap and page-level infrastructure exist. | GUI/app fallback paths can exhaust heap; user heap, `mmap`/`brk`-style growth, OOM policy, and allocator hardening are incomplete. |
| Executable loader | Partial | ELF/user-process image code exists. | Syscall 13 direct spawn is currently deferred because the real filesystem-loaded process path faults. |
| System API/lib | Partial | Syscall shims and userlib pieces exist. | App-facing ABI is not complete enough for normal programs: file descriptors, process APIs, stdio, timers, IPC, and error mapping remain incomplete. |
| Dynamic library loading | Missing | Shared-library design exists in other compiler/SFFI contexts. | No in-guest app dynamic linker/loader path for SimpleOS processes. |

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
`doc/04_architecture/simpleos_architecture.md`.

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
`doc/04_architecture/simpleos_exokernel_storage_architecture.md`.

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

## Current QEMU Evidence

Latest checked artifact:

- Kernel: `build/os/simpleos_desktop_e2e_66.elf`
- Disk image: `build/os/fat32_hello_check_47.img`
- Serial log: `build/os/simpleos_desktop_hello_check_66_serial.log`
- Result: QEMU exited through the debug-exit path and the serial log reached
  `TEST PASSED`.

The current x86_64 desktop E2E binary boots in QEMU with the FAT32 NVMe image
attached and reaches:

- `[desktop-e2e] desktop-ready`
- `[desktop-e2e] shortcut:ok key=meta+b app=browser_demo`
- `[desktop-e2e] hello:shortcut:ok key=meta+h app=hello_world`
- `[desktop-e2e] remote-grouping:ok pid=4242 windows=2`
- `[desktop-e2e] editor-shortcut:ok key=meta+e app=editor`
- `TEST PASSED`

This proves boot, framebuffer initialization, launcher shortcut routing, WM
window registration, and resident app window materialization. It does not yet
prove that apps are normal filesystem-loaded, process-isolated, scheduler-owned
programs. The active app path now proves the filesystem bytes are found and the
known-app launch result is produced by the Simple syscall dispatcher before the
C syscall shim fallback:

- `[syscall13] dispatch_direct enter`
- `[vfs-root] c_fat32_read_ok path=/sys/apps/<app> bytes=<n>`
- `[exec-source] vfs_hit path=/sys/apps/<app> bytes=<n>`
- valid filesystem ELF bytes now enter the normal `create_user_task` path before
  any resident fallback is considered
- `build_user_process_image` takes an owned copy of resolved VFS/FAT32 bytes
  before ELF parsing and stores owned segment/file-byte copies in the image
- launcher process rows expose `launcher_process_is_process_backed(pid)` so
  QEMU/system specs can distinguish scheduler-owned app PIDs from resident
  manifest fallbacks without scraping log text
- no `[c-syscall13] fat32 app image validated` marker
- resident manifest fallback markers such as `mode=resident-manifest`

Those fallback markers must disappear before the process-backed app requirement
is closed. The next blocker is making `build_user_process_image` plus
`Scheduler.create_user_task` safe for real FAT32 app ELFs under the full QEMU
desktop smoke and then removing the shared resident compatibility fallback.

2026-04-20 follow-up: the live `simpleos_desktop_disk_boot_spec.spl` FAT32
desktop lane is green again with the compatibility fallback guarded away from
process-backed PIDs. The remaining QEMU blocker is still the C-side syscall-13
fallback in `baremetal_stubs.c`, which can emit
`[c-syscall13] fat32 app image validated; resident pid allocated` after the
SPL trap bridge declines a direct process spawn.

## Completion Criteria

The missing-subsystems work is complete only when packaged apps launch from
filesystem paths as independent OS-managed processes and QEMU evidence shows:

- launcher records a process-backed PID for each packaged app;
- scheduler can inspect and reap those app tasks;
- WM windows are registered through app IPC using the scheduler-owned PID;
- no packaged app relies on resident manifest fallback;
- file I/O, memory allocation, and syscall behavior remain stable across the
  Browser Demo, Hello World, Editor, Terminal, and File Manager smoke paths.
