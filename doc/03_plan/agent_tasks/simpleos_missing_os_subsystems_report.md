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
| Process isolation | Partial | `create_user_task` works end-to-end on x86_64: TCB built, user address space created, ELF segments bulk-mapped, task enqueued. Ring-3 first-dispatch helper (`arch_x86_64_enter_user_first` / syscall 14 EnterUserBlocking) wired. Pre-blocker live run shows three process-backed app PIDs with zero faults. | Full live re-verification blocked by compiler freestanding-stub symbol-weakness collision (see `doc/08_tracking/todo/simpleos_stub_collision_freestanding_2026-04-21.md`). Demand paging, page-fault handler, and TSS.RSP0/SYSCALL MSR hardening remain incomplete. |
| System memory allocator | Partial | Kernel heap and page-level infrastructure exist. | GUI/app fallback paths can exhaust heap; user heap, `mmap`/`brk`-style growth, OOM policy, and allocator hardening are incomplete. |
| Executable loader | Partial | ELF loader (`build_user_process_image`), bulk segment mapper (`vmm_copy_bytes_to_phys` / `vmm_zero_phys_range`), and `enter_user_first.s` ring-3 entry helper all implemented. Syscall 14 (EnterUserBlocking) wired end-to-end. Pre-blocker lane: Browser Demo pid=1, Hello World pid=2, Editor pid=3, `TEST PASSED`, 0 faults. | Syscall 13 gate (`syscall.spl:1246`, returns `-12`) still in place until live re-verification passes. Full re-run blocked by compiler freestanding-stub symbol-weakness collision. |
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

- Kernel: `build/os/simpleos_desktop_e2e_32.elf`
- Disk image: `build/os/fat32.img`
- Serial log: `build/os/simpleos_desktop_direct_serial.log`
- Result: QEMU timed out after the guest emitted `TEST PASSED`; this is the
  expected harness shape for this direct serial run because the ISA debug-exit
  path is not consumed by the wrapper command.

The current x86_64 desktop E2E binary boots in QEMU with the FAT32 NVMe image
attached and reaches:

- `[arch-init] scheduler topology probed`
- `[desktop-e2e] desktop-ready`
- `[desktop-e2e] shortcut:ok key=meta+b app=browser_demo`
- `[desktop-e2e] hello:shortcut:ok key=meta+h app=hello_world`
- `[desktop-e2e] remote-grouping:ok pid=4242 windows=2`
- `[desktop-e2e] editor-shortcut:ok key=meta+e app=editor`
- `TEST PASSED`

This proves boot, framebuffer initialization, launcher shortcut routing, WM
window registration, and resident app window materialization. It does not yet
prove that apps are normal filesystem-loaded, process-isolated, scheduler-owned
programs. The active app path now proves the filesystem bytes are found, copied
into owned loader storage, and parsed into a `UserProcessImage` before the
launcher intentionally falls back to resident-manifest materialization:

- `[syscall13] dispatch_direct enter`
- `[vfs-root] c_fat32_read_ok path=/sys/apps/<app> bytes=<n>`
- `[exec-source] vfs_hit path=/sys/apps/<app> bytes=<n>`
- `[syscall13] build_user_process_image ok`
- `[syscall13] user image handoff gated; scheduler enqueue pending`
- no `[c-syscall13] fat32 app image validated` marker
- no `EXCEPTION`, `cr2=...`, `cr3=...`, `heap exhausted`, `unresolved fn`, or
  `PANIC` marker
- `build_user_process_image` takes an owned copy of resolved VFS/FAT32 bytes
  before ELF parsing and stores owned segment/file-byte copies in the image
- `stack_builder` uses literal stack-size constants so the native baremetal
  build no longer folds the default stack size to zero
- the direct desktop lane initializes scalar identity PMM/VMM before VFS and
  syscall 13; expected markers are `[PMM] scalar init complete`,
  `[VMM] VMM initialization complete`, and
  `[desktop-e2e] memory-bootstrap:ok`
- user segment mapping now avoids cross-module raw address fallback calls and
  maps only the initial stack-frame pages; the remaining stack range is reserved
  for future demand growth once user page-fault handling is active
- launcher process rows expose `launcher_process_is_process_backed(pid)` so
  QEMU/system specs can distinguish scheduler-owned app PIDs from resident
  manifest fallbacks without scraping log text
- the C syscall shim now only uses its legacy fallback for `-ENOSYS`, so this
  lane no longer emits `[c-syscall13] fat32 app image validated`
- resident manifest fallback markers such as `mode=resident-manifest`

Those fallback markers must disappear before the process-backed app requirement
is closed. The current blocker is no longer filesystem loading, ELF/SMF image
construction, PMM initialization, VMM initialization, or user image mapping. A
direct-handoff diagnostic run reached:

- `[scheduler] create_user_task: address space ok`
- `[scheduler] create_user_task: map returned`
- `[scheduler] create_user_task: tcb built`
- `[scheduler] create_user_task: task stored`
- `[scheduler] create_user_task: caps registered`

The run then stalled before `_enqueue_ready` could enter. Until the scheduler
runqueue handoff works from syscall/trap context and the x86_64 return path can
actually switch into the new user context, syscall 13 remains gated and returns
`-12` so the launcher uses the validated resident-manifest compatibility path.

The x86_64 desktop lane now uses single-CPU `Scheduler.new_bootstrap()` for
early syscall/trap globals and clamps impossible early CPUID/SMP topology
counts. This avoids allocating the full 32-CPU scheduler state during direct
`-kernel` boot and prevents the pre-desktop heap exhaustion seen while tracing
the direct-handoff blocker. `Scheduler.new()` still keeps the normal
platform-topology behavior for unit-tested scheduler construction.

## Completion Criteria

The missing-subsystems work is complete only when packaged apps launch from
filesystem paths as independent OS-managed processes and QEMU evidence shows:

- launcher records a process-backed PID for each packaged app;
- scheduler can inspect and reap those app tasks;
- WM windows are registered through app IPC using the scheduler-owned PID;
- no packaged app relies on resident manifest fallback;
- file I/O, memory allocation, and syscall behavior remain stable across the
  Browser Demo, Hello World, Editor, Terminal, and File Manager smoke paths.
