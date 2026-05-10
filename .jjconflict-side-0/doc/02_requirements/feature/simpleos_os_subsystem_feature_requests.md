# SimpleOS OS Subsystem Feature Requests

## Purpose

These feature requests turn the missing-subsystems report into implementable
work items. The target is host-OS-style application behavior: apps are loaded
from files, run as scheduler-owned processes, and use OS APIs. Drivers may keep
baremetal hardware assumptions.

References:

- `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md`
- `doc/03_plan/agent_tasks/simpleos_process_apps_plan.md`

## FR-SOS-001: File I/O for Executable Loading

**Goal:** Load executable bytes from mounted filesystems through VFS.

**Requirements:**

- `g_vfs_read_file_bytes(path)` returns stable Simple-owned bytes for seeded
  app executables.
- Canonical app paths such as `/sys/apps/browser_demo` resolve to the current
  FAT32 image aliases without exposing alias names to apps.
- File reads must return enough bytes for ELF program-header validation and
  segment loading, not only the ELF magic prefix.
- Read failures return an empty byte array and emit a serial diagnostic.

**Acceptance:**

- Resolving `/sys/apps/browser_demo`, `/sys/apps/hello_world`, and
  `/sys/apps/editor` reaches real ELF bytes from FAT32.
- The loader can parse the returned bytes as ELF instead of falling back to
  resident manifest-only validation.

## FR-SOS-002: Scheduler-Owned App Tasks

**Goal:** Convert filesystem-loaded executables into scheduler-owned tasks.

**Requirements:**

- Spawn returns a scheduler PID, not a resident fallback PID.
- Launcher process records track scheduler PID, app id, state, and window count.
- Task lookup, yield, exit, wait, and reaping work for app tasks.

**Acceptance:**

- QEMU logs include `[launcher] process-backed app_id=... pid=...`.
- `launcher_find_process_by_pid(pid)` resolves the process after spawn.
- Exited app tasks are reaped without leaving stale windows.

## FR-SOS-003: Process Isolation

**Goal:** Give each app a user address space separated from kernel state.

**Requirements:**

- ELF segments map into a per-process page table.
- Kernel and MMIO regions are not writable from user code.
- User pointer validation protects syscall buffers.
- Page faults identify process, address, access type, and recovery policy.

**Acceptance:**

- A bad user pointer returns an error or terminates only the faulty process.
- One app cannot modify another app's memory or kernel memory.

## FR-SOS-004: System Memory Allocator

**Goal:** Provide robust kernel and user allocation behavior.

**Requirements:**

- Kernel heap must not be exhausted by normal desktop launch paths.
- User processes get their own heap growth API.
- `mmap`/`munmap` or equivalent supports file and anonymous mappings.
- OOM paths fail cleanly and include diagnostics.

**Acceptance:**

- Desktop launches Browser Demo, Hello World, Editor, Terminal, and File Manager
  without heap exhaustion.
- A forced oversized allocation fails without corrupting scheduler or VFS state.

## FR-SOS-005: Executable Loader

**Goal:** Load static app executables from filesystem bytes into runnable images.

**Requirements:**

- Validate ELF class, machine, program headers, segment sizes, and entry point.
- Map loadable segments with correct permissions.
- Build initial stack with path, argv, envp, and auxv placeholders.
- Reject invalid or unsupported binaries with clear errno-style results.

**Acceptance:**

- Valid seeded app ELFs build `UserProcessImage`.
- Truncated or malformed ELFs are rejected before scheduler enqueue.

## FR-SOS-006: System API and User Library

**Goal:** Give apps a stable API surface instead of baremetal calls.

**Requirements:**

- Userlib wraps syscalls for files, process lifecycle, memory, IPC, timers, and
  debug output.
- Return values use consistent errno/result mapping.
- App code does not call hardware or kernel internals directly.

**Acceptance:**

- App source can call userlib APIs and run on SimpleOS without knowing whether
  storage, graphics, or input are baremetal-backed.

## FR-SOS-007: Dynamic Library Loading

**Goal:** Support shared libraries after static app execution is reliable.

**Requirements:**

- Define shared object search paths and dependency metadata.
- Resolve symbols and apply relocations per process.
- Map shared text read-only and data privately per process.
- Surface missing-library and missing-symbol errors.

**Acceptance:**

- A dynamically linked smoke app starts with one shared library dependency.
- Static apps continue to work without the dynamic loader.

## FR-SOS-008: Syscall and Trap Return Correctness

**Goal:** Make syscall entry, dispatch, and return reliable for apps.

**Requirements:**

- Syscall 13 direct spawn must return without corrupting control flow.
- Trap handlers preserve registers required by the ABI.
- Negative errno and positive PID returns are distinguishable.

**Acceptance:**

- The QEMU desktop app path no longer emits
  `[syscall13] installed direct bridge deferred`.
- Positive PID returns reach launcher correctly.

## FR-SOS-009: Process Lifecycle

**Goal:** Complete lifecycle management for normal apps.

**Requirements:**

- Implement spawn/exec, exit, wait, kill/terminate, crash classification, and
  zombie cleanup.
- Parent/child ownership must be explicit.
- Launcher-visible state must distinguish running, exited, crashed, and
  terminated.

**Acceptance:**

- A test app exits with code 0 and the parent observes that code.
- A crashing app is marked crashed and its windows are cleaned up.

## FR-SOS-010: IPC and Window Protocol

**Goal:** Make GUI apps talk to WM/compositor through IPC.

**Requirements:**

- Apps request windows through a stable compositor IPC message.
- WM assigns ownership using scheduler PID and app id.
- Input, repaint, close, focus, and destroy events have defined message shapes.

**Acceptance:**

- Browser Demo creates its windows through IPC after process spawn.
- No app window is created by resident shell fallback.

## FR-SOS-011: App Runtime Startup

**Goal:** Provide a process entry runtime before app `main`.

**Requirements:**

- Initialize heap, stdio handles, argv/envp, panic handler, and syscall userlib.
- Preserve app path and app id.
- Define CLI vs GUI startup mode.

**Acceptance:**

- Hello World receives its app path and can print through stdio/debug output.

## FR-SOS-012: User/Kernel ABI Boundary

**Goal:** Stabilize the ABI contract between user processes and kernel.

**Requirements:**

- Define syscall register convention, pointer ownership, and buffer copy rules.
- Validate all user pointers before kernel reads or writes.
- Version ABI-visible structs and message formats.

**Acceptance:**

- Invalid syscall buffers cannot panic the kernel.
- ABI tests cover positive, negative, and boundary-sized buffers.

## FR-SOS-013: Filesystem Namespace

**Goal:** Define stable app-visible filesystem layout.

**Requirements:**

- Reserve `/bin`, `/sys/apps`, `/lib`, `/etc`, `/home`, and `/tmp`.
- Mount table lookup must hide FAT32 short-name implementation details.
- App manifests reference canonical paths only.

**Acceptance:**

- `/sys/apps/hello_world` launches regardless of root 8.3 alias details.

## FR-SOS-014: Timers and Preemption

**Goal:** Support time-based app behavior and fair scheduling.

**Requirements:**

- Provide timer interrupt or equivalent wakeup source.
- Implement sleep/timeouts for user processes.
- Prevent one app from monopolizing CPU in normal scheduling mode.

**Acceptance:**

- A sleeping app yields CPU and wakes after the requested interval.

## FR-SOS-015: Stdio, Terminal, and Pipes

**Goal:** Support normal CLI app I/O.

**Requirements:**

- Provide stdin, stdout, and stderr handles.
- Terminal app owns an interactive session.
- Pipes connect app output to another process or terminal buffer.

**Acceptance:**

- A CLI smoke app writes stdout and the terminal displays it.

## FR-SOS-016: Permissions or Capabilities

**Goal:** Prevent apps from accessing all OS resources by default.

**Requirements:**

- Manifests declare required file, IPC, device, and network capabilities.
- Kernel checks capabilities at syscall dispatch.
- Denials return consistent permission errors.

**Acceptance:**

- An app without file-write capability cannot write `/etc` or `/sys/apps`.

## FR-SOS-017: Networking API

**Goal:** Expose networking to apps through OS services.

**Requirements:**

- Define socket or network-service APIs.
- Keep NIC drivers below the app boundary.
- Support nonblocking or timeout-capable operations.

**Acceptance:**

- A network smoke app can open a connection or issue a local network-service
  request without direct driver access.

## FR-SOS-018: App Manifest and Package System

**Goal:** Make app identity and launch metadata explicit.

**Requirements:**

- Manifests define app id, executable path, icon, permissions, args,
  dependencies, and GUI/CLI/service mode.
- Launcher reads manifests from filesystem, not hardcoded resident tables.
- Missing or invalid manifests produce visible launch errors.

**Acceptance:**

- Adding a manifest and executable to the disk image makes a new app visible to
  the launcher without code changes.

## FR-SOS-019: Debuggability

**Goal:** Make process-backed app failures diagnosable.

**Requirements:**

- Provide process list, syscall trace, kernel log, crash dump, and fault decode.
- Include app id, PID, path, trap number, fault address, and exit code.
- Keep diagnostics available in serial/QEMU tests.

**Acceptance:**

- A forced app fault produces a readable process crash report and does not hide
  the failing PID.
