# SimpleOS Wine Support Research Report

Date: 2026-05-06

## Decision

Do not start a full Wine implementation now. Start prerequisite OS/framework work first, plus a narrow Wine feasibility spike.

## Why

Wine is not just a PE parser. It needs a Unix/POSIX-like host substrate: process creation, native threads/TLS, signal-to-SEH exception handling, mmap/protect/unmap-style VM, dynamic loading, file descriptors, sockets, timers, IPC for `wineserver`, filesystem/path/attribute semantics, and graphics/audio/input/font backends.

SimpleOS has promising pieces: x86_64 boot, FAT32 desktop disk proof, GUI/WM scaffolding, TCP/IP/socket service, a freestanding libc/sysroot lane, and partial process/user-mode work. But current repo evidence still shows blocking gaps:

- desktop app launch still has resident fallback evidence;
- pthreads are no-op stubs and the kernel is one-thread-per-process;
- dynamic linking is missing;
- process isolation and page-fault/demand-paging hardening are incomplete;
- app ABI is missing normal fd/process/stdio/timer/IPC/error behavior;
- there is no X11, Wayland, OpenGL/GLX, Vulkan, mature audio, or Wine-compatible desktop backend.

## Recommended Path

1. Close SimpleOS process-backed app execution first: no resident fallback, scheduler-owned app PIDs, stable reaping, stable IPC to WM.
2. Implement a POSIX host ABI tier: fd table, pipes, sockets, poll/select equivalent, timers, errno mapping, cwd/env/argv, process spawn, filesystem namespace, path normalization, locks, and sharing modes.
3. Implement real threads: pthread-compatible create/join/detach, TLS, mutex/condvar/semaphore/event waits, and per-thread fault/exception context.
4. Implement VM requirements: fixed mappings, executable mappings, `mprotect`, guard pages, page-fault delivery, stack growth policy, and user pointer validation.
5. Choose the Wine hosting model:
   - **Port upstream Wine** only after POSIX + dynamic linking + backend surfaces exist.
   - **Build a SimpleOS Wine-like NT layer** if the goal is long-term native integration, accepting much more work.
   - **Run Wine inside a Linux compatibility personality/container** if fastest app compatibility matters.
6. Start a feasibility spike now only for PE inspection and a non-GUI console "hello.exe" loader experiment. Treat it as research, not the Wine port.

## Go/No-Go

- Full Wine port: **NO-GO today**.
- Prerequisite framework work: **GO**.
- Narrow PE/NT loader spike: **GO**, if scoped to learning and test fixtures.

## Evidence

- Local research: `doc/01_research/local/simpleos_wine_support.md`
- Domain research: `doc/01_research/domain/simpleos_wine_support.md`
- Key local blockers: `doc/09_report/simpleos_implementation_status_2026-04-04.md`, `doc/03_plan/agent_tasks/simpleos_missing_os_subsystems_report.md`, `doc/09_report/fr_sos_024_desktop_disk_live_2026-04-22.md`
- External sources: WineHQ, Wine build-dependencies wiki, Wine source-tree wiki, Wine Developer Guide.
