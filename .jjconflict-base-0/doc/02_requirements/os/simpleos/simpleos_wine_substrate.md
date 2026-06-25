<!-- codex-design -->

# Feature Requirements: SimpleOS Wine Substrate

Date: 2026-05-06

## Scope

This requirement set converts the user objective into a staged platform program:

1. research Wine-needed features in SimpleOS and Simple lib;
2. improve the 2D rendering library and WM toward an X11-class graphics backend;
3. extend VM/process support for containers and Wine-level virtual memory;
4. cover the remaining Wine host substrate features;
5. base host waits and file/network I/O on the existing `nogc_async_mut` async library set;
6. only then run a non-GUI `hello.exe` milestone.

The current goal is not to claim upstream Wine compatibility. The goal is to build the SimpleOS/Simple-lib substrate that makes a future Wine port technically credible.

## Requirements

### REQ-001: Wine Substrate Capability Matrix

SimpleOS must expose a versioned capability matrix covering process, VM, POSIX ABI, thread/TLS, dynamic loading, filesystem, IPC, graphics, audio, fonts, input, and PE/COFF loader readiness.

Acceptance:

- Each capability has states: `missing`, `scaffold`, `partial`, `ready`, `verified`.
- Each capability links to implementation paths and verification evidence.
- Unknown "all other features" are represented as explicit capability rows, not hidden scope.

### REQ-002: Process-Backed App Baseline

Packaged SimpleOS apps must launch from filesystem bytes as scheduler-owned user processes without resident fallback.

Acceptance:

- Browser Demo, Hello World, Editor, Terminal, and File Manager launch with scheduler-owned PIDs.
- Process reaping and fault reporting are observable.
- WM windows are registered through process-owned IPC, not resident manifests.

### REQ-003: POSIX-Like Simple Lib Host ABI

Simple lib must provide a host ABI tier sufficient for Wine substrate work.

Acceptance:

- File descriptors, cwd/env/argv, stdio, pipes, sockets, timers, errno mapping, and process spawn APIs exist.
- Filesystem path, attribute, lock, sharing, and long-name behavior are documented and tested.
- APIs are async-first internally over `nogc_async_mut` futures, completion I/O, event-loop registration, and wakers, while exposing compatibility shims where Wine needs POSIX shapes.

### REQ-004: Thread, TLS, And Synchronization Support

SimpleOS must support more than one thread per process with TLS and synchronization semantics needed by Wine.

Acceptance:

- Thread create/join/detach and per-thread TLS exist.
- Mutex, condvar, semaphore, event, and wait APIs have blocking and timeout behavior.
- Faults and exceptions can be attributed to the correct thread.

### REQ-005: Wine-Level VM And Container Isolation

SimpleOS VM must support fixed mappings, executable mappings, guard pages, `mprotect`-style permission changes, user pointer validation, and per-container namespaces.

Acceptance:

- A process can reserve, commit, protect, and unmap user ranges.
- Page faults expose process, thread, address, access type, and recovery policy.
- Containers isolate process, filesystem, IPC, network, and capability namespaces.

### REQ-006: X11-Class 2D Rendering And WM Backend

The 2D renderer and WM must expose enough backend behavior to host a Wine graphics driver later.

Acceptance:

- Surfaces, windows, clipping, damage regions, blits, text/glyph rendering, cursors, input, clipboard, screen modes, and expose/configure events exist.
- The backend has an X11-like object model even if it is native SimpleOS, not X11 protocol compatible.
- Golden/pixel and event-sequence tests cover WM/backend parity.

### REQ-007: Dynamic Loading And PE/COFF Loader Preparation

SimpleOS must define how Unix-side dynamic loading and Windows PE/COFF loading will coexist.

Acceptance:

- In-guest dynamic loading has a design and minimal implementation path.
- PE/COFF parser can validate DOS header, PE signature, machine type, optional header, sections, imports, relocations, TLS directory, and subsystem.
- Loader rejects unsupported binaries with structured errors.

### REQ-008: Non-GUI `hello.exe` Milestone

After REQ-002 through REQ-009 reach `verified`, SimpleOS must run or faithfully interpret a non-GUI Windows console `hello.exe`.

Acceptance:

- The test binary is PE32+ x86_64 console subsystem.
- The milestone prints expected stdout text or returns a structured "unsupported import" error before any unsafe execution.
- The milestone runs under a repeatable QEMU or host-emulated test lane.

### REQ-009: `nogc_async_mut` Async Substrate

Wine-facing host waits and file/network I/O must be built on the existing `nogc_async_mut` and `nogc_async_mut_noalloc` library set, not a second async runtime.

Acceptance:

- `Future`, `Poll`, `Waker`, `EventLoop`, and `IoDriver` are the canonical async primitives for Wine substrate work.
- Completion operations cover open, read, write, close, timeout, and completion polling before host ABI readiness can be claimed.
- Event-loop support covers fd register, deregister, and wake behavior before wait/select/poll compatibility can be claimed.
