<!-- codex-design -->

# Detail Design: SimpleOS Wine Substrate

Date: 2026-05-06

## Capability Matrix

Add a small data model in Simple lib or OS docs first, then promote to code:

- `WineCapabilityId`: process, vm, posix_fd, async, pthread, dynload, fs_semantics, ipc_wait, renderer2d, wm_backend, audio, fonts, input, pe_loader, hello_exe.
- `WineCapabilityState`: missing, scaffold, partial, ready, verified.
- `WineCapabilityEvidence`: path, command, last_result, notes.

## 2D Renderer/WM Target

The target is X11-class behavior, not necessarily X11 protocol wire compatibility:

- display/screen discovery;
- window create/map/unmap/destroy/configure;
- surface allocation and present;
- clip regions, damage, expose events;
- blit/fill/text/glyph operations;
- keyboard, pointer, cursor, clipboard, focus;
- event queue with deterministic replay for tests.

The Phase 1 readiness contract lives in `src/lib/common/ui/x11_backend_gate.spl`.
It is intentionally a gate over native SimpleOS backend semantics, not an X11
server. Wine-facing graphics work must satisfy that gate before claiming a GUI
backend is ready.

## VM/Container Target

Extend current VMM/process work with:

- reserve/commit/protect/unmap API;
- fixed-address mapping checks;
- executable and non-executable page permissions;
- guard pages and stack growth policy;
- page fault records;
- container namespaces for pid, fs, ipc, net, and capabilities.

The Phase 1 readiness contract lives in `src/lib/common/wine_vm_gate.spl`.
It checks Wine-level VM and namespace prerequisites before any PE execution
milestone can advance.

## POSIX And Thread Target

Simple lib adapters expose compatibility APIs over native services:

- fd table and descriptor inheritance;
- pipes, sockets, timers, poll/select-like waits;
- errno mapping;
- pthread create/join/detach;
- TLS keys and per-thread exception state;
- mutex, condvar, semaphore, event wait objects.

The Phase 1 host-substrate readiness contract lives in
`src/lib/common/wine_host_gate.spl`. It covers the "all other features" bucket:
POSIX fd/process/timer behavior, filesystem semantics, server IPC/handles,
pthread/TLS/synchronization, dynamic loading, audio, fonts, crypto, HID,
printing, and multimedia.

## `nogc_async_mut` Async Target

Wine-facing host waits and I/O are based on the existing async library set:

- `nogc_async_mut.async.future.Future` and `nogc_async_mut.async.poll.Poll`;
- `nogc_async_mut.io.driver.IoDriver` completion submission and polling;
- `nogc_async_mut.io.event_loop.EventLoop` fd registration and deregistration;
- `nogc_async_mut.io.event_loop.Waker` wake callbacks;
- `nogc_async_mut_noalloc` capability/no-heap constraints for low-level paths.

The Phase 1 async readiness contract lives in
`src/lib/common/wine_async_gate.spl`. `hello.exe` remains blocked unless this
gate is represented as `async=verified` together with process, VM, host, POSIX,
thread, dynamic-loader, and PE-loader gates.

## PE/COFF `hello.exe` Target

Stage 1 is pure parse/validate:

- DOS header and `MZ`;
- PE signature;
- machine type x86_64;
- optional header PE32+;
- section table bounds;
- import table summary;
- relocation table summary;
- TLS directory summary;
- console subsystem check.

Stage 2 maps image sections into a non-executable sandbox object.
Stage 3 runs only a known non-GUI fixture after VM, process, async, thread, and import gates are verified.

The Phase 1 PE readiness contract lives in `src/lib/common/wine_pe_gate.spl`.
It blocks `hello.exe` until the loader proves safe validation and mapping
behavior without executing arbitrary PE code early.

## Error Handling

All unsupported features return structured errors such as:

- `UnsupportedMachine`;
- `UnsupportedSubsystem`;
- `MissingCapability`;
- `UnsafeVmState`;
- `UnsupportedImport`;
- `InvalidPeBounds`.
