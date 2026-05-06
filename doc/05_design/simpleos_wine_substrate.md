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

`src/lib/common/ui/wine_x11_adapter.spl` adds a modeled X11-class backend state
for the Wine graphics precondition. It records display/screen discovery,
window create/map/configure/destroy, surface/damage/expose/present, input/focus,
cursor, clipboard, text/glyph, blit, and fill evidence, then feeds the existing
feature, event, and pixel gates. It is a deterministic native-backend contract,
not an X11 protocol server or final Wine graphics driver.

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

`src/lib/common/wine_vm_adapter.spl` adds a modeled address-space adapter for
the PE mapping path. It supports reserve, fixed reserve with overlap rejection,
commit, protect, unmap, guard pages, user-pointer lookup, access-fault
classification, and fault evidence that feeds the existing `wine_vm_gate`.
This is still not a kernel VMM replacement; it is the executable contract the
loader path can depend on while the OS-level VM/container implementation
continues.

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

`src/lib/common/wine_posix_adapter.spl` is the concrete Phase 2 POSIX adapter
contract. It enumerates the Wine-facing fd, stdio, pipe, socket, timer,
poll/wait, cwd/env/argv, spawn, path, lock, and errno APIs, maps blocking-shaped
compatibility calls onto `nogc_async_mut` completion I/O and event-loop
primitives, and derives the `wine_posix_gate` feature string only when the API
coverage and async backend evidence are present. It is still a readiness
contract, not the final syscall implementation.

`src/lib/common/wine_thread_adapter.spl` is the concrete Phase 3 thread contract.
It maps currently available `nogc_async_mut/thread_sffi` thread, mutex, and
condvar symbols, and keeps TLS keys, semaphores, event wait objects, and
per-thread fault records as explicit blockers until implemented.

`src/lib/common/wine_dynload_adapter.spl` is the dynamic-loading coexistence
contract. It recognizes existing native `spl_dlopen`/`spl_dlsym` style support
but does not treat that as Wine-ready until search paths, dependency lists,
link namespaces, relocation application, import binding, TLS callback handling,
PE/native loader boundaries, and structured loader errors are all represented.

`src/lib/common/wine_service_adapter.spl` covers the remaining host-service
preconditions: IPC server, handle table, audio device/buffer, font discovery
and rasterization, crypto random/hash, HID keyboard/pointer, printer spool, and
multimedia timer evidence. It derives the final `wine_host_gate` features only
from complete service pairs, so partial audio/font/crypto/HID coverage cannot
accidentally mark the host substrate ready.

`src/lib/common/wine_precondition_manifest.spl` composes the process baseline,
VM, renderer, host, POSIX, pthread, dynamic loading, async, PE-loader, and NT bridge gate
states into one ordered manifest. Its process evidence requires all five named
desktop apps from REQ-002: Browser Demo, Hello World, Editor, Terminal, and
File Manager.

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
thread, dynamic-loader, PE-loader, and NT bridge gates.

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
Stage 3 runs only a known non-GUI fixture after VM, process, async, thread, import, and modeled NT bridge gates are verified.

The Phase 1 PE readiness contract lives in `src/lib/common/wine_pe_gate.spl`.
It blocks `hello.exe` until the loader proves safe validation and mapping
behavior without executing arbitrary PE code early.

The Phase 1 milestone probe lives in
`src/lib/common/wine_hello_exe.spl`. It checks the full substrate gate string,
validates PE headers, section-table bounds, required data directories, and the
first import descriptor name, and validates mapped relocation and TLS directory
bounds plus the null import descriptor terminator. It resolves only the minimal console
`KERNEL32.dll` import set through `src/lib/common/wine_nt_api_catalog.spl` and
`src/lib/common/wine_nt_import.spl`, including the expected hint/name RVA
bindings for the known imported calls. The catalog marks only `GetStdHandle`,
`WriteFile`, and `ExitProcess` as implemented, while broader `kernel32.dll` and
`ntdll.dll` memory, file, thread/wait, heap, and process-environment calls are
listed as catalogued prerequisites that must not dispatch yet. The import layer
returns a structured binding plan with the expected `GetStdHandle`, `WriteFile`,
and `ExitProcess` RVAs before the CPU plan is accepted.
`src/lib/common/wine_nt_virtual_memory.spl` models the `VirtualAlloc`,
`VirtualProtect`, and `VirtualFree` precondition over the existing Wine VM
adapter. `src/lib/common/wine_nt_file_io.spl` models the `CreateFileW`,
`ReadFile`, and `CloseHandle` precondition over the POSIX/`nogc_async_mut`
adapter. `src/lib/common/wine_nt_thread_wait.spl` models `CreateThread`,
`WaitForSingleObject`, and `GetLastError` over the thread/TLS/wait-object
adapter. `src/lib/common/wine_nt_process_env.spl` models `GetCommandLineW` and
`GetEnvironmentStringsW` over the POSIX/`nogc_async_mut` argv/env contract.
`src/lib/common/wine_nt_heap.spl` models `HeapAlloc` and `HeapFree` with a
deterministic process-heap handle and VM-reservation-backed block tracking.
`src/lib/common/wine_ntdll_bridge.spl` maps the catalogued ntdll/Rtl forms onto
those modeled VM, file, close, and heap preconditions while preserving
underlying readiness failures.
These APIs remain non-dispatchable for arbitrary PE imports until the
broader NT bridge can route them safely. It then checks
entry-point and image-size readiness through
`src/lib/common/wine_image_map.spl`, requires bounded section raw/virtual layout
plus an executable entry section, and asks `src/lib/common/wine_cpu_exec.spl`
for a CPU-level hello execution plan. That CPU plan combines the non-native-jump
CPU/thread envelope, instruction-dispatch evidence, and a tiny x86_64 hello
call skeleton decoded by `src/lib/common/wine_x86_64_decode.spl`, including
relative call targets for the known import payloads and stdout buffer. The
hello probe verifies the import binding plan and CPU execution plan agree, then
passes the CPU plan to the fixture dispatcher before bridging any output. It resolves the concrete
milestone NT calls through `src/lib/common/wine_nt_api_catalog.spl` and
`src/lib/common/wine_nt_bridge.spl`, including stdout handle and byte-count
checks for the modeled `GetStdHandle`, `WriteFile`, and `ExitProcess` call
sequence. It then executes only a
marked known `SIMPLE_WINE_HELLO` fixture that also carries a
`SIMPLE_WINE_STDOUT:` payload through
`src/lib/common/wine_hello_dispatch.spl`. The stdout returned by the runnable
probe is extracted only from the decoded stdout-buffer RVA, then sent through
the NT bridge. The probe result records the modeled stdout handle, byte count,
and exit code as execution evidence. It must not generalize that path to
arbitrary PE programs.

The app entrypoint uses the manifest probe path:
`wine_hello_exe_probe_manifest_evidence(data, manifest, execution_evidence)`.
The manifest proves ordered substrate preconditions first; the separate typed
execution evidence then covers the known CPU envelope and x86_64 dispatch fixture.
This prevents the runnable smoke from bypassing the composed precondition
manifest with a raw gate string.

`src/lib/common/wine_precondition_fixture_builder.spl` builds the known fixture
manifest from the adapter contracts instead of literal `"ready"` strings. The
fixture manifest is derived from the VM adapter, X11-class backend adapter,
host-service adapter, POSIX adapter, thread adapter, dynamic-loader adapter,
async gate, PE-loader gate, modeled NT bridge gate, and the five-app process
evidence contract.

`src/lib/common/wine_x86_64_decode.spl` remains a tiny milestone decoder, but
it now classifies supported, unsupported, and truncated instruction forms at
file offsets before the hello skeleton is accepted. This keeps unsupported
x86_64 execution failures structured while broad instruction dispatch remains
future work.

`src/lib/common/wine_hello_fixture.spl` owns the synthetic milestone PE bytes
and the verified gate list used by tests and the runnable probe, including the
known import call targets and stdout payload. The app entrypoint
`src/app/wine_hello/main.spl` runs that fixture and prints the resulting stdout,
so the command-level smoke check is:

```bash
bin/simple run src/app/wine_hello/main.spl
```

## Error Handling

All unsupported features return structured errors such as:

- `UnsupportedMachine`;
- `UnsupportedSubsystem`;
- `MissingCapability`;
- `UnsafeVmState`;
- `UnsupportedImport`;
- `InvalidPeBounds`.
