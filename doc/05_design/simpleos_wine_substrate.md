<!-- codex-design -->

# Detail Design: SimpleOS Wine Substrate

Date: 2026-05-06

## Capability Matrix

Add a small data model in Simple lib or OS docs first, then promote to code:

- `WineCapabilityId`: process, vm, posix_fd, async, pthread, dynload, fs_semantics, ipc_wait, renderer2d, wm_backend, audio, fonts, input, pe_loader, hello_exe.
- `WineCapabilityState`: missing, scaffold, partial, ready, verified.
- `WineCapabilityEvidence`: path, command, last_result, notes.

## MDSOC+ Design Rule

The Wine substrate is MDSOC+ based:

- shared Wine contracts and evidence records live in `src/lib/common/wine_*`
  as common tree-node facades;
- kernel VM, scheduler, and driver state remain MDSOC-only;
- long-lived userland state for WM, process/container, registry, wineserver-like
  dispatch, audio, fonts, input, and GUI sessions is modeled as ECS inside the
  owning MDSOC capsule;
- POSIX, Win32, X11-class, and Wine adapters are translation veneers over native
  ports/capabilities and must not own sibling service state directly.

Any new resident Wine-facing service spec must declare its ECS `World`,
components, systems, and public MDSOC port/capability facade before code is
added.

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

The executable-environment serial-log gate also requires MDSOC+ evidence for
the owning capsule, public port/facade, and resident ECS state owner before
VM/full-OS/container markers can be used as compatibility readiness evidence.

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

## Wine Process Session Target

`src/lib/common/wine_process_session.spl` models a Wine process request,
handoff boundary, and controlled hello execution boundary. It validates
executable path and working directory, distinguishes the controlled `hello.exe`
milestone from full Wine readiness, emits a `dry-run-ready` handoff only when
explicitly requested, and can route that controlled hello plan through the
VM-backed hello executor.

Arbitrary `.exe` sessions require `wine_substrate_full_wine_gate(...) ==
"ready"` for planning, but the controlled executor still rejects them as
`unsupported-process-session`. Full-Wine process plans must also pass
`wine_process_validate_full_image(...)`, which runs PE header, section,
directory, import, relocation, TLS, and image-map gates before any future
arbitrary execution boundary can be added. `wine_process_prepare_full_image_handoff(...)`
then maps that validated full-Wine image plus stack/guard regions into a
SimpleOS OS-backed VM process and returns entrypoint, mapped-size, and
no-host-code-jump evidence without executing arbitrary instructions. After
image validation,
`wine_process_inspect_full_imports(...)` exposes a bounded first-import table
inspection result with DLL name and imported symbols for the known-console
binding path. `wine_process_inspect_import_descriptor_table(...)` is the
MDSOC-facing full-image inspection layer for arbitrary process preparation: it
accepts a caller-supplied descriptor bound and per-descriptor symbol bound,
walks all import descriptors up to the null terminator, resolves DLL names, and
counts each thunk table without binding DLLs, patching IATs, or executing
process code. `wine_process_inventory_import_descriptor_thunks(...)` then
projects that descriptor table into descriptor-qualified thunk records with DLL
name, symbol name, thunk index, thunk RVA, and import-name RVA. This inventory
is still read-only preflight data; it is not a loader, resolver, binder, or
execution path. `wine_process_plan_import_dependencies(...)` deduplicates the
descriptor DLL list and accepts only the currently modeled substrate DLL
families (`KERNEL32`, `USER32`, and `GDI32`), returning explicit rejection
evidence for unsupported modules before loader work can begin. It still returns
no module handles, export addresses, bound thunks, or executable state.
`wine_process_plan_import_resolution(...)` is the next process-session preflight
layer: it uses the supported dependency plan, a modeled module table for the
currently covered DLL families, and descriptor-qualified thunk inventory to
prove that each imported symbol has a modeled module handle and procedure
address. The result is still evidence only: no real DLL is loaded, no IAT is
patched, and no arbitrary process code is executed.
`wine_process_plan_import_descriptor_thunk_patch_records(...)` converts that
modeled resolution into descriptor-qualified patch records carrying DLL name,
symbol, descriptor index, lookup thunk RVA, IAT RVA, import-name RVA, and
modeled procedure address. This is the multi-DLL analogue of the older
known-KERNEL32 record plan, but it still stops before VMA permission changes or
IAT writes.
`wine_process_apply_import_descriptor_thunk_patches_in_vma(...)` consumes those
records through the modeled SimpleOS process VMA path: it maps the PE image,
opens a bounded `rw` write window, writes the modeled procedure addresses into
descriptor-qualified IAT slots, restores `rx`, and rechecks the no-host-code
jump policy. The lookup thunk table remains read-only import metadata. This is
still a modeled multi-DLL thunk application over covered DLL families, not real
DLL loading, relocation, TLS callback execution, or arbitrary PE instruction
dispatch.
`wine_process_plan_full_image_loader_runtime(...)` composes the full-image VM
handoff with bounded relocation planning and TLS callback-table planning before
any arbitrary process execution boundary. It returns relocation and TLS runtime
evidence while preserving the no-host-code-jump and no-arbitrary-execution
boundary; it does not mutate VM relocation targets, dispatch TLS callbacks,
load real DLLs, or transfer control to PE code.
`wine_process_apply_loader_relocations_in_vma(...)` then opens a modeled
process VMA write window for the validated image, applies the bounded DIR64
relocation target in the copied image bytes, restores `rx`, and rechecks the
no-host-code-jump policy. This is loader-owned relocation mutation evidence for
the process image, but it still does not dispatch TLS callbacks, load real DLLs,
or execute arbitrary PE instructions.
`wine_process_record_tls_callback_dispatch(...)` composes that relocated image
state with the TLS callback table plan, verifies that the first callback target
is mapped inside the process image, and records a loader-owned TLS callback
dispatch. The record is still non-executing preflight: it does not step callback
instructions, run user code, load DLLs, or cross the arbitrary PE execution
boundary.
`wine_process_bind_known_kernel32_imports(...)`
then plans the currently supported KERNEL32 console binding sequence and
rejects unsupported or incomplete import sets; it still does not patch thunks or
execute arbitrary process code. `wine_process_plan_import_thunk_patches(...)`
turns a supported binding plan into explicit guarded import-thunk evidence for
the CPU execution gate, without mutating image bytes.
`wine_process_cpu_dispatch_preflight(...)` composes that loader evidence with
caller-provided CPU evidence and runs the CPU and instruction-dispatch gates
before any future arbitrary process dispatch can be attempted. It checks
non-import CPU prerequisites before the heavier import-record planning path, so
missing thread/stack/dispatch evidence is rejected without running the PE loader
chain.
`wine_process_prepare_known_console_image(...)` is the shared preflight for
known-console dispatch and execution: it applies the bounded copied-image thunk
patches and returns the patched image plus the composed CPU evidence.
`wine_process_map_known_console_image(...)` then maps that patched image into a
modeled SimpleOS process address space with OS VMA backing, image-map evidence,
and a no-host-code-jump check at the PE entrypoint. This is still a bounded
preflight record; it does not expose writable arbitrary process memory or step
general instructions.
For the mapped known-console path,
`wine_process_apply_known_kernel32_thunk_patches_in_vma(...)` opens a modeled
write window only on that bounded process image, applies the three planned
KERNEL32 thunk records, restores `rx` permissions, and rechecks the
no-host-code-jump policy before dispatch evidence can pass.
`wine_process_plan_known_console_dispatch(...)` then decodes the bounded known
console call sequence from that patched image. The sequence now models
RIP-relative indirect calls through the patched thunk RVAs, so the decoded
targets are the IAT slots rather than direct import-name RVAs, still without
running arbitrary instructions. `wine_process_execute_known_console(...)` runs
only that decoded known-console plan through the existing modeled NT bridge and
returns stdout plus exit code.
`wine_process_resolve_known_kernel32_module(...)` and
`wine_process_resolve_known_kernel32_module_ex(...)` run bounded KERNEL32
`GetModuleHandleW`/`LoadLibraryW` or `LoadLibraryExW`/`GetProcAddress`/
`FreeLibrary` sequences for full-Wine process plans and return
handle/procedure evidence without arbitrary DLL loading. The `LoadLibraryExW`
path currently accepts only the modeled zero-flags case.
`wine_kernel32_plan_dll_search_order(...)` models the DLL basename search lane
used before a real module load is allowed: KnownDlls first, then application
directory, Windows system directories, current directory, and PATH-derived
directories. It returns candidate paths and selected modeled source evidence
without reading host files, mapping DLL images, running DLL entrypoints, or
executing arbitrary PE code.
`wine_dll_prepare_image_map_handoff(...)` composes that search plan with
SimpleOS VM process-space map/unmap primitives while recording the modeled
`NtCreateSection`/`NtMapViewOfSection`/`NtUnmapViewOfSection` lifecycle.
It returns selected DLL path, mapped base, and mapped size, but still does not
read host DLL bytes, keep a real DLL loaded, run DllMain, execute TLS callbacks,
or dispatch arbitrary PE instructions.
`wine_dll_load_session_*` records a modeled loaded-DLL session on top of that
image-map handoff. It tracks DLL name, selected path, mapped base/size, section
handle, refcount, unload, and rollback evidence, but its loaded state is still a
contract record: host DLL bytes are not read, no real DLL view is retained,
DllMain and TLS callbacks are not executed, and arbitrary PE code is not
dispatched.
`wine_dll_entrypoint_lifecycle_gate(...)` adds an explicit non-executing DLL
startup lifecycle gate over that modeled load state. It requires modeled
loaded-image evidence, records loader-lock acquisition, TLS-callback planning,
and DllMain process-attach planning, and returns a hard block if a caller asks
to execute DLL startup code before the real host/file-backed execution gates
exist.
`wine_dll_validate_file_bytes(...)` validates supplied file-backed PE DLL bytes
for the selected DLL path. It checks MZ/PE signatures, x86_64 PE32+ headers,
the DLL characteristic, image size, and a DLL entrypoint RVA, then records that
bytes are present while still blocking persistent DLL views, TLS callbacks,
DllMain, and arbitrary execution.
`wine_dll_probe_candidate_bytes(...)` composes DLL search-order candidates with
a modeled byte-file table, selects the first candidate that has bytes, and then
passes those bytes through the PE DLL byte-validation gate. It provides
search-plus-file-probe evidence without opening real host files, retaining DLL
views, or executing DLL startup code.
`wine_dll_map_file_backed_view(...)` maps validated DLL file-probe bytes into a
retained SimpleOS process image view. It records the selected path, mapped base,
image size, and entrypoint RVA on an OS-backed VMA, but still does not perform
relocations, import binding, TLS callback execution, DllMain, or arbitrary PE
dispatch.
`wine_dll_apply_file_view_relocations(...)` opens a modeled write window on the
retained DLL view, applies bounded DIR64 relocation evidence from
`wine_pe_apply_relocation_plan`, restores `rx`, and verifies no-host-code-jump;
still no import binding, TLS callbacks, DllMain, or arbitrary PE dispatch.
`wine_dll_bind_file_view_imports(...)` composes that relocated retained view
with bounded import descriptor inventory and the modeled KERNEL32/USER32/GDI32
module table. It opens a second modeled write window, patches supported IAT
slots with modeled procedure addresses, restores `rx`, and keeps real DLL
loads, TLS callbacks, DllMain, and arbitrary PE dispatch blocked.
`wine_dll_record_file_view_tls_dispatch(...)` composes the import-bound retained
view with TLS callback-table planning and records loader-lock/TLS-before-DllMain
dispatch evidence. The callback target must map inside the DLL image, but
callback instructions, DllMain, and arbitrary PE code are still not executed.
`wine_dll_prepare_file_view_dllmain_handoff(...)` then prepares a non-executing
DllMain process-attach handoff from the same import-bound retained view. It
requires TLS planning, a byte-mapped DLL entrypoint, and a no-host-code-jump
check, while requests to actually execute DllMain remain hard-blocked.
`wine_dll_record_file_view_startup_fault(...)` composes that DllMain handoff
with modeled VM fault evidence and records the loader-lock release, SEH
dispatch, and startup rollback boundary. Only `deliver-seh` startup faults are
accepted; unsupported policies stay blocked and no TLS callback, DllMain, or
arbitrary PE instruction execution occurs.
`wine_process_resolve_first_import_module(...)` composes the PE first-import
inspection gate with that module resolver, so validated full-Wine process
images can resolve a requested procedure against their first imported KERNEL32
module through the same bounded zero-flags `LoadLibraryExW` table before any
future import-table-wide loader pass is added.
`wine_process_load_and_bind_known_kernel32_imports(...)` then requires that
module-resolution evidence before accepting the known KERNEL32
`GetStdHandle`/`WriteFile`/`ExitProcess` binding plan, preserving a separate
status for imports that are both loaded and bound. It reuses one bounded import
inspection for module resolution and binding so the process-session aggregate
specs do not repeatedly traverse the same PE import table.
`wine_process_plan_known_kernel32_thunk_patch_records(...)` expands the known
KERNEL32 binding plan into bounded patch records for the three modeled import
slots. It derives those record RVAs from the PE first-import lookup thunk table,
then records symbol names, thunk indexes, thunk RVAs, and name RVAs.
`wine_process_apply_known_kernel32_thunk_patches(...)` consumes those records
and writes modeled KERNEL32 procedure addresses into a copied PE image for the
same three known slots. This is still bounded fixture image mutation, not
arbitrary DLL loading, full import-table patching, real OS memory mutation, or
rollback-complete process memory patching.
`wine_process_plan_import_loader_state(...)` owns modeled import-loader module
state for bounded multi-DLL full-Wine process plans. It loads supported
`KERNEL32`/`USER32`/`GDI32` modules through the modeled table, tracks maximum
refcounts, releases every loaded handle after successful import resolution, and
rolls back loaded handles when procedure resolution fails. This records loader
lifetime evidence only; it still does not load host DLLs, run DLL entrypoints,
execute TLS callbacks, patch the IAT, or transfer control to arbitrary PE code.
`wine_process_apply_import_loader_transaction_in_vma(...)` composes that loader
state accounting with descriptor-qualified VMA import patching. The transaction
requires released loader refcounts before the process VMA write window is
accepted, carries the loader counts beside patch counts, and aborts before VMA
patching when modeled module resolution rolls back.
`wine_process_prepare_imported_entrypoint_handoff(...)` consumes the import
loader transaction and exposes the patched process image entrypoint address with
entrypoint mapping evidence. This is still a handoff record only; it does not
execute the entrypoint, dispatch arbitrary PE instructions, load host DLLs, or
run DLL/TLS entrypoints.
`wine_process_record_imported_entrypoint_startup_fault(...)` then composes that
handoff with modeled VM fault evidence and records the process-entrypoint SEH
rollback boundary. The accepted fault must target the imported entrypoint with
`execute` access and `deliver-seh` policy; other policies or addresses stay
blocked before rollback evidence is claimed.
`wine_seh_dispatch_fault(...)` models the first SEH frame-chain gate below that
rollback boundary. It requires a thread-local active frame, a frame address
inside the modeled stack, and a handler address inside the mapped image before
SEH handler handoff evidence is emitted; handlers are still not executed.
`wine_process_plan_import_thunk_patches(...)` consumes those explicit records,
so thunk patch evidence now carries module-loader, record-planning, and
import-thunk preconditions before CPU dispatch preflight can pass.
`wine_import_thunk_binding_gate(...)` also requires
`import-module-loaded`, `import-module-handle-valid`, and
`import-module-loader-sequence`, so callers cannot bypass the process-session
load-and-bind gate by supplying only the older thunk-binding tokens.

`src/app/wine_process_session_plan/main.spl` exposes the controlled hello
process-session handoff as a command. It prints command, substrate readiness,
dry-run handoff status, controlled execution status, and hello stdout.

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
RIP-relative indirect call targets for the known patched thunk slots and the
stdout buffer. The hello probe verifies the import binding plan and CPU
execution plan agree on those thunk RVAs, then
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
file offsets before the hello skeleton is accepted. The scan-only forms include
the bounded frame-pointer prologue and epilogue markers `push rbp`,
`mov rbp,rsp`, and `pop rbp`, so common compiler frame setup can be recognized
without widening into arbitrary dispatch. This keeps unsupported x86_64
execution failures structured while broad instruction dispatch remains future
work.

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
