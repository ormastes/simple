# SimpleOS Wine/Proton/Steam Implementation Architecture

**Feature:** wine-proton-steam-impl  
**Phase:** arch  
**Date:** 2026-05-07

---

## Purpose

This document designs the path from modeled readiness gates to real,
working implementations across all 10 REQs for Wine/Proton/Steam support
in SimpleOS. It extends and complements the existing arch docs:

- `doc/04_architecture/simpleos_wine_substrate.md`
- `doc/04_architecture/simpleos_wine_wm_vm.md`
- `doc/04_architecture/simpleos_proton_substrate.md`
- `doc/04_architecture/mdsoc_architecture_tobe.md`

---

## D-1: Scope Boundary vs Existing Proton Substrate Doc

The existing `simpleos_proton_substrate.md` states the boundary: "This is a
readiness classifier. It does not implement upstream Proton, Steam client
integration, a Linux ABI, a Vulkan driver, DXVK, VKD3D-Proton, or arbitrary
Windows game compatibility."

**Decision:** that boundary remains valid for the *readiness classifier module*
(`src/lib/common/proton_session.spl`). The new implementation work adds
*parallel implementation modules* alongside each facade. The facades become
thin wrappers that delegate to the real modules rather than returning modeled
evidence. No upstream Proton, DXVK, or VKD3D-Proton source is vendored; we
write Simple-native layers that reproduce the interfaces at each relevant
boundary (Vulkan ICD protocol, PE section layout, NT syscall bridge,
Steam IPC protocol).

---

## D-2: REQ-7 Host-Architecture Assumption

On an x86_64 SimpleOS host, Wine binary execution uses **native dispatch**:
map the PE image, set up TEB/PEB/TLS, enter the PE entry point directly. No
instruction emulator or JIT is written. On non-x86_64 hosts an FEX/box64-class
binary translator would be required, but that is out of scope for this release.
All modules referencing `wine_cpu_exec.spl` assume x86_64 and document this
explicitly.

---

## D-3: Vulkan ICD Transport

Three options: (a) virtio-gpu Venus passthrough, (b) software rasterizer
(lavapipe-class), (c) SFFI shim to host Vulkan loader.

**Decision:** start with (c) SFFI shim (`vulkan_icd_sffi.spl`) because
`src/app/io/vulkan_ffi.spl` already declares the FFI surface and compiled-mode
SFFI is the fastest path to a working ICD. Venus passthrough (a) is the
production target for QEMU-hosted SimpleOS and will be added in a follow-up
(`vulkan_icd_virtio.spl`). Software rasterizer is deferred.

---

## D-4: esync vs fsync Default

esync (eventfd-based NT event/semaphore mapping) is simpler to kernel-land
because it maps directly onto a kevent (kernel event object). fsync
(futex-based) is more efficient under high-contention. **Decision:** implement
kevent + kfutex as the shared kernel primitive; esync userland wrapper lands
first because it only needs kevent, fsync lands second reusing kfutex.

---

## MDSOC+ Placement Rules (Recap)

| Layer | Rule |
|-------|------|
| Kernel page tables, fault handler, TSS/SYSCALL MSR, IRQ, device mmio | MDSOC-only, no ECS |
| Userland services (process supervisor, WM, container mgr, registry, audio, font, Steam/Proton launcher) | MDSOC outer ports/capabilities + ECS World inside |
| `src/lib/common/wine_*.spl` and `src/lib/common/proton_*.spl` facades | Common tree-node contract nodes, no owned long-lived state |
| Compatibility adapters (POSIX, Win32, X11-class, loader, async) | MDSOC outer + stateless or capability-threaded, reuse `nogc_async_mut` |
| Vulkan ICD, DXVK, VKD3D shims | `src/lib/nogc_async_mut/gpu/` (queue/fence are async); must not import `gc_async_mut/gpu/` |

---

## Milestone Staging

| Milestone | REQs | What lands |
|-----------|------|-----------|
| M1 — Kernel Foundation | REQ-4, REQ-1, REQ-3 | Demand paging, page-fault handler, TSS.RSP0/SYSCALL MSR hardening, kevent/kfutex kernel primitives, scheduler-owned PIDs, kernel multi-thread, TLS keys, semaphore, event-wait |
| M2 — Host ABI | REQ-2, REQ-8 | POSIX fd table, stdio, pipes, sockets, timers, errno, cwd/env/argv, spawn; async IoDriver wired to fd register/deregister/wake |
| M3 — Loader + Native Exec | REQ-6, REQ-7 | PE/COFF section mapper, in-guest dlopen/dlsym, NT bridge dispatch, TEB/PEB/TLS setup, native x86_64 entry |
| M4 — Display / WM | REQ-5 | wine_x11_adapter bound to wine_simpleos_window_bridge with real /win records, framebuffer present, input events, clipboard, cursor |
| M5 — Proton | REQ-9, REQ-10 | Vulkan ICD SFFI shim, DXVK D3D9/10/11 stubs, VKD3D D3D12 stubs, shader cache, esync/fsync userland, pressure-vessel container exec, Steam IPC bridge, controller HID |

---

## Module Plan

### M1 — Kernel Foundation (new kernel-side modules)

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| `kernel_process_table` | `src/lib/nogc_async_mut_noalloc/baremetal/process_table.spl` | Scheduler-owned PID registry; maps actor → OS PID | New |
| `kernel_vm_fault` | `src/lib/nogc_async_mut_noalloc/baremetal/vm_fault.spl` | Demand-paging page-fault handler; guard page, copy-on-write, VMA region lookup | New |
| `kernel_tss_syscall` | `src/lib/nogc_async_mut_noalloc/baremetal/tss_syscall.spl` | TSS.RSP0 write, SYSCALL/SYSRET MSR (LSTAR/STAR/SFMASK), kernel stack isolation | New |
| `kernel_namespace` | `src/lib/nogc_async_mut_noalloc/baremetal/namespace.spl` | pid/fs/ipc/net/capability namespace facet records; clone/unshare contracts | New |
| `kevent` | `src/lib/nogc_async_mut_noalloc/baremetal/kevent.spl` | Kernel event object (set/reset/wait/pulse); underpins esync NT events | New |
| `kfutex` | `src/lib/nogc_async_mut_noalloc/baremetal/kfutex.spl` | Futex-like wait/wake on address; underpins fsync and condvar | New |
| `kernel_thread` | `src/lib/nogc_async_mut_noalloc/baremetal/kernel_thread.spl` | Kernel multi-thread creation (clone-thread), TLS segment (FS.base write), kernel-stack allocation | New |

### M1 — Kernel Foundation (userland process supervisor service)

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| `process_supervisor_service` | `src/lib/nogc_async_mut/process/supervisor.spl` | MDSOC+ capsule: ECS World for process records; exposes `ProcessPort` capability; no resident fallback markers | New |
| `process_supervisor_ecs` | `src/lib/nogc_async_mut/process/supervisor_ecs.spl` | ECS components: ProcessRecord, PidComponent, NamespaceRef, ThreadList, VmSpaceRef, ExitStatus | New |

### M1 — thread_sffi extensions

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| `thread_sffi` | `src/lib/nogc_async_mut/thread_sffi.spl` | Add TLS key alloc/set/get, semaphore create/post/wait, event-wait create/set/reset/wait | Modified |

### M2 — Host ABI

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| `posix_fd_table` | `src/lib/nogc_async_mut/posix/fd_table.spl` | Real fd table: open, close, dup, dup2, read, write, seek | New |
| `posix_stdio` | `src/lib/nogc_async_mut/posix/stdio.spl` | stdin/stdout/stderr fd bindings, buffered write | New |
| `posix_pipe` | `src/lib/nogc_async_mut/posix/pipe.spl` | Kernel pipe: create, read, write, close, poll | New |
| `posix_socket` | `src/lib/nogc_async_mut/posix/socket.spl` | AF_UNIX + AF_INET socket create/bind/connect/send/recv | New |
| `posix_timer` | `src/lib/nogc_async_mut/posix/timer.spl` | POSIX timer_create/settime/gettime; maps to kernel kevent | New |
| `posix_errno` | `src/lib/nogc_async_mut/posix/errno.spl` | errno mapping table SimpleOS → POSIX; per-thread errno storage | New |
| `posix_process` | `src/lib/nogc_async_mut/posix/process.spl` | cwd/env/argv access; fork/exec/waitpid bridge to process_supervisor | New |
| `wine_posix_adapter` | `src/lib/common/wine_posix_adapter.spl` | Delegates to posix_* modules; removes modeled gates | Modified |
| `io_driver_fd` | `src/lib/nogc_async_mut/io/fd_driver.spl` | IoDriver impl: register/deregister fd, wake-on-ready (epoll/kqueue backend) | New |
| `wine_async_gate` | `src/lib/common/wine_async_gate.spl` | Delegates to io_driver_fd + EventLoop; removes modeled gate | Modified |

### M3 — Loader + Native Exec

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| `pe_section_mapper` | `src/lib/nogc_sync_mut/ffi/pe_section_mapper.spl` | Maps PE sections (code, data, bss, reloc, rsrc) into VMA; calls wine_vm_adapter | New |
| `pe_import_resolver` | `src/lib/nogc_sync_mut/ffi/pe_import_resolver.spl` | Resolves PE import table entries to NT shim addresses or native exports | New |
| `pe_tls_initializer` | `src/lib/nogc_sync_mut/ffi/pe_tls_initializer.spl` | PE TLS directory init: TLS callbacks, TLS slot array, FS-base TEB setup | New |
| `guest_dlopen` | `src/lib/nogc_sync_mut/ffi/guest_dlopen.spl` | In-guest dlopen/dlsym: search PE load order, link namespaces, dep graph | New |
| `wine_dynload_adapter` | `src/lib/common/wine_dynload_adapter.spl` | Delegates to guest_dlopen + pe_section_mapper; removes modeled gate | Modified |
| `wine_dll_image_loader` | `src/lib/common/wine_dll_image_loader.spl` | Replaces modeled section mapping with pe_section_mapper calls | Modified |
| `wine_dll_view_import_binding` | `src/lib/common/wine_dll_view_import_binding.spl` | Replaces modeled import binding with pe_import_resolver calls | Modified |
| `wine_dll_view_relocation` | `src/lib/common/wine_dll_view_relocation.spl` | Replaces modeled relocation with real base-reloc application | Modified |
| `wine_dll_view_tls_dispatch` | `src/lib/common/wine_dll_view_tls_dispatch.spl` | Replaces modeled TLS dispatch with pe_tls_initializer calls | Modified |
| `nt_bridge_dispatch` | `src/lib/common/wine_nt_bridge.spl` | Real NT syscall dispatch table; maps NtCreateFile, NtWriteFile etc. to posix_fd_table | Modified |
| `wine_cpu_exec` | `src/lib/common/wine_cpu_exec.spl` | x86_64 native entry: sets TEB/PEB (FS.base), enters PE AddressOfEntryPoint; documents x86_64-only assumption | Modified |
| `wine_hello_dispatch` | `src/lib/common/wine_hello_dispatch.spl` | Uses nt_bridge_dispatch for real stdout; not hardcoded payload | Modified |

### M4 — Display / WM

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| `wm_service` | `src/lib/nogc_async_mut/wm/service.spl` | MDSOC+ capsule: ECS World for window sessions; exposes `WmPort` capability | New |
| `wm_service_ecs` | `src/lib/nogc_async_mut/wm/service_ecs.spl` | ECS components: WindowRecord, SurfaceRef, DamageRegion, FocusTag, CursorState, ClipboardBuffer, InputEventQueue, PresentChecksumEvidence | New |
| `win_framebuffer_present` | `src/lib/nogc_async_mut/wm/framebuffer_present.spl` | Writes pixel data to SimpleOS `/win` device; double-buffer swap | New |
| `win_input_dispatch` | `src/lib/nogc_async_mut/wm/input_dispatch.spl` | Reads /win input queue; dispatches keyboard/pointer events to window ECS components | New |
| `wine_x11_adapter` | `src/lib/common/ui/wine_x11_adapter.spl` | Binds to wm_service via WmPort; replaces modeled gate with real present/input calls | Modified |
| `wine_simpleos_window_bridge` | `src/lib/common/ui/wine_simpleos_window_bridge.spl` | Delegates create/map/present/input/clipboard/destroy to wm_service ECS; removes checksum-only evidence | Modified |

### M5 — Proton / Vulkan / Steam

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| `vulkan_loader` | `src/lib/nogc_async_mut/gpu/vulkan_loader.spl` | Vulkan loader: enumerate ICDs, select device, create instance/device | New |
| `vulkan_icd_sffi` | `src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl` | SFFI shim ICD: delegates vkCreateInstance/Device/Queue/Submit to host Vulkan via spl_dlopen | New |
| `vulkan_icd_virtio` | `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl` | Venus virtio-gpu passthrough ICD (follow-up, not M5 landing) | New |
| `vulkan_dispatch` | `src/lib/nogc_async_mut/gpu/vulkan_dispatch.spl` | Vulkan dispatch table: fn pointer table per device/instance | New |
| `dxvk_d3d9` | `src/lib/nogc_async_mut/gpu/dxvk_d3d9.spl` | D3D9→Vulkan translation stubs: CreateDevice, CreateTexture, DrawPrimitive → vk* calls | New |
| `dxvk_d3d10` | `src/lib/nogc_async_mut/gpu/dxvk_d3d10.spl` | D3D10→Vulkan translation stubs | New |
| `dxvk_d3d11` | `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl` | D3D11→Vulkan translation stubs | New |
| `vkd3d_d3d12` | `src/lib/nogc_async_mut/gpu/vkd3d_d3d12.spl` | D3D12→Vulkan translation stubs: CreateDevice, CreateCommandList, ExecuteCommandLists | New |
| `shader_cache` | `src/lib/nogc_async_mut/gpu/shader_cache.spl` | SPIR-V shader cache: key = (pipeline hash, device UUID), store to /cache/shaders | New |
| `esync` | `src/lib/nogc_async_mut/esync/esync.spl` | esync userland: NT event/semaphore → kevent; create/set/reset/wait/signal | New |
| `fsync` | `src/lib/nogc_async_mut/fsync/fsync.spl` | fsync userland: mutex/condvar → kfutex; futex_wait/futex_wake bridge | New |
| `wine_thread_adapter` | `src/lib/common/wine_thread_adapter.spl` | NT thread waits delegate to esync/fsync; TLS keys delegate to thread_sffi | Modified |
| `pressure_vessel` | `src/lib/nogc_async_mut/container/pressure_vessel.spl` | Pressure-vessel container exec: unshare namespaces, pivot_root, exec launcher | New |
| `steam_runtime` | `src/lib/nogc_async_mut/steam/steam_runtime.spl` | Steam runtime ABI: linker namespace setup, LD_LIBRARY_PATH management, runtime rootfs mount | New |
| `proton_launcher` | `src/lib/nogc_async_mut/steam/proton_launcher.spl` | Proton launcher: locate Proton prefix, set up environment, exec wine64/wine through pressure_vessel | New |
| `steamworks_bridge` | `src/lib/nogc_async_mut/steam/steamworks_bridge.spl` | Steamworks IPC bridge: Unix socket to steam process; wraps ISteamClient/ISteamUser messages | New |
| `controller_hid` | `src/lib/nogc_async_mut/steam/controller_hid.spl` | Steam controller HID: /dev/input event read, SDL2-class mapping, XInput/DirectInput bridge | New |
| `steam_service_ecs` | `src/lib/nogc_async_mut/steam/service_ecs.spl` | ECS components: AppRecord, PrefixRecord, ContainerRef, RuntimeRef, ShaderCacheRef, ControllerState, LaunchSessionRecord | New |
| `proton_session` | `src/lib/common/proton_session.spl` | Delegates to proton_launcher + steam_service; removes modeled gates; keeps MDSOC capsule contract | Modified |

---

## Dependency Map

Dependencies flow strictly downward; no circular deps.

```
# M1 kernel — bottom layer
kernel_vm_fault         -> (kernel bare metal, no Simple lib deps)
kernel_tss_syscall      -> (kernel bare metal)
kernel_namespace        -> (kernel bare metal)
kevent                  -> (kernel bare metal)
kfutex                  -> (kernel bare metal)
kernel_thread           -> kevent, kfutex
kernel_process_table    -> kernel_namespace, kernel_thread

# M1 userland process supervisor
process_supervisor_ecs  -> (std.common value types only)
process_supervisor_service -> process_supervisor_ecs, kernel_process_table (via syscall port)

# M1 thread extension
thread_sffi             -> kevent, kfutex (via SFFI)

# M2 host ABI
posix_errno             -> (no deps)
posix_fd_table          -> posix_errno, nogc_async_mut.async.future
posix_pipe              -> posix_fd_table
posix_socket            -> posix_fd_table
posix_stdio             -> posix_fd_table
posix_timer             -> kevent, posix_errno
posix_process           -> posix_fd_table, process_supervisor_service (port)
io_driver_fd            -> posix_fd_table, nogc_async_mut.async.io
wine_posix_adapter      -> posix_fd_table, posix_pipe, posix_socket, posix_stdio, posix_timer, posix_process
wine_async_gate         -> io_driver_fd, nogc_async_mut.async.future

# M3 loader
pe_section_mapper       -> wine_vm_adapter, wine_image_vm_map
pe_import_resolver      -> pe_section_mapper, wine_nt_api_catalog
pe_tls_initializer      -> pe_section_mapper, thread_sffi
guest_dlopen            -> pe_section_mapper, pe_import_resolver, pe_tls_initializer
wine_dynload_adapter    -> guest_dlopen
wine_dll_image_loader   -> pe_section_mapper
wine_dll_view_import_binding -> pe_import_resolver
wine_dll_view_relocation -> pe_section_mapper
wine_dll_view_tls_dispatch -> pe_tls_initializer
nt_bridge_dispatch      -> posix_fd_table, posix_process, wine_ntdll_loader
wine_cpu_exec           -> nt_bridge_dispatch, pe_tls_initializer
wine_hello_dispatch     -> nt_bridge_dispatch

# M4 WM
wm_service_ecs          -> (std.common value types)
win_framebuffer_present -> wm_service_ecs
win_input_dispatch      -> wm_service_ecs
wm_service              -> wm_service_ecs, win_framebuffer_present, win_input_dispatch
wine_simpleos_window_bridge -> wm_service (WmPort)
wine_x11_adapter        -> wine_simpleos_window_bridge

# M5 Proton
vulkan_dispatch         -> (no deps, fn pointer table)
vulkan_icd_sffi         -> vulkan_dispatch, nogc_sync_mut.ffi.dynamic
vulkan_loader           -> vulkan_icd_sffi
dxvk_d3d9               -> vulkan_loader, vulkan_dispatch
dxvk_d3d10              -> vulkan_loader, vulkan_dispatch
dxvk_d3d11              -> vulkan_loader, vulkan_dispatch
vkd3d_d3d12             -> vulkan_loader, vulkan_dispatch
shader_cache            -> nogc_async_mut.io (file), nogc_sync_mut.crypto (hash)
esync                   -> kevent, thread_sffi
fsync                   -> kfutex, thread_sffi
wine_thread_adapter     -> esync, fsync, thread_sffi
pressure_vessel         -> kernel_namespace, posix_process
steam_runtime           -> pressure_vessel, posix_fd_table
proton_launcher         -> steam_runtime, wine_cpu_exec, guest_dlopen
steamworks_bridge       -> posix_socket
controller_hid          -> posix_fd_table
steam_service_ecs       -> (std.common value types)
proton_session          -> proton_launcher, steamworks_bridge, controller_hid, steam_service_ecs, vulkan_loader, shader_cache

# No circular dependencies: verified
# Direction: baremetal syscall.spl < kernel_* < posix_* / thread_sffi < wine_*_adapter < proton_session
```

---

## ECS World Definitions

### ProcessSupervisor ECS World

**Components:** `ProcessRecord { pid: u64, state: ProcessState }`, `NamespaceRef { ns_id: u64 }`, `ThreadList { tids: [u64] }`, `VmSpaceRef { asid: u64 }`, `ExitStatus { code: i32 }`  
**Systems:** `spawn_system`, `wait_system`, `reap_system`, `pid_alloc_system`  
**Port:** `ProcessPort` (capabilities: spawn, kill, wait, get_pid)

### WM Compositor ECS World

**Components:** `WindowRecord { wid: u32, title: text }`, `SurfaceRef { buf_id: u32 }`, `DamageRegion { rect: Rect }`, `FocusTag`, `CursorState { x: i32, y: i32, shape: CursorShape }`, `ClipboardBuffer { data: [u8] }`, `InputEventQueue { events: [InputEvent] }`  
**Systems:** `present_system`, `input_dispatch_system`, `focus_system`, `clipboard_system`  
**Port:** `WmPort` (capabilities: create_window, destroy_window, present, get_input, set_cursor, clipboard_read, clipboard_write)

### Steam/Proton Launcher ECS World

**Components:** `AppRecord { app_id: u64, name: text }`, `PrefixRecord { path: text, arch: text }`, `ContainerRef { container_id: u64 }`, `RuntimeRef { runtime_path: text }`, `ShaderCacheRef { cache_path: text }`, `ControllerState { buttons: u32, axes: [f32; 6] }`, `LaunchSessionRecord { pid: u64, phase: LaunchPhase }`  
**Systems:** `launch_system`, `container_setup_system`, `shader_warm_system`, `controller_poll_system`  
**Port:** `SteamPort` (capabilities: launch_app, list_apps, get_controller_state, warm_shader_cache)

---

## Public API

### Kernel Primitives (`nogc_async_mut_noalloc/baremetal/`)

```
fn kevent_create(auto_reset: bool) -> KEventHandle
fn kevent_set(h: KEventHandle) -> void
fn kevent_reset(h: KEventHandle) -> void
fn kevent_wait(h: KEventHandle, timeout_ns: u64) -> WaitResult

fn kfutex_wait(addr: *u32, expected: u32, timeout_ns: u64) -> WaitResult
fn kfutex_wake(addr: *u32, count: u32) -> u32

fn kernel_thread_create(entry: fn() -> void, stack_size: usize) -> Tid
fn kernel_thread_tls_set(key: u32, val: *void) -> void
fn kernel_thread_tls_get(key: u32) -> *void

fn process_table_alloc_pid() -> Pid
fn process_table_register(pid: Pid, asid: u64, ns: NamespaceRef) -> void
fn process_table_lookup(pid: Pid) -> Option<ProcessTableEntry>
```

### thread_sffi Extensions (`nogc_async_mut/thread_sffi.spl`)

```
fn tls_key_alloc(destructor: fn(*void) -> void) -> TlsKey
fn tls_key_set(key: TlsKey, val: *void) -> void
fn tls_key_get(key: TlsKey) -> *void
fn semaphore_create(initial: u32) -> SemHandle
fn semaphore_post(h: SemHandle) -> void
fn semaphore_wait(h: SemHandle, timeout_ns: u64) -> WaitResult
fn event_wait_create(manual_reset: bool) -> EventWaitHandle
fn event_wait_set(h: EventWaitHandle) -> void
fn event_wait_reset(h: EventWaitHandle) -> void
fn event_wait_wait(h: EventWaitHandle, timeout_ns: u64) -> WaitResult
```

### POSIX fd table (`nogc_async_mut/posix/fd_table.spl`)

```
fn fd_open(path: text, flags: FdFlags) -> Result<Fd, Errno>
fn fd_close(fd: Fd) -> Result<void, Errno>
fn fd_read(fd: Fd, buf: *u8, len: usize) -> Result<usize, Errno>
fn fd_write(fd: Fd, buf: *u8, len: usize) -> Result<usize, Errno>
fn fd_seek(fd: Fd, offset: i64, whence: SeekWhence) -> Result<i64, Errno>
fn fd_dup(fd: Fd) -> Result<Fd, Errno>
fn fd_dup2(fd: Fd, target: Fd) -> Result<Fd, Errno>
```

### PE Loader (`nogc_sync_mut/ffi/pe_section_mapper.spl`)

```
fn pe_map_image(bytes: [u8], vm: VmSpace) -> Result<PeImageRef, PeError>
fn pe_unmap_image(img: PeImageRef) -> void

fn pe_resolve_imports(img: PeImageRef, catalog: NtApiCatalog) -> Result<void, PeError>
fn pe_apply_relocations(img: PeImageRef, load_delta: i64) -> Result<void, PeError>
fn pe_init_tls(img: PeImageRef) -> Result<void, PeError>
fn pe_entry_point(img: PeImageRef) -> *void
```

### In-guest dlopen (`nogc_sync_mut/ffi/guest_dlopen.spl`)

```
fn guest_dlopen(path: text, flags: u32) -> Result<GuestModuleHandle, DlError>
fn guest_dlsym(handle: GuestModuleHandle, symbol: text) -> Result<*void, DlError>
fn guest_dlclose(handle: GuestModuleHandle) -> void
```

### WM Port (`nogc_async_mut/wm/service.spl`)

```
fn wm_create_window(title: text, rect: Rect) -> Result<WmWindowHandle, WmError>
fn wm_destroy_window(h: WmWindowHandle) -> void
fn wm_present(h: WmWindowHandle, buf: *u8, stride: u32) -> Result<void, WmError>
fn wm_get_input(h: WmWindowHandle) -> Option<InputEvent>
fn wm_set_cursor(h: WmWindowHandle, shape: CursorShape) -> void
fn wm_clipboard_read() -> [u8]
fn wm_clipboard_write(data: [u8]) -> void
```

### Vulkan Loader (`nogc_async_mut/gpu/vulkan_loader.spl`)

```
fn vk_loader_init() -> Result<VkLoaderHandle, VkError>
fn vk_create_instance(info: VkInstanceCreateInfo) -> Result<VkInstance, VkError>
fn vk_enumerate_physical_devices(inst: VkInstance) -> [VkPhysicalDevice]
fn vk_create_device(pdev: VkPhysicalDevice, info: VkDeviceCreateInfo) -> Result<VkDevice, VkError>
```

### esync (`nogc_async_mut/esync/esync.spl`)

```
fn esync_create_event(manual_reset: bool, initial_state: bool) -> EsyncHandle
fn esync_set_event(h: EsyncHandle) -> void
fn esync_reset_event(h: EsyncHandle) -> void
fn esync_wait_for_multiple(handles: [EsyncHandle], wait_all: bool, timeout_ms: u32) -> WaitResult
fn esync_create_semaphore(initial: u32, max: u32) -> EsyncHandle
fn esync_release_semaphore(h: EsyncHandle, count: u32) -> void
```

### fsync (`nogc_async_mut/fsync/fsync.spl`)

```
fn fsync_mutex_lock(addr: *u32) -> void
fn fsync_mutex_trylock(addr: *u32) -> bool
fn fsync_mutex_unlock(addr: *u32) -> void
fn fsync_condvar_wait(cv: *u32, mutex: *u32, timeout_ns: u64) -> WaitResult
fn fsync_condvar_signal(cv: *u32) -> void
fn fsync_condvar_broadcast(cv: *u32) -> void
```

### Steam/Proton (`nogc_async_mut/steam/proton_launcher.spl`)

```
fn proton_launch_app(app_id: u64, exe_path: text, prefix_path: text) -> Result<Pid, ProtonError>
fn proton_shutdown_app(pid: Pid) -> void
class ProtonLaunchRecord { app_id: u64, pid: Pid, container_id: u64, phase: LaunchPhase }
```

---

## Requirement Coverage

| REQ | Primary modules | Milestone |
|-----|----------------|-----------|
| REQ-1 | `process_supervisor_service`, `process_supervisor_ecs`, `kernel_process_table` | M1 |
| REQ-2 | `posix_fd_table`, `posix_stdio`, `posix_pipe`, `posix_socket`, `posix_timer`, `posix_errno`, `posix_process`, `wine_posix_adapter` | M2 |
| REQ-3 | `kernel_thread`, `thread_sffi` (TLS keys, semaphore, event-wait), `kevent`, `kfutex` | M1 |
| REQ-4 | `kernel_vm_fault`, `kernel_tss_syscall`, `kernel_namespace`, `process_supervisor_service` | M1 |
| REQ-5 | `wm_service`, `wm_service_ecs`, `win_framebuffer_present`, `win_input_dispatch`, `wine_x11_adapter`, `wine_simpleos_window_bridge` | M4 |
| REQ-6 | `pe_section_mapper`, `pe_import_resolver`, `pe_tls_initializer`, `guest_dlopen`, `wine_dynload_adapter` | M3 |
| REQ-7 | `wine_cpu_exec`, `nt_bridge_dispatch`, `wine_hello_dispatch` | M3 |
| REQ-8 | `io_driver_fd`, `wine_async_gate`, `posix_fd_table` | M2 |
| REQ-9 | `vulkan_loader`, `vulkan_icd_sffi`, `vulkan_dispatch`, `dxvk_d3d9/10/11`, `vkd3d_d3d12`, `shader_cache` | M5 |
| REQ-10 | `esync`, `fsync`, `pressure_vessel`, `steam_runtime`, `proton_launcher`, `steamworks_bridge`, `controller_hid`, `steam_service_ecs`, `proton_session` | M5 |
