# WM / GUI / Web Host Platform Matrix

**Status:** read-only audit, 2026-08-05. No source was modified.
**Scope:** the host seam under the portable WM/GUI/web stack — 2D surface creation
+ event delivery — across macOS, Windows, FreeBSD, SimpleOS, Linux.

**Portability contract under audit:** *"if Simple 2D (rendering + event delivery)
runs on SimpleOS, the WM runs on SimpleOS."* Generalized: the WM is portable code
sitting on a host seam; each platform must implement that seam.

## Headline

The seam is **not one seam**. Six independent host layers exist with divergent
bodies and no common selector:

| # | Layer | Platform coverage |
|---|---|---|
| 1 | `src/lib/nogc_async_mut/wm/host.spl` (new, sibling lane) | linux, simpleos — **imported by nothing** |
| 2 | `src/lib/nogc_async_mut/wm/{compositor,input,service}.spl` | platform-blind |
| 3 | `src/os/services/wm/` | simpleos (real IPC) |
| 4 | `src/os/compositor/hosted_backend*.spl` + `src/runtime/hosted{_cocoa,_win32}.c` + `src/runtime/hosted/*.rs` | macos, windows, sdl2/winit |
| 5 | `src/lib/*/play/wm/` (4 tiers) | macos, linux, windows — drives *existing* windows |
| 6 | `src/lib/gc_async_mut/gpu/engine2d/backend_*.spl` | GPU backends, no OS branching |

**FreeBSD has no implementation in any of the six.** Its only appearance in the
entire WM/GUI/GPU tree is two comments.

**The real macOS and Windows backends are unreachable from `src/`** — see the
next section, which outranks every individual stub.

## The central defect: the real backends are unreachable

**Two rival dispatchers exist. The platform-aware one is dead; the live one does
not detect the platform.**

1. **`select_hosted_backend`** — `src/os/compositor/hosted_backend.spl:257-274`.
   This *is* platform-aware: `:254` calls `rt_hosted_select_surface()`, genuinely
   defined at `src/runtime/hosted/select.rs:66` (override atomic →
   `SIMPLE_HOSTED_SURFACE` env `:72` → `cfg!(target_os)` default `:47-53`). Arms:
   `:270 sel == 1` → Cocoa, `:272 sel == 2` → Win32, fallthrough `:274` → winit.

   It is **dead code with zero callers.** Verified repo-wide across `src` and
   `test`: the only three occurrences of the name are its own definition `:257`
   and two comments — one of which, `:35`, is a **TODO admitting the gap**.

   Worse, it **cannot even resolve**: `:271` and `:273` call
   `HostedCocoaBackend.create(...)` / `HostedWin32Backend.create(...)`, and
   **neither method exists** — both files define only `try_create`
   (`hosted_backend_cocoa.spl:40`, `hosted_backend_win32.spl:39`).

2. **`_create_backend_for_kind`** — `src/os/compositor/host_compositor_bootstrap.spl:14-32`.
   This is the **live** path. It branches on `kind: HostBackendKind` — a value
   **passed in by the caller** (`cfg.backend`, `:137`). No `rt_hosted_select_surface`,
   no env var, no target check. **Nothing on the live path detects macOS vs
   Windows vs Linux vs FreeBSD.**

**And nothing ever supplies a native kind.** Verified repo-wide (anchored,
excluding vendor): `HostBackendKind.Sdl2` / `.Cocoa` / `.Win32` appear at exactly
**nine** sites — three *comparisons* in `host_compositor_bootstrap.spl:15,20,25`,
and six *constructions* that are all in test specs
(`test/01_unit/os/compositor/host_compositor_entry_spec.spl:389-391` and its
duplicate `test/unit/os/compositor/host_compositor_entry_spec.spl:171-173`).
**Zero production sites construct a native backend kind.**

Consequence: every live path falls through `:32` to
`HeadlessHostCompositorBackend.new(w, h)`. The genuinely real Cocoa, Win32 and
SDL2 backends — the ones this audit confirms call actual OS APIs — are
**unreachable from `src/`**. The only code that ever selects them is a unit test.

*Scope caveat:* reachability was established over `src/` and `test/`. An
out-of-tree embedder could hand-pass a native kind, which would exercise the real
code. "Unreachable" is scoped to this repo.

**Corollary — the default surface is synthetic even where selection succeeds.**
`hosted_backend.spl:222` `HostedCompositorBackend.create` calls
`rt_winit_buffer_create`, and the whole `rt_winit_buffer_*` family (declared
`:43-52`) has **no native definition anywhere in the repo**. A repo-wide sweep of
all `.rs`/`.c`/`.h`/`.toml` puts all 10 hits under
`src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/`, where
`winit_sffi_buffer.rs:18-31` is `vec![color; w*h]` plus
`NEXT_BUFFER_ID.fetch_add(1)` → `Ok(int_value(id))`. So a **compiled** build of
this path would fail to link; the **interpreted** build returns a synthetic
incrementing handle with no OS window. `:228` returns the backend
unconditionally, with no `buf <= 0` check.

## Matrix

Legend — **real** / **admits** (stub that returns false/error/unsupported) /
**FALSE-SUCCESS** (returns ok/true/a handle while doing no real work).

### Linux

| Capability | Verdict | Evidence |
|---|---|---|
| Surface | **real code, FALSE-SUCCESS default** | Real: `src/runtime/runtime_sdl2.c` (894 lines, 10 real `SDL_*` sites, only version `#if`s), declared `hosted_backend_sdl2.spl:38-55`; real winit via `src/lib/nogc_sync_mut/ui/gui_renderer.spl:115` → `DynLib.open` :131 → `fp_window_new` :156. **But** the default live path never selects them (see central defect) and lands on `HeadlessHostCompositorBackend` or the synthetic `rt_winit_buffer_create` handle |
| Events | **real + FALSE-SUCCESS** | Real: `gui_renderer.spl:198` decodes live winit events. FALSE-SUCCESS: `hosted_input_backend.spl:437-455` `_build_mouse_event()` hardcodes `dx: 0, dy: 0`; `:227` declares `rt_winit_event_mouse_button -> (i64,bool)` but the runtime defines it `-> i64` (ABI mismatch; pressed-ness garbage) |
| Backend | **real** | Vulkan + CUDA verified live on this host (see Execution) |
| Dispatch reachable | **FALSE-SUCCESS** | `select.rs:51-53` has **no linux arm**; linux falls into `else → SEL_WINIT = 0`, and **the crate contains no winit backend** (`:5` calls 0 "winit / linux / anything unknown"). `hosted_backend.spl:269-275` treats 0 as implicit fall-through with no error path |

### macOS

| Capability | Verdict | Evidence |
|---|---|---|
| Surface | **real but unreachable** | `src/runtime/hosted_cocoa.c:251-252` `[NSWindow alloc] initWithContentRect:`, `:263` `makeKeyAndOrderFront`, `:261` `NSImageView`. Compiled on macOS by `src/compiler_rust/runtime/build.rs:158-164` (`-xobjective-c`). Rust twin `src/runtime/hosted/cocoa.rs:242`, gated `#[cfg(all(target_os="macos", feature="cocoa-real"))]` :154. Simple wrapper `hosted_backend_cocoa.spl:40-53` `try_create` guards on `rt_cocoa_window_new` :45 and returns `nil` on failure — correct. Unreachable per central defect |
| Events | **real** | `hosted_cocoa.c:619` `rt_cocoa_event_pump` → `:636` `nextEventMatchingMask:` + `:646` `sendEvent:`. Rust twin `cocoa.rs:507` |
| Backend | **real (Metal) + FALSE-SUCCESS (adapter)** | Honest: `backend_metal.spl:394` `if not is_macos(): return false`; `src/lib/nogc_sync_mut/io/metal_sffi.spl` has 46 real `extern fn rt_metal_*`. FALSE-SUCCESS: `backend_metal_adapter.spl:49,52,55` hardcode `supports_compute/graphics/present → true` **on any host, including this Linux one**; `:47` `readback()` returns `""` (success sentinel) transferring zero pixels |
| Dispatch reachable | **FALSE-SUCCESS at the Simple layer** | `select.rs:47-48` `cfg!(target_os="macos") → SEL_COCOA` is correct but dead. Non-native C/Rust fallbacks are **honest** (`cocoa.rs:84` `-1`; `hosted_cocoa.c:53-106` `-1`/`false`/`0`). The lie is above them: `hosted_backend_cocoa.spl:34-35` `uses_native_cocoa_symbols() -> bool: true` |

### Windows

| Capability | Verdict | Evidence |
|---|---|---|
| Surface | **real but unreachable** | `hosted_win32.c:230` `RegisterClassExW`, `:377` `CreateWindowExW`, `:264` `CreateDIBSection`, `:613` `BitBlt`. Rust twin `win32.rs:281,328,363` gated `#[cfg(all(target_os="windows", feature="win32-real"))]` :145. Wrapper `hosted_backend_win32.spl:39-52` `try_create`. Unreachable per central defect |
| Events | **real** | `hosted_win32.c:850` `rt_win32_message_pump` → `:863` `PeekMessage` + `:882-883` `TranslateMessage`/`DispatchMessage`. Rust twin `win32.rs:823` `PeekMessageW`. *Minor real defect:* `hosted_win32.c:89` includes `windows.h` without `#define UNICODE`, so `PeekMessage` resolves to the **A** variant paired with a **W**-registered class |
| Backend | **FALSE-SUCCESS** | `backend_directx.spl:277` on any host calls `dxvk_d3d11_create_device()` → `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl:184` `val handle = _d11_devices.len() + 1` — **fabricated handle; the file has zero externs**. Its ICD `vulkan_icd_sffi.spl:103-108` increments a counter and always returns `_icd_ok(...)`; never fails. Readback is CPU: `backend_directx.spl:447,455` `engine2d_readback(self.sw.read_pixels(), "cpu_mirror")`. `name():231` self-reports `"directx-software-emulation"` — partial honesty — but `probe_backend` still returns `.success(...)` |
| Dispatch reachable | **FALSE-SUCCESS at the Simple layer** | `select.rs:49-50` correct but dead; C/Rust stubs honest (`win32.rs:55` `-1`). Lie above them: `hosted_backend_win32.spl:33-34` `uses_native_win32_symbols() -> true`. **Build gap:** `build.rs:136` compiles `hosted_win32.c` only when `target_os != "windows"` — the real C Win32 path is never compiled *on Windows*; the Rust provider serves instead |

### FreeBSD

| Capability | Verdict | Evidence |
|---|---|---|
| Surface | **MISSING** | Zero FreeBSD arms in any host backend. `HostBackendKind` (`host_compositor_core.spl:145-153`) has no BSD variant |
| Events | **MISSING** | `hosted_input_backend.spl:4` and `:152` name FreeBSD in **docstrings only**: *"used on macOS, Linux, Windows, FreeBSD host desktops"*. The file has **zero platform arms** — no `if platform ==`, no `match os`, no cfg, no uname, no env var. It is a single unconditional winit path |
| Backend | **MISSING** | Anchored `freebsd\|is_bsd\|\bbsd\b` over `src/lib/gc_async_mut/gpu/**/*.spl` = **0 hits** |
| Dispatch reachable | **FALSE-SUCCESS** | `select.rs:51` lumps FreeBSD into `else → SEL_WINIT = 0`, a backend the crate does not contain. No error is ever raised |

**FreeBSD WM/GUI is unimplemented.** Not partial — absent. The repo's 78 FreeBSD
files are all compiler/linker/package/bootstrap; none touch UI. The docstrings at
`hosted_input_backend.spl:4,152` are the audit's clearest single hazard: they
assert FreeBSD support that no code provides.

### SimpleOS

| Capability | Verdict | Evidence |
|---|---|---|
| Surface | **real** | `src/os/compositor/fb_backend.spl:121` `FramebufferBackend.create(fb: FramebufferDriver, ...)` via `os.drivers.framebuffer.fb_driver`. Note it takes an already-built driver — it is a SimpleOS path, **not** a host-Linux one (no ioctl/mmap/`/dev/fb`, no externs) |
| Events | **real (IPC) + FALSE-SUCCESS (device)** | Real: `src/os/services/wm/wm_service.spl:167` `syscall(SYS_IPC_CREATE_PORT, ...)` with honest failure `:168-171`; `:190` `syscall(SYS_IPC_RECV, port, 0,0,0,0)` blocking, `:214` non-blocking. Constants `:46-48`; `use os.userlib.syscall_raw.{syscall}` `:31`. FALSE-SUCCESS: `arm64_virtio_input_backend.spl:90-95` → `src/os/kernel/arch/arm64/virtio_input.spl:32`, whose `rt_arm64_virtio_input_poll` is **dangling repo-wide** — the poll always takes `return nil` at `:35`, presenting as a quiet, healthy virtqueue |
| Backend | **real / admits** | Framebuffer + software real; `backend_virtio_gpu.spl:135` honestly gates on `virtio_gpu_initialized()` |
| Dispatch reachable | **real, but bifurcated** | SimpleOS does **not** route through `select.rs` (no simpleos arm) or `HostBackendKind`; it uses `src/os/services/wm/` + `fb_backend.spl` directly. The new `host.spl` `WmHostSimpleOs` is a **parallel re-implementation that never calls the kernel and is imported by nothing** |

**SimpleOS is the best-implemented non-Linux platform and the only one with real,
reachable, executable evidence.** The stated contract holds for SimpleOS.

## False-success stubs, ranked

Counting rule: one entry per distinct code site returning success/a handle while
performing no corresponding real work. **31 sites in 6 clusters.**

### Cluster 0 — host-backend dispatch and capability self-report (4 sites)

These sit above everything else: they make a simulated host claim to be native.

0a. **`hosted_backend_cocoa.spl:34-35`** — `static fn uses_native_cocoa_symbols()
    -> bool: true`, hardcoded **regardless of whether `__APPLE__` was compiled
    in**; `:32` reports the name `"cocoa-real-sffi"`. On this Linux host the
    underlying C shim is the honest `#ifndef __APPLE__` stub returning `-1`, yet
    the Simple layer above it reports "real native cocoa".
0b. **`hosted_backend_win32.spl:33-34`** — `uses_native_win32_symbols() -> true`,
    same shape; `:31` reports `"win32-native"`.
0c. **`hosted_backend.spl:222,228`** — synthetic winit buffer handle returned
    unconditionally (see corollary above).
0d. **`hosted_backend_gui_renderer.spl:15-20`** — `create` builds
    `val pixels: [u32] = []` at `:18` and returns
    `HostedGuiRendererBackend.new(renderer, w, h, pixels)` as a valid backend
    whose pixel store is an empty array.

0a and 0b are the purest instances of the pattern this audit was asked to hunt:
a boolean named `uses_native_*_symbols` whose body is a literal `true`.

### Cluster 1 — the new WM host seam (3 sites)

`src/lib/nogc_async_mut/wm/host.spl` is 517 lines that make **zero OS calls and
declare zero externs**, yet present themselves as the canonical host seam.

1. **`host.spl:177-271` — the entire `impl WmHost for WmHostLinux`.**
   `platform()` :178 returns `"linux"`. `supports()` :181-186 returns **`true`
   for all ten capabilities**, including `screen_capture`, `foreign_windows` and
   `process_exec`. `port_open` :197 returns `self.port_ctr + 1` — a counter, not
   an OS handle. `present` :256 increments a field and returns
   `wm_host_status(true, "presented")`. `input_poll` :235 drains an in-memory
   array that only test code fills. `clipboard_get/set` :266,269 read and write a
   struct field. Nothing touches X11, Wayland, evdev or SDL. Anchored search
   confirms **0 occurrences** of `XOpenDisplay`, `XCreateWindow`, `XNextEvent`,
   `wl_display_connect` or `wl_compositor` anywhere in non-vendored source, so no
   real Linux backing exists for it to delegate to.
2. **`host.spl:407-411` — `WmHostSimpleOs.present`** returns
   `wm_host_status(true, "presented")` with no kernel call, while the file's own
   docstring `:16-17` claims SimpleOS *"refuses at runtime rather than answering
   green"*.
3. **`host.spl:342-345` — `WmHostSimpleOs.now_micros`** returns
   `boot_micros + tick_micros`, both initialized to `0` at `:320-322` and never
   updated. The frame report's health check `:515` `clock_advanced: t1 >= t0`
   therefore passes on `0 >= 0` — a frozen clock reports as advancing.

The docstring is its own indictment: `:16-37` carefully enumerates what SimpleOS
*cannot* do and promises honest refusal, and the SimpleOS side does honour that
for clipboard (`:418,421` return `"unsupported:clipboard"`) — but the **Linux**
side claims every capability and implements none.

### Cluster 2 — WM core tier A (7 sites)

`src/lib/nogc_async_mut/wm/`, platform-blind, every success path fabricated:

4. `service.spl:27` `wm_port_open()` → counter handle (`:33-37`); docstring `:3-4`
   claims it opens a connection port to the WM service. Nothing is opened.
5. `service.spl:40` `wm_window_create()` → `_wm_window_ctr + 1` (`:54-60`)
6. `service.spl:62` `wm_port_close()` → `return true` (`:73`) on a flag flip
7. `compositor.spl:116` `wm_compositor_window_present()` → `_ok("presented", ...)`
   (`:124`); the "frame" is `checksum + frame_seed + width*height*4 + id`
   (`:120-121`) — arithmetic in place of pixels
8. `compositor.spl:151` `wm_compositor_poll_input()` → `ok: true, state: "event"` (`:161`)
9. `input.spl:71` `wm_input_poll()` → `ok: true, state: "event"` (`:80`)
10. `wm_optimization.spl:226` `present_batcher_present_batch` returns formatted
    text; nothing presents

**Reachability makes this worse:**
`test/03_system/app/simpleos/feature/simpleos_wine_proton_steam_impl_spec.spl:203-209`
asserts `wm_port_open()` yields a valid port and
`wm_window_create(port, "wine-test", 800, 600)` yields a window handle. Both
assertions pass against counters, so a **system-level spec named for
Wine/Proton/Steam is green while nothing is opened.**

### Cluster 3 — GPU backends and session adapters (10 sites)

11. **`backend_webgpu.spl:277`** — `init()` ends in a bare `true` regardless of
    whether `webgpu_sffi_is_available()` succeeded. Verified directly: the
    `gpu_ready = true` assignment sits three `if`s deep (`:270-275`) while
    `self.initialized = true; true` executes unconditionally. So `probe_backend`
    reports "WebGPU initialized" on a pure-CPU surface.
12. **`backend_webgpu.spl:561`** — `read_pixels_with_source()` is the single
    expression `engine2d_readback(self.buf, "cpu_mirror")`, unconditional.
    *(Calibration case supplied with the task; confirmed exactly.)*
13. `dxvk_d3d11.spl:184` — fabricated D3D11 device handle (see Windows row)
14. `vulkan_icd_sffi.spl:103-108` — ICD always returns `_icd_ok(...)`
15-19. **All five session adapters** return `""` — the success sentinel — from
    `readback()` after validating arguments and transferring **zero pixels**:
    `backend_metal_adapter.spl:47`, `backend_webgpu_adapter.spl:49`,
    `backend_vulkan_adapter.spl:49`, `backend_cuda_adapter.spl:46`,
    `backend_cpu_adapter.spl:42`
20. `backend_metal_adapter.spl:49,52,55` — `supports_*` hardcoded `true` on any host

Mitigation that exists: `engine.spl:960` `detect_best_backend_viable()` → `:910`
`probe_backend_viable()` rejects any backend whose readback source is not
`device_readback` / `host_cache_after_device_present` (`:948`). **This is the only
thing catching the `cpu_mirror` stubs**, and it is a *separate* entry point from
the default `engine.spl:879` `detect_best_backend()`, which does not check.

### Cluster 4 — input event sources (5 sites)

21. `hosted_input_backend.spl:437-455` `_build_mouse_event()` — `dx: 0, dy: 0`
    hardcoded; a permanently motionless delta reported as a healthy MouseEvent
22. `hosted_input_backend.spl:227` — `rt_winit_event_mouse_button` declared
    `-> (i64,bool)`, runtime defines `-> i64`; pressed-ness silently garbage
23. `hosted_input_sdl2.spl:42-64` `poll_events` — 3 of its 6 externs dangling
    (below), event shapes do not match `src/os/drivers/input/ps2_mouse.spl:52-63`,
    and the file has **no call sites anywhere in `src/`**. It cannot work
24. `hosted_input_sdl2.spl:93-96` — `if code >= 97 and code <= 122: return Key.A`;
    **every lowercase letter maps to `A`**, every digit to `Num0`
25. `arm64_virtio_input_backend.spl:90-95` — dangling poll reads as an idle
    virtqueue (see SimpleOS row)

### Cluster 5 — Rust host crate (2 sites)

26. `src/runtime/hosted/webgpu.rs:80-84` — `shutdown()` returns `true` with the
    comment *"even in stub mode we pretend shutdown 'succeeded'"*. Benign
    (idempotent teardown) but explicitly fabricated
27. `src/runtime/hosted/select.rs:51-53,76-78` — no arm for linux, freebsd or
    simpleos, and an unrecognized `SIMPLE_HOSTED_SURFACE` value also silently
    falls through to `SEL_WINIT = 0`, a backend absent from the crate

*(Sites 28-31 are the four in Cluster 0, numbered 0a-0d above.)*

## Dangling externs (verified repo-wide)

An unresolved extern is **WARN-only** in this repo, so every one of these builds
clean. Confirmed dangling after a repo-wide anchored search excluding vendor:

| Symbol | Declared at | Status |
|---|---|---|
| `rt_sdl2_get_event_type` | `hosted_input_sdl2.spl:5-10`, `hosted_backend_sdl2.spl` | **dangling** — declarations only |
| `rt_sdl2_get_key_code` | same | **dangling** |
| `rt_sdl2_get_mouse_button` | same | **dangling** |
| `rt_arm64_virtio_input_poll` | `src/os/kernel/arch/arm64/virtio_input.spl:11` | **dangling** |
| `rt_winit_buffer_*` (family) | `hosted_backend.spl:43-52` | **no native definition** — interpreter-only |

**Correction carried from an intermediate finding.** A narrower search initially
reported `rt_winit_event_keyboard_input`, `rt_winit_event_mouse_moved`,
`rt_mmio_read_u8` and *all six* `rt_sdl2_*` accessors as dangling. Re-checking
against the full non-vendored tree refuted that: the winit pair is defined in
`src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_input.rs`,
`rt_mmio_read_u8` in `src/runtime/startup/baremetal/runtime_minimal.c`, and
`rt_sdl2_poll_event` / `_get_mouse_x` / `_get_mouse_y` in
`src/runtime/runtime_sdl2.c`. Only the entries above survive. This is the
"a missing object reads as a rewritten history" trap: **a symbol absent from the
directory you searched is not a symbol absent from the repo.**

## Honest implementations — what this audit did *not* find wrong

Recorded so the finding count is not read as blanket condemnation:

- `src/runtime/hosted_cocoa.c` and `hosted_win32.c`: non-native branches return
  `-1` / `false` / `0` throughout. Anchored search finds **zero** `return true` /
  `return 1` inside either stub region. Textbook honest.
- `src/runtime/hosted/{cocoa,win32}.rs`: same discipline (`-1`, `false`, `0`).
- `hosted_backend_cocoa.spl:40-53` / `hosted_backend_win32.spl:39-52`
  `try_create`: correctly guard on the FFI result and return `nil` on failure.
  (The dishonesty is in the sibling `uses_native_*_symbols`, not here.)
- `src/lib/*/play/wm/`: the **only platform-aware tier**. `wm_platform()` at
  `mod.spl:71`, real out-of-process control via `rt_process_run_timeout` :37
  (osascript / xdotool / PowerShell), honest
  `Err(play_error(ERR_BACKEND_UNAVAILABLE, "...unsupported platform"))` at
  `:128,160,264,309,344,382,402`. **Zero false-success sites.** Its three sibling
  tiers are genuine re-exports, not placeholders
  (`nogc_async_mut/play/wm/mod.spl:7-11` → `gc_async_mut:7` → `gc_sync_mut:3`),
  reachable in production from `src/app/cli/theme_sync.spl:22` and
  `src/app/play/wm_access_cli.spl:40`.
- `src/lib/nogc_sync_mut/ui/gui_renderer.spl`: real winit via `DynLib`, and
  exemplary honesty — `:118-119` prints *"is an API stub (not implemented) — no
  window opened"* and returns `nil`; `:136` prints the exact build command on
  dlopen failure.
- `src/os/services/wm/`: real SimpleOS syscalls with real failure paths.
- Metal, Vulkan, CUDA, OpenCL, OpenGL, virtio_gpu backends all gate on genuine
  availability probes and fail honestly.

## What can actually be EXECUTED from this Linux host

| Platform | Executable here? | Detail |
|---|---|---|
| **Linux** | **Partially — headless only** | `DISPLAY` and `WAYLAND_DISPLAY` are **both unset**: there is no graphical session on this host. GPU compute verified live (below). On-screen window creation and real event delivery are **not executable here** — the very paths this audit most needs to test |
| **SimpleOS** | **Yes, via QEMU** | 10+ harnesses: `check-simpleos-x86-64-wm-qemu-readiness.shs`, `-wm-render-event-evidence.shs`, `-wm-hello-lifecycle-evidence.shs`, `check-simpleos-wm-fullscreen-evidence.shs`, `check-simpleos-arm64-wm-qemu-readiness.shs`, others |
| **FreeBSD** | **No — bootstrap only** | `scripts/check/check-freebsd-bootstrap-qemu.shs` exists but is compiler bootstrap. **No FreeBSD WM/GUI harness exists**, because there is no FreeBSD WM/GUI code to harness |
| **macOS** | **No — static only** | Metal.framework absent (confirmed: `/System/Library/Frameworks/Metal.framework` does not exist). **Zero macOS CI runners** — of 69 `runs-on:` declarations, 67 are `ubuntu-latest`, 2 are `windows-latest`. The 16 `check-macos-*` evidence scripts require a physical Mac and can run neither here nor in CI |
| **Windows** | **No locally — CI only** | 2 `windows-latest` runners plus `.ps1` harnesses (`check-windows-d3d12-render-log-evidence.ps1`, `check-windows-native-mdi-evidence.ps1`, `check-windows-gui-web-2d-evidence-bundle.ps1`) |

Host ground truth verified by positive probe, not by file inspection:

- `nvidia-smi`: **NVIDIA RTX A6000**, **NVIDIA TITAN RTX** — matches the stated baseline
- `vulkaninfo --summary`: TITAN RTX and RTX A6000 at apiVersion 1.4.312, plus
  llvmpipe 1.4.318 (software) — **Vulkan works**
- SDL2 and X11/Wayland client libraries present in `ldconfig` (2 and 4 entries) —
  the *libraries* exist even though no display-server session does

## What this audit cannot see

1. **Runtime behaviour on four of five platforms.** macOS, Windows and FreeBSD
   were **statically checked only**. A path that reads real can still fail at
   runtime; a path that reads stubbed can be dead and harmless. Only SimpleOS
   (QEMU) and headless Linux were executable.
2. **On-screen presentation on any platform, including Linux.** With no display
   session on this host, the audit could not confirm that a single pixel reaches
   a single screen anywhere. Every "surface: real" verdict is a **code-reading
   verdict**, not a rendered-frame verdict.
3. **Whether the honest non-native stubs are ever actually selected.** The
   `cfg`/feature gating (`cocoa-real`, `win32-real`) was read, not exercised.
   `native_all` takes default features → stubs on Linux, but which artifact a
   given build links was not proven by execution.
4. **The sibling lane's in-flight work.** `host.spl` is being actively
   consolidated by another lane. Its zero-importer status may be work-in-progress
   rather than abandonment — though the four-tier duplication it sits on top of
   predates it.
5. **Whether the 127 platform-named specs are vacuous.** 127 of 370 specs naming
   macOS/Cocoa/Win32/D3D12/FreeBSD also name a WM/GUI/render concept, yet only
   Linux and Windows runners exist. Whether they skip, mock, or assert against
   the false-success stubs was **not individually verified** — but
   `simpleos_wine_proton_steam_impl_spec.spl:203-209` is a confirmed instance of
   the last kind.
6. **Out-of-tree callers.** The "real backends unreachable" verdict is scoped to
   `src/` and `test/`. An external embedder passing a native `HostBackendKind`
   would exercise the genuinely real code.
7. **Dynamic dispatch in a production launch.** `SIMPLE_2D_BACKEND` /
   `SIMPLE_HOSTED_SURFACE` and `rt_hosted_set_surface_override` were traced
   statically; what a real launch selects was not observed.

## Recommended follow-ups (not performed — read-only lane)

1. Wire a real dispatcher: either give `select_hosted_backend` a caller and fix
   its two calls to nonexistent `create` methods, or have
   `_create_backend_for_kind` derive `kind` from `rt_hosted_select_surface()`
   instead of taking it from the caller. Today no production code can reach the
   native backends at all.
2. Make `uses_native_cocoa_symbols` / `uses_native_win32_symbols`
   (`hosted_backend_cocoa.spl:34-35`, `hosted_backend_win32.spl:33-34`) reflect
   the actual compile-time gate instead of returning literal `true`.
3. Make `WmHostLinux.supports()` (`host.spl:181`) return `false` for everything it
   cannot do, or delete `WmHostLinux` until it has a backing implementation.
   Claiming `screen_capture` and `foreign_windows` from a struct with zero
   externs is the most misleading single construct found.
4. Give `select.rs` explicit `freebsd` / `simpleos` arms that **error** rather
   than silently returning a code for a backend the crate does not contain.
5. Delete the FreeBSD claims from `hosted_input_backend.spl:4,152` or implement
   them. A docstring is the cheapest possible false-success.
6. Route `detect_best_backend()` through the same viability check as
   `detect_best_backend_viable()`, so `cpu_mirror` backends cannot win the
   default path.
7. Define or delete the dangling externs, especially the `rt_winit_buffer_*`
   family that only the interpreter implements.
8. Resolve the four-tier WM duplication: tier A appears to be an abandoned
   re-implementation of tier B (it references the same `SYS_IPC_CREATE_PORT 22` /
   `SYS_IPC_RECV 21` constants tier B actually calls, but never calls them).
