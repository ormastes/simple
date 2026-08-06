# Design: Screen-Type Selection, Shared Showcase Stack, Input HAL, 2D Perf

Date: 2026-08-06. Research basis: five parallel agent sweeps (SimpleOS boot/config,
engine2d/SIMD, ui widget stack, input/HAL/Vulkan, 2D optimization literature).
Companion plan: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md`.
Complements (does not replace) `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md`
(evidence gates) and `doc/04_architecture/os/shared_wm_stack.md`.

## 1. Current state (verified 2026-08-06)

### Screens / display
- `src/os/kernel/boot/init_services.spl:179` `_init_display_service()` hardcodes BGA
  1024x768x32. No selection point.
- A real common surface trait already exists: `CompositorBackend` +
  `CompositorGlassCapable` in `src/os/compositor/display_backend_core.spl`
  (width/height/clear/fill_rect/draw_text/blit_pixels/present/present_rect).
  Implementors: hosted (winit/win32/cocoa/sdl2), browser, engine2d overlay, GPU.
  **Correction (WS-A detail, verified):** `FramebufferBackend`
  (`fb_backend.spl:121`) implements `RenderBackend`, **not** `CompositorBackend` —
  the factory's four arms are therefore not uniform and the fb arm needs an
  adapter. Constructor signatures differ per arm (`GpuCompositorBackend.new`,
  `Engine2dCompositorBackend.create_named/create_from_env`,
  `browser_compositor_backend(w,h)`, `select_hosted_backend(...)`,
  `baremetal_engine2d_overlay_backend`).
- Per-screen renderers exist but are constructed ad hoc at disparate call sites:
  2D (`compositor_engine2d.spl`), web (`web_render_surface.spl`,
  `simple_web_window_renderer.spl`), GUI (`simple_gui_hosted_wm.spl`), WM
  (`shell.spl` + `wm_core.spl`). `dual_backend.spl` is a compare harness, not a selector.

### Config
- Only guest boot config is `/etc/rc.conf` (`src/os/kernel/boot/rc_conf.spl`):
  boolean `*_enable` keys + `hostname`, key-whitelisted, defaults to enabled.
  Cannot express `screen_type="web"` today.
- `src/os/simpleos_config_matrix.spl` (`SimpleOsRuntimeProfile`) is a test-gating
  capability/evidence contract, NOT a runtime switch — must feed, not become, the
  runtime policy.

### UI widget stack
- **`DrawIrV3Scene` is the real shared render contract** (packed scene +
  HIT_SHAPES/OWNER_RECORDS). GUI: `widget_draw_ir` → `draw_ir_v2_to_v3` via
  `ui_gui_packed_producer.spl`. Web: `ui_web_packed_producer.spl`. Same output type.
- `app.ui.render` is a string (text/html) contract for ~20 CLI apps — unrelated seam.
- Three divergent "HALs": `RenderBackend` trait (`common/ui/backend.spl`) — imported
  by **8** targets (WS-B verified; §1 previously said 7), **never impl'd**;
  `GuiRenderer.present_argb_u32`+`poll_event` (raw pixels,
  `src/app/browser/gui_window.spl`); WM file/env process contract
  (`wm_app_process_contract.spl`).
  Six importers are under `src/app/ui.*`, but **two are OS-side**
  (`fb_backend.spl:15`, `browser_backend.spl:16`). Consequence: `ScreenHost` is
  **additive, not a rename** — renaming would drag WS-B into WS-A/WS-C's files.
  All 8 keep their existing import unchanged.
- **Fail-open specs (WS-B verified):** `common.ui.backend_factory` does not exist
  repo-wide, yet seven specs import `create_backend` from it. An unresolved `use`
  is only a WARN, so those specs prove nothing and must not be cited as coverage.
- **`WmFsAppEvent{seq,kind,x,y,button,pressed}` carries no key/char/wheel field** —
  keytype-on-WM (AC-5) is physically blocked until the struct is extended
  (`key_code`, `ch`, `mods`, `wheel`, defaulted).
- **`ShowcaseSurface` is `Standalone|HostWm|SimpleOsWm`** — no Web, no 2D variant,
  so "flip the readiness bits" was unimplementable as written; the enum needs a
  schema change first.
- **`WidgetNode` is a handle over a module-global store** (`struct WidgetNode:
  id: text`). So showcase logic is "no I/O, no host imports", *not* pure; linked-panel
  sync is a post-dispatch prop mirror rather than a `widget_hit.spl` change; and each
  spec needs a distinct widget-id prefix or examples collide on the global registry.
- No shared pointer-event ingress type: `UIEvent` is semantic (no x/y); each backend
  calls `widget_hit.widget_dispatch_*` itself.
- `examples/06_io/ui/widget_showcase_gui.spl` hand-draws with engine2d primitives,
  bypassing the shared pipeline. `showcase_catalog.spl` readiness bits: all false.

### Input
- PS/2 keyboard (`src/os/drivers/input/ps2_keyboard.spl`) and mouse
  (`ps2_mouse.spl`) implemented, **polled only** — no IRQ1/IRQ12 registration.
- No `HalInput` in `src/os/kernel/arch/hal.spl`. De-facto abstraction is
  `trait InputBackend` (`src/os/compositor/input_backend.spl`).
- `src/os/drivers/input/input_event.spl` (`InputEventQueue`, Key/Mouse/Touch/Gamepad
  events) has **zero consumers** — dead parallel type system; two incompatible
  `MouseEvent` types (compositor.spl:6-13 warns about this).
  **Correction (WS-C detail, verified):** `InputEventQueue` (`:226`) is not a queue —
  it is four counters plus last-seen scalars and stores no events at all. It must be
  written, not merely rewired.
- No SDL2 `InputBackend` impl on host (winit only). Mouse wheel dropped end-to-end
  (open bug `wm_mouse_wheel_events_dropped_2026-07-05.md`). A third input model
  exists in `game2d/input/` (`InputSnapshot`).

### 2D performance (why it is slow)
Hot path: `render_adapter.spl` → `browser_renderer.spl` → `scene.spl` →
`gc_async_mut/gpu/engine2d/backend_software.spl` (rasterizer) →
`nogc_sync_mut/gpu/engine2d/simd_kernels.spl` → `runtime_simd_dispatch.c` (native)
or `interpreter_extern/simd.rs` (interpreted). Ranked defects:
1. Interpreted extern bridge is O(framebuffer) per span (`simd.rs`
   unpack/pack_u32_array rebuild the whole array per call). Native C path is
   in-place O(count) — catastrophic interpreted-only.
2. Alpha blend SIMD is net-negative: gather→native→scatter = 3 interpreted
   per-pixel passes replacing 1 (`simd_kernels.spl:372-392`, duplicated in
   `backend_software.spl:621/:764`). No in-place `blend_span` extern exists
   (fill/copy have one at `simd_native_rows.spl:5,6`).
   Escalation (WS-D detail, verified): even the *native*
   `rt_engine2d_simd_blend_row_u32` (`runtime_simd_dispatch.c:1454`) mallocs two
   scratch buffers and unbox/reboxes every pixel (`:1467-1476`) — blend is bad on
   the native path too, not only interpreted.
3. `simd_fill_row` allocates a native row then copies back per element — slower
   than scalar. Blit is unconditionally scalar.
4. Damage tracking is write-only: `dirty_tiles` marked at 6 sites, cleared in
   `present()`, read by nobody. `tile.spl get_dirty_tiles()` unwired.
5. No batching, no double buffer, no layer cache; `read_pixels()` copies per-pixel
   interpreted.
- Facade inconsistency: `gc_async_mut` simd facades point at two different owner
  trees; canonical owner is `nogc_sync_mut/gpu/engine2d/`. **Worse than described
  (WS-D verified):** `nogc_async_mut/gpu/engine2d/` carries its own full
  `simd_kernels.spl` + `simd_provider.spl` *bodies*, not facades — a real second
  implementation to delete, not a `use` to repoint.
- **Representation constraint (WS-D verified):** pixel words are **boxed
  `int64_t`** (`engine2d_box_pixel`/`unbox_pixel`), not `uint32_t*`. Every new C
  kernel must keep that discipline; SSE2/AVX2/NEON sketches may not silently assume
  packed u32. Unboxing to a packed buffer is exactly the cost being removed, so the
  boxing decision itself is the deeper lever if kernels stay allocation-bound.
- Config hooks today: `native_simd_spans` flag, `SIMPLE_2D_BACKEND` env,
  `variants/ui/renderer/*`; no per-kernel SIMD override.
- Evidence: `doc/09_report/gui_perf_benchmark_2026-07-10.md` (p50 2389 ms vs Cairo
  0.032 ms draw-only); harness `test/perf/graphics_2d/bench_harness.spl`.

### Vulkan / GPU
- virtio-gpu **2D** driver real (`src/os/drivers/virtio/virtio_gpu*.spl`, ~1710 L),
  PCI BAR mapping + DMA syscalls 83/84 implemented.
- **WS-E verified:** only opcodes `0x0100`–`0x0107` + cursor `0x0300/0x0301` exist
  (`virtio_gpu_types.spl:13-20`); every 3D/capset/blob opcode is absent, and only
  `VIRTIO_GPU_CONTROLQ` is wired. Feature negotiation **acks nothing** —
  `virtio_gpu_init.spl:48-57` writes VERSION_1 only, legacy paths write guest
  features `= 0`, so VIRGL/BLOB/CONTEXT_INIT are rejected by construction.
- **Evidence-gate defect (WS-E, must fix before any Vulkan claim):**
  `scripts/check/check_simpleos_multiconfig_live_evidence.spl:145` hard-equals
  `virtio-gpu-pci,disable-modern=on,disable-legacy=off` — the legacy 2D device,
  which cannot expose a Venus capset. The fix is a lane-keyed allow-list that
  *tightens* (blocks a Vulkan claim asserted on the 2D device), never loosens.
- `vulkan_icd_virtio.spl` is 182 L, fully modeled; `_venus_transport_send:52`
  increments a counter and returns a fake handle. Its opcode enum `1..5` is
  invented, not Venus `VkCommandTypeEXT`.
- Vulkan on SimpleOS **does not exist**: `vulkan_icd_virtio.spl` Venus transport is
  modeled/stubbed. Needs virtio-gpu 3D (virgl/Venus) feature bits + real ring
  transport. Host Vulkan lives in the Rust runtime.

## 2. Target design

### 2.1 Screen-type selection (config)
- Extend `rc_conf.spl` with string-valued keys: accept `screen_type="wm|2d|web|gui"`
  (default `wm` = today's behavior) plus `screen_res`, `screen_simd` (see 2.4).
  Add `rc_conf_value(key) -> text?` accessor; keep `*_enable` semantics unchanged.
- New `src/os/compositor/backend_factory.spl`: registry keyed by screen_type →
  constructs the matching `CompositorBackend` + screen app shell. Fail-closed:
  consult `SimpleOsRuntimeProfile` capability flags; unsupported type on a profile
  → log + fall back to `wm` (never blank screen).
- `_init_display_service()` calls the factory instead of hardcoding BGA.
- Host harness honors the same selection via existing `SIMPLE_2D_BACKEND` env
  convention (`SIMPLE_SCREEN_TYPE` env mirrors rc.conf key) so showcases run
  identically on host and guest.

### 2.2 One host interface (the only per-target code)
Make `RenderBackend` (`src/lib/common/ui/backend.spl`) the single host interface and
actually implement it. Final shape:

```
trait ScreenHost:                      # renamed/extended RenderBackend
    fn size() -> (i32, i32)
    fn present_scene(scene: DrawIrV3Scene)   # packed contract — the seam
    fn poll_input() -> HostInputEvent?       # unified ingress
```

- `HostInputEvent` = one shared type: `Pointer{x,y,button,pressed,wheel}` |
  `Key{code,ch,down,mods}` | `Resize{w,h}`. Lives in `src/lib/common/ui/`
  (pure). Replaces per-backend ad-hoc ingress; adapters translate
  winit/SDL2/WM-file-events/PS2 into it. The dead `input_event.spl` queue is
  deleted or rewritten to carry this type (one MouseEvent, not two).
- Four impls, each thin: `wm` (via `wm_app_process_contract` file/env bridge),
  `gui` (SDL2/winit window, wraps `GuiRenderer`), `web` (HTML/DOM bridge via
  `ui.web` server), `2d` (direct engine2d framebuffer / SimpleOS fb).
- Everything above `ScreenHost` — widget tree, layout, hit-testing, event reducer,
  DrawIR production — is shared, byte-identical across targets. Arch check: showcase
  modules may import only `std.*` common/ui + `ScreenHost`; enforced by a
  `simple_check_arch`-style dependency test.

### 2.3 Showcases (same logic, different host)
One shared core `showcase_core.spl` (widget tree: toolbar widget, scroll panel with
scrollbar, two linked panels — scrolling one scrolls the other, event probe pane
logging click/drag/keytype) + 4 thin mains (2d/web/gui/wm) that only pick the
`ScreenHost` impl. Fix `widget_showcase_gui.spl` to use the shared pipeline instead
of hand-drawn engine2d calls. Flip `showcase_catalog.spl` readiness bits only with
captured evidence (play_wm/play_sdl2 screenshots + event transcripts).

### 2.4 Input path to simple-2d
**Ruling (WS-C detail): no `HalInput` trait.** `hal_current.spl:36` is x86_64-hardwired,
so routing input through the HAL would make PS/2 the only reachable device on every
build and orphan the virtio/USB/host backends. `InputBackend` stays the abstraction
(already runtime-selected via the optional `Compositor.input`). The one genuinely
arch-specific piece, `HalInterrupt.interrupt_set_handler`, already exists
(`hal.spl:128` → `:386` → `hal_current.spl:159` → `arch_adapt/x86_64/interrupt.spl:27`)
and is used as-is — nothing is added to `hal.spl`.
- Keep polling as the baseline (works today); add IRQ1/IRQ12 handlers via
  `HalInterrupt.interrupt_set_handler` feeding the (rewritten) single event queue;
  polling remains as fallback behind the same queue API. Drivers split into
  `isr_ingest()` (status read, one `port_inb`, fixed ring store, EOI — no alloc, no
  text, no trait dispatch) and `decode_pending(queue)`; the poll loop calls the same
  `isr_ingest`, so the two modes differ by one line and `SIMPLE_PS2_IRQ=off` must
  produce an identical transcript.
- `InputBackend` impls converge on producing `HostInputEvent`.
- Add SDL2 `InputBackend`/host impl (gap: winit-only today). Fix mouse wheel
  end-to-end (open bug). PS/2 mouse gains Z-byte wheel packet support.

### 2.5 2D performance design (ordered by measured impact)
1. **In-place span kernels incl. blend**: add `blend_span(dst_handle, offset,
   src_handle, count)` + `blit_row` externs to `runtime_simd_dispatch.c` (SSE2
   baseline, AVX2 dispatch) and route `simd_kernels.spl` to them; delete
   gather/scatter blend paths (both duplicates). Fix `simd_fill_row` copy-back.
2. **Interpreter bridge O(n)**: make `simd.rs` extern ops operate on the rt array
   buffer in place (no unpack/pack of the whole framebuffer per span).
3. **Damage-driven present**: wire the already-marked `dirty_tiles` through
   `get_dirty_tiles()` → `present_rect` per dirty tile; full present only when
   whole-frame dirty. Widget layer: bbox invalidation feeds tile marking.
4. **Fast paths**: premultiplied ARGB internal format, opaque → copy path,
   alpha==0 skip, per-surface opaque flag.
5. **Per-window backing store + occlusion** in `wm_core`/compositor: windows own
   buffers, compositor blits visible regions top-down, drag = blit, scroll =
   memmove + damage revealed strip.
6. **Glyph atlas** (A8 shelf-packed, masked SIMD blit) for terminal/browser text.
7. **SIMD config** (`screen_simd` rc.conf key + `SIMPLE_2D_SIMD` env):
   `auto|off|sse2|avx2|neon` + per-kernel toggles (fill/copy/blend/blit) — needed
   both for perf tuning and because disabling SIMD spans is a *speedup* under the
   interpreter until (2) lands. Default: auto (native), off (interpreted) until
   bridge fix proves otherwise on the bench.
- Every step gated by `test/perf/graphics_2d/bench_harness.spl` before/after on a
  pinned worktree, native binary (not seed, not interpreter), reported in the
  campaign report. Guard against known traps: `SIMPLE_EXECUTION_MODE=native` is
  not a mode; measure with the deployed self-hosted binary.

### 2.6 Vulkan on SimpleOS
Phased on top of the existing virtio-gpu 2D driver: (a) negotiate VIRGL/Venus
feature bits + capsets; (b) 3D context create + Venus ring transport over ctrlq
using existing MapBar/AllocDma syscalls; (c) point `vulkan_icd_virtio.spl` at the
real transport, replacing modeled responses; (d) evidence via the existing
multiconfig RenderDoc/readback gates. **QEMU-only scope** (virtio-gpu is a QEMU
device): per board-runnable rule this is explicitly scoped QEMU-first with the
board gap filed, not implied board-runnable
(`doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only.md`).

Corrected QEMU args (the published multiconfig args are the 2D legacy path and
cannot do Venus): `virtio-gpu-gl-pci,hostmem=256M,blob=true,venus=true,context_init=true`
with `-display sdl,gl=on` or `egl-headless,gl=on`; host needs virglrenderer built
`-Dvenus=true` and a working `vulkaninfo`. `-display none` disables the GL renderer
and reads as a false E1 failure.

Honesty rule: llvmpipe/lavapipe ⇒ `blocked:software-renderer`, never `pass`.
Park criterion: if the host QEMU cannot expose Venus, file the blocker — never
relabel modeled responses or substitute the host SFFI ICD as target proof.

Open review item: the Venus capset v0 ring-layout header fields were not verified
against a spec source (the plan parses layout from the capset blob rather than
hardcoding). Review before E2 starts.

## 3. Non-goals
- No new widget toolkit; reuse `widget_kind.spl` variants (Scroll, Menubar, …).
- TUI cell-grid path stays as-is (not bridged to DrawIrV3 in this campaign).
- `app.ui.render` string contract untouched.
- No virgl full GL — Venus/Vulkan path only.
