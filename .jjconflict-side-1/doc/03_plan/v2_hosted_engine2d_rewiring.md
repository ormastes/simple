# V2 Hosted Backend → Engine2D Rewiring

**Date:** 2026-04-14
**Scope:** V2 "Pure Simple on host OS" drawing path. Rewires
`src/os/compositor/hosted_backend.spl` to delegate through `Engine2D` +
`RenderBackend`, plus a backend-selection mechanism.
**Driver:** `doc/01_research/domain/v2_gpu_defaults_2026-04-14.md` (T3
research). This plan addresses **gap 1** (Engine2D bypass) and **gap 3**
(no selection mechanism). Gap 2 (Cocoa / Win32 hosted shims) is tracked
elsewhere and explicitly deferred.

---

## 1. Problem statement

`HostedCompositorBackend` does not construct an `Engine2D` and bypasses
every `backend_*` file. All draw operations are direct
`rt_winit_buffer_*` FFI calls into a CPU-side pixel buffer at
`src/os/compositor/hosted_backend.spl:60-162` (the trait `impl`) and the
constructor at `src/os/compositor/hosted_backend.spl:170-192`. The raw
FFI declarations live at `src/os/compositor/hosted_backend.spl:19-27`,
and the `clear / fill_rect / draw_char_8x16 / put_pixel / present /
present_rect / blend_rect / blur_region / gradient_v / read_pixel`
implementations between **lines 66 and 162** are all single-line winit
FFI dispatches. There are **23** `rt_winit_buffer_*` token occurrences
inside `hosted_backend.spl` itself.

This violates the layering described in
`doc/04_architecture/cross_platform_wm.md` and
`doc/04_architecture/gui_layer_contract.md`: the V2 hosted path was
supposed to plug into the same `Engine2D → RenderBackend` stack that
SimpleOS V1 uses through `compositor_engine2d.spl`. Instead it is a
parallel CPU-only drawing tree that no `backend_metal`, `backend_vulkan`,
`backend_opengl`, or `backend_cpu` ever sees.

---

## 2. Target architecture

```
                    DesktopShell
                         │
                    Compositor (Compositor.with_backends)
                         │
                  CompositorBackend (trait)
                         │
            ┌────────────┴────────────┐
            │ HostedCompositorBackend │  ← rewired
            └────────────┬────────────┘
                         │ delegates each method
                         ▼
                      Engine2D                       (engine.spl)
                         │
                  RenderBackend (trait)              (backend.spl)
        ┌──────────┬─────┴─────┬──────────┬──────────┐
        │ Metal    │ Vulkan    │ OpenGL   │ Cpu /    │
        │ (macOS)  │ (Lin/BSD/ │ (legacy) │ Software │
        │          │  Win)     │          │ (floor)  │
        └────┬─────┴─────┬─────┴────┬─────┴────┬─────┘
             │           │          │          │
             ▼           ▼          ▼          ▼
        Metal dev   Vulkan dev  GL FBO     [u32] buffer
             │           │          │          │
             └───────────┴────┬─────┴──────────┘
                              ▼
                  rt_winit_buffer_present(win, buf)
                  (only the final blit uses winit FFI)
```

**Key invariant:** after Phase B, the only `rt_winit_buffer_*` symbol
that `hosted_backend.spl` references is `rt_winit_buffer_present` (and
its create/free counterparts), used purely as a "swap chain" — every
pixel-level call goes through `Engine2D`.

---

## 3. Constructor refactor

### Current
`src/os/compositor/hosted_backend.spl:170`
```
static fn new(window_id: i64, buffer_id: i64, w: i32, h: i32)
    -> HostedCompositorBackend
```
Caller passes a pre-allocated winit buffer id; the backend stores it in
module-level vars at `hosted_backend.spl:30-33`.

### Proposed
```
static fn with_engine(window_id: i64, engine: Engine2D, w: i32, h: i32)
    -> HostedCompositorBackend
```
`HostedCompositorBackend` gains an `engine: Engine2D` field. The winit
buffer is owned **inside** the `engine` (specifically, inside the active
`RenderBackend` — `CpuBackend`'s `[u32]` array, or the GPU backend's
device-side framebuffer). The hosted backend keeps `window_id` only so
that `present()` can blit the engine's `read_pixels()` to the OS window
via a single `rt_winit_buffer_present` call.

### `hosted_entry.spl` diff sketch
`src/os/hosted/hosted_entry.spl:55-72` (before):
```
val win = rt_winit_window_new(el, w, h, "SimpleOS")
val buf = rt_winit_buffer_create(WINDOW_WIDTH, WINDOW_HEIGHT, BG_COLOR)
var backend = HostedCompositorBackend.create(win, w32, h32, bg_u32)
val input  = HostedInputBackend.create(el)
val comp   = Compositor.with_backends(backend, input, w32, h32)
```
After:
```
val win    = rt_winit_window_new(el, w, h, "SimpleOS")
val engine = Engine2D.create_for_host(w32, h32)   # picks per-OS default
var backend = HostedCompositorBackend.with_engine(win, engine, w32, h32)
val input   = HostedInputBackend.create(el)
val comp    = Compositor.with_backends(backend, input, w32, h32)
```
Notes:
- `rt_winit_buffer_create` disappears from `hosted_entry.spl`. The
  hosted backend creates its own winit blit buffer lazily inside
  `present()` (or once at construction), since the engine framebuffer
  is owned by the `RenderBackend`.
- `Engine2D.create_for_host` is a new selector wrapper (see §5).

---

## 4. Method-by-method mapping

Trait surface reference: `src/os/compositor/display_backend.spl:1-30`
(grouped here for convenience).

| `CompositorBackend` method | New `HostedCompositorBackend` body | Engine2D / RenderBackend target |
|---|---|---|
| `width() -> i32` | return `self.w` | none (cached) |
| `height() -> i32` | return `self.h` | none (cached) |
| `clear(color)` | `self.engine.clear(color)` | `Engine2D.clear` → `RenderBackend.clear` |
| `fill_rect(x,y,w,h,color)` | `self.engine.draw_rect_filled(x,y,w,h,color)` | `RenderBackend.draw_rect_filled` |
| `draw_text(x,y,s,fg,bg)` | `self.engine.draw_text(x, y, s, fg, font_size_default)` | `RenderBackend.draw_text` (font_size baked from 8x16 → 14 pt; bg painted via prior `draw_rect_filled` of the text bbox) — **bridge** |
| `draw_char_8x16(x,y,ch,fg,bg)` | bridge: `engine.draw_rect_filled(x,y,8,16,bg)` then iterate glyph bits and `engine.draw_rect_filled(x+col, y+row, 1, 1, fg)` | **bridge** — same approach as `Engine2dCompositorBackend` (`compositor_engine2d.spl`) |
| `put_pixel(x,y,color)` | `self.engine.draw_rect_filled(x,y,1,1,color)` | **bridge** (matches existing wrapper) |
| `present()` | `self.engine.present()` then `rt_winit_buffer_present(window_id, blit_buf)` after copying `engine.read_pixels()` into `blit_buf` | `Engine2D.present` + winit blit |
| `present_rect(x,y,w,h)` | same as `present()` for V2 (full-frame swap is acceptable) | same |
| `blend_rect(x,y,w,h,color,alpha)` | bridge — pre-multiply alpha into color and call `self.engine.draw_rect_filled(...)`. **Open question:** add `RenderBackend.blend_rect` later. | **bridge** |
| `blur_region(x,y,w,h,radius)` | bridge — no-op in CPU/Software paths; on Vulkan/Metal, call into a shader once available. **Open question.** | **bridge** |
| `gradient_v(x,y,w,h,c1,c2)` | `self.engine.draw_gradient_rect(x,y,w,h,c1,c2)` | `RenderBackend.draw_gradient_rect` |
| `read_pixel(x,y) -> u32` | bridge — `engine.read_pixels()` into a cached `[u32]`, index `y*w+x`. Cache invalidated each `present()`. | **bridge** |

**Tally:** 13 `CompositorBackend` methods total. **5** map cleanly
(`width`, `height`, `clear`, `fill_rect`, `gradient_v`) and a 6th
(`present`) is clean modulo the swap-chain blit. **7** need bridges —
identical bridge shapes already exist in `compositor_engine2d.spl`, so
the implementation cost is largely a copy-and-tweak.

---

## 5. Backend-selection mechanism

**Today:** `Engine2D.create()` calls `detect_best_backend` at
`src/lib/gc_async_mut/gpu/engine2d/engine.spl:160-201`, probing
`cuda → rocm → metal → vulkan → opengl → intel → software` blindly.
There is no env var, no CLI flag, and `MetalBackend.create().init(1,1)`
runs unconditionally (see T3 doc gap macOS-3 — segfault risk on
non-macOS hosts).

**Proposed.** Three concentric overrides, all read in `engine.spl`:

1. **Env var:** `SIMPLE_ENGINE2D_BACKEND={metal|vulkan|opengl|cpu|software|auto}`
   Read once in a new `Engine2D.create_for_host(w, h)` constructor. If
   set and not `"auto"`, call `create_with_backend(w, h, value)` directly
   and skip detection.
2. **CLI flag:** `--engine2d-backend=<name>` on `bin/simple run`. The CLI
   sets `SIMPLE_ENGINE2D_BACKEND` in the child process so the same code
   path handles it.
3. **Per-OS auto-default table** (replaces fixed priority in
   `detect_best_backend` at `engine.spl:160-201`):
   - `macos` → `[metal, opengl, software, cpu]`
   - `linux`, `freebsd` → `[vulkan, opengl, software, cpu]`
   - `windows` → `[vulkan, opengl, software, cpu]`
   - any other → `[software, cpu]`

Tied to the T3 table verbatim (do not duplicate the rationale here).

**Probe-gating fix.** Each backend exposes a side-effect-free
`is_available()` that the selector calls **before** `create().init(1,1)`.
For `MetalBackend`, this is `rt_metal_is_available()` already declared
at `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:23-27`. For
`VulkanBackend`, `rt_vulkan_is_available()` at `backend_vulkan.spl:32`.
For `OpenGLBackend`, `opengl_available()` at `backend_opengl.spl:90`.
`CpuBackend` is unconditional. `cuda`, `rocm`, `intel` are dropped from
the V2 default chain (still reachable via explicit
`create_with_backend`).

**File to edit:** `src/lib/gc_async_mut/gpu/engine2d/engine.spl`,
`detect_best_backend` (`engine.spl:160-201`), plus a new
`create_for_host` static fn alongside `create` and `create_with_backend`.

---

## 6. Caller migration

`grep rt_winit_buffer_ src/**/*.spl test/**/*.spl examples/**/*.spl`
returns **70** total occurrences in `.spl` files: **23** inside
`hosted_backend.spl` (rewired in this plan) and **47** outside it. The
non-`hosted_backend.spl` occurrences cluster into:

| File | Lines | Action in this plan |
|---|---|---|
| `src/os/hosted/hosted_entry.spl` | 17, 59 | Update constructor call (§3 sketch); drop the `rt_winit_buffer_create` extern import. |
| `src/os/compositor/dual_backend.spl` | 18, 19, 83, 93 | Reads pixels from `native_backend.buffer_id` for diffing. After Phase B, change to `native_backend.engine.read_pixels()`. Save-bmp helper still allowed. |
| `examples/simple_os/hosted/hosted_wm.spl` | 17, 42 | Switch to `with_engine` + `Engine2D.create_for_host`. |
| `examples/simple_os/hosted/hosted_wm_compare.spl` | 26-28, 62, 91, 123 | Same. Keep `rt_winit_buffer_create` only if the example explicitly compares Engine2D output against a hand-painted reference buffer. |
| `examples/simple_os/hosted/hosted_wm_verify.spl` | 23-26, 113, 141, 146, 163 | Same. The `save_bmp` call stays — it's a verification helper, not a draw call. |
| `test/system/os/hosted_wm_system_test.spl` | 32-36 + body | **Out of scope for Phase B.** This system test predates the rewire and exercises the raw FFI directly as a smoke test. Leave untouched until Phase C; gate on `SIMPLE_ENGINE2D_BACKEND=cpu` if needed. |
| `test/system/os/simpleos_capabilities_test.spl` | 31-35 + body | Same — leave on raw FFI, it tests the FFI itself. |

`HostedCompositorBackend.create` / `.new` callers (5 `.spl` sites) all
get migrated in Phase B:
- `src/os/hosted/hosted_entry.spl:69`
- `examples/simple_os/hosted/hosted_wm.spl:42`
- `examples/simple_os/hosted/hosted_wm_compare.spl:73`
- `examples/simple_os/hosted/hosted_wm_verify.spl:117`
- `src/os/compositor/dual_backend.spl:32, 41` (field type — keep, `HostedCompositorBackend` type does not change)

---

## 7. Test plan

### Unit
**New file:** `test/unit/os/compositor/hosted_backend_engine2d_spec.spl`

- `it("constructs a HostedCompositorBackend with a CPU Engine2D")` —
  build `Engine2D.create_with_backend(64, 64, "cpu")`, then
  `HostedCompositorBackend.with_engine(0, engine, 64, 64)`. Assert
  `backend.width() == 64` and `backend.height() == 64`.
- `it("delegates clear to engine.clear")` — call `clear(0xFF112233)`,
  then `read_pixel(0,0) == 0xFF112233`.
- `it("delegates fill_rect / gradient_v / draw_text without crashing")`
  — sanity exercise of every clean-mapping method.
- `it("bridges put_pixel and draw_char_8x16")` — assert the bridge
  produces non-background pixels in the expected glyph cells.
- `it("does NOT call rt_winit_buffer_fill_rect during draw")` —
  mockable via a counter extern shim; or assert via inspection that
  the only winit symbol referenced is `rt_winit_buffer_present` plus
  create/free.

The unit spec MUST run with `window_id == 0` (no real winit window) by
short-circuiting `present()` when `window_id == 0`, so the spec works
under the interpreter without a display server.

### System / integration
**Extend:** `examples/simple_os/hosted/hosted_wm_compare.spl` (or move
its harness into `test/system/os/hosted_engine2d_compare_spec.spl`).
Render the same scene through (a) the legacy raw-FFI path and (b) the
new Engine2D-backed `HostedCompositorBackend` configured with
`SIMPLE_ENGINE2D_BACKEND=cpu`. Save both buffers via
`rt_winit_buffer_save_bmp` and assert byte-identical (or
PSNR > 40 dB if minor rounding shows up in the bridges). This is the
acceptance gate for Phase B.

### Per-OS default
**New file:** `test/unit/lib/engine2d/detect_best_backend_spec.spl`.
Use a mock `is_available_fn(name) -> bool` injected into a refactored
`detect_best_backend(host_os, probe)` to enumerate the table-driven
truth without touching a real GPU:

| `host_os` | available probes | expected default |
|---|---|---|
| `macos` | `metal=true` | `metal` |
| `macos` | `metal=false, opengl=true` | `opengl` |
| `linux` | `vulkan=true` | `vulkan` |
| `linux` | `vulkan=false, opengl=false` | `software` |
| `windows` | `vulkan=true` | `vulkan` |
| `freebsd` | `vulkan=true` | `vulkan` |
| `unknown` | (all false) | `software` |

This spec also closes the macOS-3 segfault bug from the T3 doc — the
`is_available` gate is asserted by the `metal=false` row.

---

## 8. Phased rollout

### Phase A — additive Engine2D constructor (CPU only)
- Add `with_engine(window_id, engine, w, h)` alongside the existing
  `new` / `create` constructors in `hosted_backend.spl`. Do NOT delete
  the old constructors yet.
- Add the `engine: Engine2D` field. The `impl CompositorBackend` block
  branches on whether `engine` is present and uses §4's mapping when
  it is, else falls back to the legacy raw-FFI body.
- Land `Engine2D.create_for_host` and the env-var read in `engine.spl`,
  but only the `cpu` branch is wired (no Metal/Vulkan probes).
- **Acceptance:** `test/unit/os/compositor/hosted_backend_engine2d_spec.spl`
  passes under `bin/simple test`, with `SIMPLE_ENGINE2D_BACKEND=cpu`,
  on the existing Linux CI runner; **and** the legacy hosted_entry path
  (still using `create`) renders pixel-identically to its current
  baseline. No caller changes outside the test file.

### Phase B — migrate callers, delete raw constructor
- Update the 5 `HostedCompositorBackend.create` callers listed in §6.
- Delete `HostedCompositorBackend.new` and `.create`. Delete the
  module-level `_hosted_*` vars at `hosted_backend.spl:30-33`.
- Delete the raw-FFI bodies in the trait impl. The only winit FFI
  decls remaining in `hosted_backend.spl` are `rt_winit_buffer_create`,
  `rt_winit_buffer_present`, `rt_winit_buffer_free`. (Optionally
  consolidate the create/free into a tiny `WinitBlitter` helper.)
- The `dual_backend.spl` reader switches to
  `native_backend.engine.read_pixels()`.
- **Acceptance:** the system compare spec from §7 passes byte-identical
  on Linux with `SIMPLE_ENGINE2D_BACKEND=cpu`.

### Phase C — wire Metal on macOS, Vulkan on Linux
- Enable the `metal` and `vulkan` branches in
  `Engine2D.create_for_host`. Drop `cuda` / `rocm` / `intel` from the
  V2 default chain.
- Add per-OS CI matrix entry: macOS runner with `=metal`, Linux runner
  with `=vulkan`, Linux runner with `=cpu`.
- Windows / FreeBSD remain on `cpu` until gap 2 (Cocoa / Win32 hosted
  shims) lands — they have no hosted surface at all today, so the
  selection mechanism is moot for them.
- **Acceptance:** the system compare spec passes on macOS with
  `=metal` and on Linux with `=vulkan`, both within the PSNR threshold.

---

## 9. Open questions

1. **`blend_rect` and `blur_region` on GPU backends.** The
   `RenderBackend` trait has no `blend_rect` / `blur_region`. Should we
   (a) extend the trait, (b) keep the bridge that pre-multiplies alpha
   and uses `draw_rect_filled` for blend and a no-op for blur, or
   (c) keep the existing `rt_gui_*` glass extern path used by
   `compositor_engine2d.spl` for the baremetal case? Option (c) does
   not work hosted because there's no shared framebuffer.
2. **`read_pixel` cache invalidation.** Calling `engine.read_pixels()`
   on every `read_pixel(x,y)` is O(w·h) per query. A read-pixel cache
   keyed on present-count is straightforward but adds state. Is this
   path hot enough to care? (The compositor uses it for hit-testing
   transparent regions.)
3. **Font size mapping for `draw_text`.** The hosted backend's 8x16
   bitmap font does not correspond to any specific point size in
   `RenderBackend.draw_text(font_size: i32)`. Pick a constant (14?) or
   add a `RenderBackend.draw_bitmap_text` overload.
4. **Who creates the winit blit buffer in Phase B?** Either
   `HostedCompositorBackend.with_engine` lazy-creates one on first
   `present()`, or the caller passes one in. The sketch in §3 chose
   the former; needs a sanity check against the winit FFI lifecycle.
5. **System tests on raw FFI.** `test/system/os/hosted_wm_system_test.spl`
   and `test/system/os/simpleos_capabilities_test.spl` keep using raw
   FFI. They are the only V2 smoke tests that exercise the winit
   runtime directly. Leave them as-is, or rewrite on top of the new
   constructor in a follow-up?
