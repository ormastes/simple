# D2 — Glass Subtrait Migration Plan

**Date:** 2026-04-14
**Parent:** `doc/03_plan/sys_gui/gui_layer_contract_fix_plan.md` §2
**Scope:** File-by-file migration for splitting glass methods (`blend_rect`, `blur_region`,
`gradient_v`, `read_pixel`) out of `CompositorBackend` into a new optional subtrait
`CompositorGlassCapable`.

---

## 1. Scope

The compositor trait today bundles glass operations (alpha blend / box blur / vertical
gradient / single-pixel read) with the core paint primitives. Three backends
(`FbCompositorBackend`, `GpuCompositorBackend`, `Engine2dCompositorBackend`) satisfy
those methods by calling shared `rt_gui_*` externs that write directly to the
baremetal framebuffer. On any non-baremetal path (virtio-GPU surface, Vulkan,
Metal, hosted, browser) this silently corrupts or misses the active surface.
Decision: move the four glass methods into an *optional* subtrait
`CompositorGlassCapable`, make each backend own its pixel path, and let backends
that cannot do glass opt out. Widgets that need glass feature-detect and fall
back to opaque fill.

---

## 2. Before / after trait shape

### Current (`src/os/compositor/display_backend.spl:19-37`)

```simple
trait CompositorBackend:
    fn width() -> i32
    fn height() -> i32
    fn clear(color: u32)
    fn fill_rect(x: i32, y: i32, w: i32, h: i32, color: u32)
    fn draw_text(x: i32, y: i32, text_str: text, fg: u32, bg: u32)
    fn draw_char_8x16(x: i32, y: i32, ch: u8, fg: u32, bg: u32)
    fn put_pixel(x: i32, y: i32, color: u32)
    fn present()
    fn present_rect(x: i32, y: i32, w: i32, h: i32)
    fn blend_rect(x: i32, y: i32, w: i32, h: i32, color: u32, alpha: u8)   # MOVE
    fn blur_region(x: i32, y: i32, w: i32, h: i32, radius: u32)            # MOVE
    fn gradient_v(x: i32, y: i32, w: i32, h: i32, color1: u32, color2: u32) # MOVE
    fn read_pixel(x: i32, y: i32) -> u32                                   # MOVE
```

### Target

```simple
trait CompositorBackend:
    fn width() -> i32
    fn height() -> i32
    fn clear(color: u32)
    fn fill_rect(x: i32, y: i32, w: i32, h: i32, color: u32)   # [x,x+w) x [y,y+h)
    fn draw_text(x: i32, y: i32, text_str: text, fg: u32, bg: u32)
    fn draw_char_8x16(x: i32, y: i32, ch: u8, fg: u32, bg: u32)
    fn put_pixel(x: i32, y: i32, color: u32)
    fn present()
    fn present_rect(x: i32, y: i32, w: i32, h: i32)
    fn as_glass_capable() -> CompositorGlassCapable?   # NEW — nil if not supported

trait CompositorGlassCapable:
    """Optional subtrait. Backends that can read + blend pixels on their own
    surface implement this. Callers must feature-detect."""
    fn blend_rect(x: i32, y: i32, w: i32, h: i32, color: u32, alpha: u8)
    fn blur_region(x: i32, y: i32, w: i32, h: i32, radius: u32)
    fn gradient_v(x: i32, y: i32, w: i32, h: i32, color1: u32, color2: u32)
    fn read_pixel(x: i32, y: i32) -> u32
```

`as_glass_capable()` default returns nil; backends that support glass override
to return `self`. No name collision: `blend_rect`/`blur_region`/`gradient_v`/
`read_pixel` remain unique across winit (`rt_winit_buffer_*`), engine2d
(which never owned these), and browser (pure-Simple buffer). Collision check
vs Engine2D `RenderBackend` trait (`src/lib/gc_async_mut/gpu/engine2d/backend.spl`)
is clean — none of the four names appear there.

---

## 3. Per-backend migration table

| Backend | File:line (origin/main) | Current glass impl | Target glass impl | Opt |
|---|---|---|---|---|
| `FbCompositorBackend` | `src/os/compositor/display_backend.spl:121-138` | `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v` / `rt_gui_read_pixel` on raw FB | Phase 1: keep wrapping `rt_gui_*` but move into `impl CompositorGlassCapable`. Phase 2: reimplement per-pixel against `FramebufferDriver` back buffer. | **Opt in** |
| `GpuCompositorBackend` | `src/os/compositor/display_backend.spl:222-240` | `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v` / `rt_gui_read_pixel` on raw FB (coincidentally works because virtio-GPU guest buffer IS the same FB) | Phase 1: **opt out** — no `CompositorGlassCapable` impl. Phase 2: implement via `VirtioGpuDriver` cmd stream. | **Opt out** (Ph1) |
| `Engine2dCompositorBackend` | `src/os/compositor/compositor_engine2d.spl:58-60, 144-160` | `rt_gui_*` externs painting the underlying baremetal FB (wrong when Engine2D wraps Vulkan/Metal) | **Opt out** — delete extern block and impls. Stays opt-out until `Engine2D.RenderBackend` grows blend primitives. | **Opt out** |
| `HostedCompositorBackend` | `src/os/compositor/hosted_backend.spl:24-26, 136-158` | `rt_winit_buffer_blend_rect` / `_blur` / `_gradient_v` / `_read_pixel` on active winit buffer | Move the four methods from `impl CompositorBackend` into new `impl CompositorGlassCapable`. Bodies unchanged. | **Opt in** |
| `BrowserCompositorBackend` | `src/os/compositor/browser_compositor_backend.spl` ~`190-250` (contains all four methods; native per-pixel against `[u32]` buffer) | Pure-Simple per-pixel on `[u32]` pixel buffer | Move the four methods into `impl CompositorGlassCapable`. Bodies unchanged. | **Opt in** |

No other `CompositorBackend` implementations exist on origin/main (confirmed:
grep for `CompositorBackend for` returns only the five backends above).

---

## 4. Per-caller migration table

Callers fall into three buckets. `.blend_rect` / `.blur_region` / `.gradient_v`
call-site counts in `src/os/compositor/`: `window_effects.spl` 112,
`desktop_chrome.spl` 90, `render_extras.spl` 44, `compositor.spl` 34,
`app_content.spl` 32, `boot_splash.spl` 19, `rendering_primitives.spl` 18,
`glass_effects_pure.spl` 9, `cursor.spl` 8, `glass_port.spl` 5,
`text_render.spl` 4, `wm_scene.spl` 3. `src/os/desktop/shell.spl`: zero
direct `.blend_rect`/`.blur_region`/`.gradient_v` calls (all glass goes via
`glass_effects*`).

| Caller file:line | Current shape | Target shape |
|---|---|---|
| `src/os/compositor/window_effects.spl:*` (all `backend.blend_rect/blur_region` calls; `backend: CompositorBackend` parameter) | `fn draw_frosted_surface(backend: CompositorBackend, …)` | Rename parameter type: `backend: CompositorGlassCapable`. Caller (`shell.spl`, `desktop_chrome.spl`) performs `as_glass_capable()` check before invoking. If nil -> skip frosted pass, fall back to `opaque_fill_fallback(backend, …)` (new helper). |
| `src/os/compositor/glass_effects_pure.spl:*` (9 call sites; signature already `backend: CompositorBackend`) | Same | Flip parameter type to `CompositorGlassCapable`. No body change. |
| `src/os/compositor/glass_port.spl:*` (port registry with function refs) | Module-level fn refs typed `CompositorBackend -> ...` | Retype to `CompositorGlassCapable -> ...`. Registration site adjusts. |
| `src/os/compositor/desktop_chrome.spl:*` (90 call sites) | `backend.blend_rect(...)` on `CompositorBackend` | Lift to the enclosing fn that already owns the backend; add one `as_glass_capable()` guard near the top of each drawing fn and branch. Inner loops unchanged. |
| `src/os/compositor/app_content.spl:*` (32), `boot_splash.spl:*` (19), `render_extras.spl:*` (44), `rendering_primitives.spl:*` (18), `cursor.spl:*` (8), `text_render.spl:*` (4), `wm_scene.spl:*` (3), `compositor.spl:*` (34) | Same pattern — `backend.blend_rect(...)` | Same — `as_glass_capable()` guard at the top; opaque-fill fallback on nil. |
| `src/os/compositor/glass_effects.spl:*` | Direct `rt_gui_*` externs | Delete file, or gut to re-export `glass_effects_pure` as `glass_effects`. See §7. |
| `src/lib/gc_async_mut/gpu/engine2d/*` callers of `.read_pixels()` | Unrelated — this is `read_pixels` (plural), not the `read_pixel(x,y)` method. No change. | — |

All call-site surface areas are inside `src/os/compositor/`. No `src/app/`
hits. Tests: two specs reference glass rendering
(`test/integration/rendering/glass_render_e2e_spec.spl`,
`test/system/gui/glass_pixel_compare_spec.spl`); both go through the
`glass_effects_pure` API, so the parameter-type flip is transparent.

---

## 5. Virtio-GPU risk analysis (the #1 risk)

Today `GpuCompositorBackend.blend_rect` at `display_backend.spl:224` calls
`rt_gui_blend_fill`. That extern writes bytes to whatever the baremetal GUI
runtime considers "the active framebuffer." Under virtio-GPU we present by
DMA'ing a shared memory region to the host; the guest's `VirtioGpuDriver`
exposes that region and the baremetal glass extern *happens to scribble into
exactly that memory*, so blur / blend currently render correctly on QEMU
virtio-GPU even though the code path semantically targets the wrong abstraction.
After the subtrait split, `GpuCompositorBackend` no longer implements
`CompositorGlassCapable`, so `as_glass_capable()` returns nil and every widget
skips the glass pass. **Visible regression:** frosted title bars, shadows, and
app-chrome gradients disappear on the virtio-GPU boot path and are replaced by
opaque fill. This is the single biggest risk of Phase 1. Mitigation: keep the
opt-out (safer than leaving the broken extern in place — it's broken on
Vulkan/Metal today), document the regression in the sys-gui-006 baseline
README, and schedule Phase 2 (native virtio-GPU blend/blur via cmd stream) as
the immediate follow-up. Rationale for opt-out over opt-in: the current
behavior is accidental and undefined on any backend other than the exact
baremetal FB layout, so "loses glass on virtio-GPU" is a principled
degradation; "ships latent data corruption on Metal" is not.

---

## 6. Phased rollout

**Phase 1 — trait split (1 PR, mechanical).**
- Edit `src/os/compositor/display_backend.spl`: split trait, keep `rt_gui_*` externs ONLY on `FbCompositorBackend`'s `CompositorGlassCapable` impl (short-term), delete them from the `GpuCompositorBackend` impl block.
- Edit `src/os/compositor/compositor_engine2d.spl`: delete `extern fn rt_gui_*` block (lines 58-60) and the glass method impls (lines 144-160). No `CompositorGlassCapable` impl.
- Edit `src/os/compositor/hosted_backend.spl`: move four methods into new impl block.
- Edit `src/os/compositor/browser_compositor_backend.spl`: move four methods into new impl block.
- Edit `src/os/compositor/glass_effects_pure.spl`, `glass_port.spl`, `window_effects.spl`: retype `backend` params to `CompositorGlassCapable`.
- Insert `as_glass_capable()` guards in `app_content.spl`, `desktop_chrome.spl`, `boot_splash.spl`, `render_extras.spl`, `rendering_primitives.spl`, `cursor.spl`, `text_render.spl`, `wm_scene.spl`, `compositor.spl` (one guard per fn that draws glass).
- Gut `glass_effects.spl` to delegate to `glass_effects_pure`.

**Phase 2 — native per-backend glass.**
- `src/os/compositor/display_backend.spl`: rewrite `FbCompositorBackend`'s `CompositorGlassCapable` impl to use `FramebufferDriver` back-buffer per-pixel blend + two-pass box blur. Drop `rt_gui_blend_fill` call site.
- Add `impl CompositorGlassCapable for GpuCompositorBackend` using `VirtioGpuDriver` cmd-stream blit + host-side blend where available, or guest-side blend on the DMA buffer before the flush command.
- Optional: add glass impl on `Engine2dCompositorBackend` once `Engine2D.RenderBackend` grows a blend primitive.

**Phase 3 — cleanup.**
- Delete the `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v` / `rt_gui_read_pixel` extern declarations in Simple and the Rust shim registration (location TBD during impl — `git grep` on origin/main confined these externs to `display_backend.spl` + `compositor_engine2d.spl`; the Rust-side definition file should be located at impl time and marked deprecated in Phase 1, deleted in Phase 3).
- Delete `glass_effects.spl` if §7 resolution chooses delete.

---

## 7. `glass_effects.spl` / `glass_effects_pure.spl` disposition

`glass_effects.spl` is a thin wrapper over `rt_gui_*` externs (plus
`glass_numeric_tokens` config). Its entire surface is superseded by
`glass_effects_pure.spl`, which already exposes identical helpers
(`glass_fill_pure`, `glass_blur_pure`, `glass_gradient_v_pure`,
`glass_shadow_pure`, `draw_glass_rect_pure`, `draw_glass_border_pure`,
`glass_begin_frame_pure`, `glass_present_pure`) routed through the
`CompositorBackend` (soon `CompositorGlassCapable`) parameter. `grep_glass_effects_imports`
shows zero Simple-side `use`/`import` sites for `glass_effects.spl` outside
the compositor directory — it has no external consumers. **Disposition: gut
in Phase 1 (replace bodies with thin forwards to `glass_effects_pure`), delete
in Phase 3 after one cycle.** `glass_effects_pure.spl` survives, gets its
parameter type flipped to `CompositorGlassCapable`, and becomes the single
glass entry point. `glass_port.spl` (port registry) survives as-is — it just
becomes a port over the subtrait.

---

## 8. Acceptance (Phase 1 done when)

- `CompositorBackend` trait no longer declares `blend_rect` / `blur_region` / `gradient_v` / `read_pixel`; `CompositorGlassCapable` declares them; `as_glass_capable()` exists on the core trait.
- `FbCompositorBackend`, `HostedCompositorBackend`, `BrowserCompositorBackend` each have an `impl CompositorGlassCapable` block; `GpuCompositorBackend` and `Engine2dCompositorBackend` do **not**.
- `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v` / `rt_gui_read_pixel` externs remain declared in **exactly one** Simple file (`display_backend.spl`, used only by Fb). `compositor_engine2d.spl` no longer references them.
- `bin/simple build` passes; `bin/simple test` passes the two glass specs in `test/integration/rendering/` and `test/system/gui/`.
- SimpleOS boots on the hosted (winit) backend with frosted title bars intact and boots on virtio-GPU with opaque (degraded) title bars plus a logged warning `glass: backend opted out of CompositorGlassCapable` on first skip.

---

## 9. Rollback plan

Phase 1 is trait-shape only; no pixel logic changes for `FbCompositorBackend`
or `HostedCompositorBackend`. If the virtio-GPU degradation is unacceptable
before Phase 2 lands, revert by (a) re-adding the four methods to
`CompositorBackend` as default-implementations that call
`as_glass_capable()` when present and no-op otherwise, and (b) adding a
temporary `impl CompositorGlassCapable for GpuCompositorBackend` that
delegates to the `rt_gui_*` externs — restoring today's accidental-but-working
virtio-GPU path while keeping the subtrait API. This rollback is a single-file
edit to `display_backend.spl` and reverts the visible regression in under one
commit; the new subtrait API and the hosted/browser opt-ins stay.

---

## 10. File existence audit

Verified on `origin/main`:
- `src/os/compositor/display_backend.spl` — exists, trait at L19-37.
- `src/os/compositor/hosted_backend.spl` — exists, winit glass at L136-158.
- `src/os/compositor/compositor_engine2d.spl` — exists, externs L58-60, glass impl L144-160.
- `src/os/compositor/browser_compositor_backend.spl` — exists, glass methods present.
- `src/os/compositor/glass_effects.spl`, `glass_effects_pure.spl`, `glass_port.spl`, `window_effects.spl` — exist.
- `src/os/desktop/shell.spl` — exists, but has **zero** direct `.blend_rect`/`.blur_region`/`.gradient_v`/`.read_pixel` calls (all glass routes through `glass_effects*`). Earlier plan note suggesting `compositor.backend.blend_rect(...)` edits to `shell.spl` is out-of-date; no `shell.spl` edit needed.
- `src/runtime/gui/glass.rs` does not exist on `origin/main`. `rt_gui_*` are **C stubs**, not Rust externs — located at `examples/simple_os/arch/{x86_64,arm64,riscv64}/boot/{baremetal_stubs,glass_render}.c`. See [d2_unresolved_loose_ends.md](./d2_unresolved_loose_ends.md) §B.
