# GUI Layer Contract Fix Plan

Status: ✅ Done 2026-04-14 — D1 locked, D2 Phase 1+2+3 landed, D3 landed
Owner: sys_gui lane
Scope: resolve the top three divergences flagged in `doc/04_architecture/gui_layer_contract.md` section 5 between `CompositorBackend` implementations.
Source files audited: `src/os/compositor/{display_backend,fb_backend,browser_compositor_backend,compositor_engine2d,hosted_backend}.spl`, `src/lib/gc_async_mut/gpu/engine2d/{backend,engine,backend_cpu,...}.spl`.

> Note on the contract doc: at the time this plan was drafted, `doc/04_architecture/gui_layer_contract.md` does not yet exist on disk — only `cross_platform_wm.md` does. The first task in step 0 below is to materialize the contract doc (or its section 5) so this plan and the implementation can both link to a stable anchor. Until that happens, treat this file as the authoritative description of the three decisions.

---

## 0. Preamble — the three divergences

| # | Divergence | Symptom | Decision |
|---|---|---|---|
| D1 | `fill_rect` edge semantics | Three backends already agree (exclusive right/bottom) but the contract has never been written down, and one Engine2D-side comment in `compositor_engine2d.spl` claims it is inclusive. Future Engine2D backends could regress. | Lock the contract: `fill_rect(x, y, w, h, color)` paints columns `[x, x+w)` and rows `[y, y+h)`. **Exclusive** right/bottom. Add a doc-test that pins it. |
| D2 | Glass externs bypass the backend | `FbCompositorBackend`, `GpuCompositorBackend`, and `Engine2dCompositorBackend` all call `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v` (`src/os/compositor/display_backend.spl:43-46, 121-133, 222-234`; `src/os/compositor/compositor_engine2d.spl`). Those externs target the underlying *baremetal framebuffer*. When Engine2D wraps a non-baremetal backend (Vulkan, virtio-GPU, Metal, …) or when the active path is `GpuCompositorBackend` over virtio-GPU, glass effects paint into the wrong surface. `HostedCompositorBackend` already does the right thing by calling `rt_winit_buffer_blend_rect/_blur/_gradient_v` on the active winit buffer (`src/os/compositor/hosted_backend.spl:24-26, 136-155`). | Move `blend_rect` / `blur_region` / `gradient_v` / `read_pixel` out of the core `CompositorBackend` trait into a new optional `CompositorGlassCapable` subtrait. Each backend implements glass via its **own** pixel path (no shared `rt_gui_*` helper). Backends that cannot do glass (Engine2D today, until the underlying RenderBackend exposes blend) opt out and the compositor degrades to opaque fills. |
| D3 | `Engine2D.draw_text` drops bg color | The widget layer expects `draw_text(x, y, text, fg, bg)` (the `CompositorBackend` shape). `Engine2D.RenderBackend.draw_text` takes only `(x, y, text, color, font_size)` (`src/lib/gc_async_mut/gpu/engine2d/backend.spl:52`, all 11 concrete backends in `src/lib/gc_async_mut/gpu/engine2d/backend_*.spl`). `Engine2dCompositorBackend.draw_text` papers over this by painting an opaque rect first, which destroys antialiased glyph edges and forces a fixed 8×16 cell pitch. | Add a `draw_text_bg(x, y, text, fg, bg, font_size)` method on a new `Engine2DExtended` subtrait. Concrete `RenderBackend` impls implement it natively (per-pixel, font-aware). The Engine2D facade exposes `draw_text_bg`; `Engine2dCompositorBackend.draw_text` calls it instead of pre-painting a rect. |

---

## 1. D1 — Lock `fill_rect` exclusive semantics ✅ Done 2026-04-14

### 1.1 Files changed

| Path | Reason |
|---|---|
| `src/os/compositor/display_backend.spl` | Add a doc comment on the trait `fn fill_rect` line specifying `[x, x+w) × [y, y+h)`. No body changes. |
| `src/os/compositor/compositor_engine2d.spl` | Remove/replace the stale "inclusive vs exclusive" remark in the file header (search for "draw_rect_filled" comment block). |
| `src/lib/gc_async_mut/gpu/engine2d/backend.spl` | Add the same exclusive-edge note to the `me draw_rect_filled` doc string in the `RenderBackend` trait. |
| `doc/04_architecture/gui_layer_contract.md` (created in step 0) | Section "Rect coordinate semantics" cites this plan and the implementation. |

### 1.2 Change sketch

```spl
# trait CompositorBackend  (display_backend.spl:28)
# Paints columns [x, x+w) and rows [y, y+h). Right/bottom edge EXCLUSIVE.
# A zero-width or zero-height rect is a no-op. Negative w/h is undefined.
fn fill_rect(x: i32, y: i32, w: i32, h: i32, color: u32)
```

```spl
# trait RenderBackend  (engine2d/backend.spl:52)
# Right/bottom edge is EXCLUSIVE — see compositor gui_layer_contract.md.
me draw_rect_filled(x: i32, y: i32, w: i32, h: i32, color: u32)
```

No production code changes are required: `FramebufferDriver.fill_rect`
(`src/os/drivers/framebuffer/fb_driver.spl`, `while col < w` / `while row < h`),
`VirtioGpuDriver.fill_rect`, `CpuBackend.draw_rect_filled`
(`while row < y + h`, `_hline(..., w, ...)` walks `col < w`), and the hosted
`rt_winit_buffer_fill_rect` extern are already exclusive.

### 1.3 Callers to audit (no code edits expected)

The audit is to confirm no off-by-one on the boundary. Files that call `.fill_rect(` and need a quick eyeball pass:

| File | `.fill_rect(` call count | Notes |
|---|---:|---|
| `src/os/compositor/fb_backend.spl` | 30 | widest blast radius — the legacy renderer |
| `src/os/compositor/desktop_chrome.spl` | 14 | window decoration, taskbar |
| `src/os/compositor/app_content.spl` | 13 | per-app paint stubs |
| `src/os/compositor/decorations.spl` | 9 | title bars, close buttons |
| `src/os/compositor/cursor.spl` | 6 | mouse glyph rects |
| `src/os/compositor/{compositor,display_backend,rendering_primitives,text_render}.spl` | 2 each | trait impls + helpers |
| `src/os/compositor/{glass_effects_pure,glass_port,window_effects,wm_scene}.spl` | 1 each | edge cases |

The auditor should look for patterns like `fill_rect(x, y, w + 1, h + 1, …)` or `fill_rect(x, y, w - 1, h - 1, …)` that would have been compensating for an inclusive impl. Spot-check first: `cursor.spl:120` paints a 5×1 crosshair — already exclusive-correct.

### 1.4 Test plan

Add `test/unit/os/compositor/fill_rect_edge_semantics_spec.spl`:

- Construct a `BrowserCompositorBackend` (pure Simple, no FFI) at 16×16.
- Call `backend.fill_rect(2, 2, 4, 4, 0xFFFF0000)`.
- Assert `read_pixel(5, 5) == 0xFFFF0000` and `read_pixel(6, 5) == 0` and `read_pixel(5, 6) == 0`.
- Repeat with the `Engine2dCompositorBackend` wrapping a `CpuBackend` Engine2D so the Engine2D path is also pinned.
- Add a parallel assertion: `fill_rect(0, 0, 0, 5, …)` is a no-op (width 0 paints nothing).

### 1.5 Risk and rollback

Risk: **low**. No runtime behavior changes — this is a documentation lock plus a regression test.
Rollback: revert the doc-comment edits and delete the new spec file. The new spec catches any future regression.

---

## 2. D2 — Move glass effects out of `CompositorBackend` ✅ Done 2026-04-14

**Status: Phase 1 + Phase 2 + Phase 3 complete 2026-04-14.** Phase 1
trait split landed earlier (`src/os/compositor/display_backend.spl`),
opt-in by `FbCompositorBackend`, `HostedCompositorBackend`,
`BrowserCompositorBackend`. Phase 2 added native per-surface glass
impls for `Engine2dCompositorBackend` and `GpuCompositorBackend`
(commit `37` — Gpu native glass, D2 Phase 2 this session). Phase 3
removed the legacy `glass_effects.spl` shared helper and the
`rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v` /
`rt_gui_read_pixel` runtime symbols. Details in
`doc/03_plan/sys_gui/d2_glass_subtrait_migration.md`.

### 2.1 Files changed

| Path | Reason |
|---|---|
| `src/os/compositor/display_backend.spl` | Split `CompositorBackend`: remove `blend_rect`, `blur_region`, `gradient_v`, `read_pixel`. Add a new trait `CompositorGlassCapable` with those four methods. Delete the file-level `extern fn rt_gui_blend_fill / _box_blur / _gradient_v / _read_pixel` declarations and the `pack` / `clamp_u64` helpers (only glass code uses them). Re-implement `FbCompositorBackend`'s glass methods inline using `FramebufferDriver` operations (per-pixel blend, two-pass box blur on the back buffer). Re-implement `GpuCompositorBackend`'s glass methods using `VirtioGpuDriver` pixel access (or, until that exists, gate them behind a `// TODO(sys-gui-glass-gpu)` returning early — but the trait is not implemented for `GpuCompositorBackend` so callers detect the absence). |
| `src/os/compositor/compositor_engine2d.spl` | Remove the `rt_gui_*` extern block and the helper module aliases. `Engine2dCompositorBackend` does **not** implement `CompositorGlassCapable` until Engine2D's `RenderBackend` grows blend/blur. Add a `// see plan: doc/03_plan/sys_gui/gui_layer_contract_fix_plan.md` comment. |
| `src/os/compositor/hosted_backend.spl` | Move the `blend_rect` / `blur_region` / `gradient_v` / `read_pixel` methods out of the `CompositorBackend` impl block and into a separate `impl CompositorGlassCapable for HostedCompositorBackend:` block. No body changes — they already use `rt_winit_buffer_*`. |
| `src/os/compositor/browser_compositor_backend.spl` | Same restructuring: glass methods move to `impl CompositorGlassCapable`. Bodies (already pure-Simple per-pixel) unchanged. |
| `src/os/compositor/glass_effects.spl` | Currently the only non-backend caller of `rt_gui_*`. Replace direct extern calls with a generic helper `apply_glass(backend: CompositorGlassCapable, …)` that the caller obtains from the active compositor. If the compositor's backend does not implement the subtrait, fall back to opaque fill (the current Engine2D wrapper case). |
| `examples/simple_os/arch/{x86_64,arm64,riscv64}/boot/{baremetal_stubs,glass_render}.c` — the four `rt_gui_*` symbols are C stubs, not Rust externs (see [d2_unresolved_loose_ends.md](./d2_unresolved_loose_ends.md) §B). | Mark the four `rt_gui_*` symbols as deprecated; keep the bodies for one cycle so out-of-tree callers do not break, then delete after `FbCompositorBackend` is verified. |

### 2.2 Change sketch

Old (`display_backend.spl`):

```spl
trait CompositorBackend:
    ...
    fn blend_rect(x: i32, y: i32, w: i32, h: i32, color: u32, alpha: u8)
    fn blur_region(x: i32, y: i32, w: i32, h: i32, radius: u32)
    fn gradient_v(x: i32, y: i32, w: i32, h: i32, color1: u32, color2: u32)
    fn read_pixel(x: i32, y: i32) -> u32

extern fn rt_gui_blend_fill(xy: u64, wh: u64, color: u64, alpha: u64)
...
```

New:

```spl
trait CompositorBackend:
    ...   # core opaque ops only (clear, fill_rect, draw_text, present, ...)

trait CompositorGlassCapable:
    """Optional glass/composite extensions. Implementations MUST paint
    onto the same surface their CompositorBackend impl draws into —
    no shared global runtime helpers."""
    fn blend_rect(x: i32, y: i32, w: i32, h: i32, color: u32, alpha: u8)
    fn blur_region(x: i32, y: i32, w: i32, h: i32, radius: u32)
    fn gradient_v(x: i32, y: i32, w: i32, h: i32, c1: u32, c2: u32)
    fn read_pixel(x: i32, y: i32) -> u32
```

`FbCompositorBackend` glass impl pseudocode (no `rt_gui_*`):

```spl
impl CompositorGlassCapable for FbCompositorBackend:
    me blend_rect(x, y, w, h, color, alpha):
        # iterate pixels in [x, x+w) × [y, y+h),
        # read self.fb back buffer pixel, srcOver blend with `color`+alpha,
        # write through self.fb.put_pixel.
```

### 2.3 Callers to update

| File | What changes |
|---|---|
| `src/os/compositor/display_backend.spl` | Glass methods removed from `CompositorBackend` impl blocks for both Fb and Gpu backends; new `impl CompositorGlassCapable for FbCompositorBackend` block added. Gpu backend deliberately does **not** get a `CompositorGlassCapable` impl in this pass (TODO link). |
| `src/os/compositor/compositor_engine2d.spl` | Glass methods removed; no subtrait impl. |
| `src/os/compositor/hosted_backend.spl` | Glass methods relocated to a new impl block. |
| `src/os/compositor/browser_compositor_backend.spl` | Same. |
| `src/os/compositor/glass_effects.spl` | Only file outside the backends that imports `rt_gui_blend_fill` / `_box_blur` / `_gradient_v`. Switch to taking a `CompositorGlassCapable` parameter. |
| `src/os/compositor/{glass_effects_pure,glass_port,window_effects}.spl` | Audit — these reference glass via `glass_effects` or fill_rect. Likely no edits. |
| `src/os/desktop/shell.spl` | Currently uses `compositor.backend.blend_rect(...)` style calls (search). Replace with capability check: `if val gc = compositor.backend.as_glass_capable(): gc.blend_rect(...)`. |
| Runtime side (`src/runtime/...` rust shim that registers `rt_gui_*`) | After all Simple-side callers are gone, drop the registration. |

Total expected files touched: **8 Simple files + 1 runtime shim**.

`rt_gui_*` symbol caller count today (Simple side, confirmed via Grep): **3 files** — `display_backend.spl`, `compositor_engine2d.spl`, `glass_effects.spl`.

### 2.4 Test plan

1. `test/unit/os/compositor/glass_capability_dispatch_spec.spl`
   - Construct `BrowserCompositorBackend`. Assert it implements `CompositorGlassCapable`. Call `blend_rect` over a known-color background and verify per-pixel srcOver result.
2. `test/unit/os/compositor/engine2d_no_glass_spec.spl`
   - Construct `Engine2dCompositorBackend`. Assert that `as_glass_capable()` returns `None` (or whatever the Simple capability-probe pattern is). Compositor code that paints glass must fall back to `fill_rect`.
3. `test/system/sys_gui_002_compositor_cold_start_spec.spl` (existing) — extend to assert that booting the compositor with both Fb and Hosted backends produces the expected glass blend result (snapshot pixel at a known-blurred coordinate).
4. `test/unit/os/compositor/glass_effects_routing_spec.spl`
   - Verifies that calling `glass_effects.apply_glass(backend, …)` paints into the same backend's pixel buffer, not into a separate global framebuffer.

### 2.5 Risk and rollback

Risk: **medium**. The trait split is a wide refactor that touches every `CompositorBackend` impl and one downstream caller. The main hazard is forgetting one impl block and breaking the boot path on a backend that is not exercised in CI (virtio-GPU is the prime suspect — see open question Q3 below).
Rollback: revert `display_backend.spl`, `glass_effects.spl`, and the four backend files. The `rt_gui_*` runtime symbols were left in place during the deprecation cycle, so reverting Simple sources is sufficient. Spec `glass_capability_dispatch_spec.spl` will fail loudly if the trait split is missing.

---

## 3. D3 — `draw_text_bg` on Engine2D ✅ Done 2026-04-14

### 3.1 Files changed

| Path | Reason |
|---|---|
| `src/lib/gc_async_mut/gpu/engine2d/backend.spl` | Define new trait `Engine2DExtended` with `me draw_text_bg(x, y, text, fg, bg, font_size)`. Do **not** add it to the base `RenderBackend` trait — it stays optional so backends can opt in incrementally. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl` | Implement `Engine2DExtended` natively: render glyphs from the shared 5×7 font, write `bg` for unset pixels and `fg` for set pixels (or `bg` only where the glyph rectangle is, leaving outside untouched — see Q1). |
| `src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl` | Same — backed by the 8×16 VGA font already used by `fb_driver`. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` | Same. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_{vulkan,metal,cuda,rocm,opengl,intel,virtio_gpu}.spl` | Add a stub `draw_text_bg` that delegates to `draw_text` plus a pre-fill (current behavior) **only** until a native impl lands. Mark with `// TODO(sys-gui-007 draw_text_bg native)`. |
| `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | Add `me draw_text_bg(x, y, text, fg, bg, font_size)` to the `Engine2D` facade. If `self.backend.as_extended()` is some, delegate; otherwise pre-fill rect + `draw_text`. |
| `src/os/compositor/compositor_engine2d.spl` | Replace the current `draw_text` body that pre-fills an 8×16-per-char rect with a single call: `self.engine.draw_text_bg(x, y, text_str, fg, bg, 16)`. |

### 3.2 Change sketch

Old (`compositor_engine2d.spl`):

```spl
me draw_text(x, y, text_str, fg, bg):
    val tw = text_str.len().to_i32() * 8
    val th = 16
    self.engine.draw_rect_filled(x, y, tw, th, bg)
    self.engine.draw_text(x, y, text_str, fg, 16)
```

New:

```spl
me draw_text(x, y, text_str, fg, bg):
    self.engine.draw_text_bg(x, y, text_str, fg, bg, 16)
```

`backend.spl` addition:

```spl
trait Engine2DExtended:
    """Optional rendering extensions over RenderBackend."""
    me draw_text_bg(x: i32, y: i32, text_val: text, fg: u32, bg: u32, font_size: i32)
```

### 3.3 Callers to update (today's bg-via-workaround sites)

- `src/os/compositor/compositor_engine2d.spl` (the rect-pre-fill workaround documented above) — single call site.
- `src/os/desktop/shell.spl` — 15 `draw_text` calls; all currently go through the `CompositorBackend.draw_text(x, y, text, fg, bg)` shape, so they automatically pick up the fix once `Engine2dCompositorBackend.draw_text` is rewired. No source edits.
- `src/os/compositor/desktop_chrome.spl` (9 calls), `app_content.spl` (81 calls), `boot_splash.spl` (7), `decorations.spl` (2): same — all already pass `bg` through `CompositorBackend`. No edits.

So the only direct edit is `compositor_engine2d.spl`. The fix is invisible to ~120 widget call sites.

### 3.4 Test plan

1. `test/unit/lib/gc_async_mut/gpu/engine2d/cpu_draw_text_bg_spec.spl`
   - Construct an Engine2D with `CpuBackend` at 64×32. Call `engine.draw_text_bg(2, 2, "A", 0xFFFFFFFF, 0xFF000000, 16)`.
   - Assert: a pixel inside the glyph stem reads `0xFFFFFFFF`; a pixel inside the glyph body but outside the stroke reads `0xFF000000`; a pixel **outside** the glyph cell reads the original buffer value (zero) — confirming no leakage past the cell.
2. `test/unit/os/compositor/engine2d_compositor_draw_text_spec.spl`
   - Construct an `Engine2dCompositorBackend`. Render two adjacent glyphs at antialiased font size 16. Assert no opaque seam between them by checking a row pixel at the glyph junction is either `bg` or partially blended, never `bg` overlaid on top of an aa pixel.
3. `test/unit/lib/gc_async_mut/gpu/engine2d/extended_capability_spec.spl`
   - Assert `CpuBackend`, `BaremetalBackend`, `SoftwareBackend` report `Engine2DExtended` capability. Stub backends report it but document delegation.

### 3.5 Risk and rollback

Risk: **medium**. Eleven concrete `RenderBackend` impls touched. The CPU/baremetal/software backends are exercised in CI; the GPU-class backends (cuda/vulkan/metal/rocm/opengl/intel/virtio_gpu) are not necessarily, and a stub that compiles but does not print text correctly will only show up under headed run.
Rollback: revert `compositor_engine2d.spl` (restores pre-fill behavior), then revert the 11 backend additions and `engine.spl` and `backend.spl`. The `cpu_draw_text_bg_spec` would fail and pin the regression.

Status: implemented 2026-04-14 (Phase 1 fallback bodies; proper per-pixel impl in follow-up). Trait `Engine2DExtended` added to `backend.spl`; all 10 `backend_*.spl` files (`cpu`, `baremetal`, `software`, `vulkan`, `metal`, `cuda`, `rocm`, `opengl`, `intel`, `virtio_gpu`) got an `impl Engine2DExtended` block; Engine2D facade forwards `draw_text_bg`; `Engine2dCompositorBackend.draw_text` now calls `engine.draw_text_bg` (the pre-paint-rect workaround is gone). Baremetal is semi-native (the underlying `FramebufferDriver.draw_text` already takes fg/bg); the other nine ship the documented fallback (`draw_rect_filled(bg) + draw_text(fg)`) with a `TODO(sys-gui-007 draw_text_bg native)` marker. Test: `test/unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl`.

---

## 4. Order of operations

Recommended order:

1. **D1 first.** It is the cheapest (doc + one regression test, zero behavior change) and it pins the invariant the other two fixes will rely on. Both glass code (D2) and `draw_text_bg` (D3) need to know whether `(x, y, w, h)` rects are inclusive or exclusive when they decide which pixels to touch.
2. **D3 second.** It is self-contained inside Engine2D and the Engine2D wrapper. Landing it before D2 means D2's `glass_effects.spl` rewrite can use the corrected text path while it is restructuring. D3 also gives the team a smaller refactor to validate the testing pattern (subtrait + capability probe) that D2 reuses on a wider scale.
3. **D2 third.** Largest blast radius. Doing it last lets the implementer rely on (a) settled rect semantics and (b) a working capability-probe idiom from D3.

Dependency notes: D2 and D3 both introduce *optional* subtraits (`CompositorGlassCapable`, `Engine2DExtended`). They should reuse the same Simple-side pattern for capability detection — agree on the shape during D3 so D2 inherits it for free.

---

## 5. Open questions (decision needed)

| ID | Question | Why it matters |
|---|---|---|
| Q1 | When `draw_text_bg` paints the background, does it fill the **entire glyph cell rectangle** (font_size × char_count wide) or only the **non-glyph pixels**? The latter preserves previously-rendered content under text, the former matches the FbCompositorBackend behavior the contract is supposed to align to. | Decision needed. Recommend: full rect (matches Fb), because that is what every existing widget caller already assumes. |
| Q2 | Should `read_pixel` stay on `CompositorGlassCapable`, or move to its own `CompositorReadback` subtrait? Read-pixel is needed for diff/screenshot infra, not just glass. | Decision needed. Recommend: separate `CompositorReadback` subtrait so screenshot tooling does not require glass support. |
| Q3 | Does `GpuCompositorBackend` need `CompositorGlassCapable` in this pass, or can it be deferred? Today it calls `rt_gui_blend_fill` against the wrong surface; the safest short-term fix is to drop the impl entirely so callers get `None` back from the capability probe and degrade. | Decision needed. Recommend: defer (drop impl, leave TODO). The virtio-GPU driver does not yet expose a per-pixel readback API needed for proper srcOver blending. |
| Q4 | Do we need a `CompositorBackend.supports(cap)` predicate, or do we lean entirely on Simple's trait-cast pattern (`if val g = backend.as_glass_capable()`)? | Decision needed. Recommend: trait cast — fewer concepts, matches existing `Option<T>` idioms. |
| Q5 | Should the `rt_gui_*` runtime symbols be deleted in this PR or in a follow-up? Deleting in the same PR is cleaner; deferring lets out-of-tree code (browser examples, dev playgrounds) keep compiling. | Decision needed. Recommend: deprecate in this PR, delete one cycle later, after `bin/simple build` runs clean across `examples/`. |

---

## 6. Definition of done

- [ ] `doc/04_architecture/gui_layer_contract.md` exists and section 5 is updated to mark D1/D2/D3 resolved with cross-links to the commits that fixed them.
- [ ] `CompositorBackend` trait no longer declares `blend_rect` / `blur_region` / `gradient_v` / `read_pixel`.
- [ ] `CompositorGlassCapable` trait exists and is implemented by `FbCompositorBackend`, `HostedCompositorBackend`, and `BrowserCompositorBackend`. Not implemented by `GpuCompositorBackend` or `Engine2dCompositorBackend` (per Q3).
- [ ] No Simple file outside `src/runtime/` references `rt_gui_blend_fill`, `rt_gui_box_blur`, `rt_gui_gradient_v`, or `rt_gui_read_pixel`. (Verified by `grep -r 'rt_gui_' src/`.)
- [ ] `Engine2DExtended` trait exists; `CpuBackend`, `BaremetalBackend`, and `SoftwareBackend` implement it natively. The other eight backends compile with stubs that delegate to `draw_text` after pre-fill, with a TODO ticket linked.
- [ ] `Engine2dCompositorBackend.draw_text` is a one-liner that calls `engine.draw_text_bg`.
- [ ] All new specs land green:
  - `test/unit/os/compositor/fill_rect_edge_semantics_spec.spl`
  - `test/unit/os/compositor/glass_capability_dispatch_spec.spl`
  - `test/unit/os/compositor/engine2d_no_glass_spec.spl`
  - `test/unit/os/compositor/glass_effects_routing_spec.spl`
  - `test/unit/lib/gc_async_mut/gpu/engine2d/cpu_draw_text_bg_spec.spl`
  - `test/unit/os/compositor/engine2d_compositor_draw_text_spec.spl`
  - `test/unit/lib/gc_async_mut/gpu/engine2d/extended_capability_spec.spl`
- [ ] `test/system/sys_gui_002_compositor_cold_start_spec.spl` still passes on Fb and Hosted backends.
- [ ] `bin/simple build` and `bin/simple test` run clean.
- [ ] PR description links back to this plan and notes which open questions were resolved.
