<!-- opus-design 2026-07-06 -->
# Draw-IR Multi-Backend Rendering — Design

**Companion research:** `doc/01_research/ui/rendering/draw_ir_multibackend_research.md`.
**Principle:** one Draw-IR, one dispatch point, one interface, **one software reference oracle**;
GPU/SIMD backends **override only what they accelerate** and fall through to the shared reference
for everything else, with **capability-honest** naming and readback. No inheritance — composition
and delegation only (repo rule). No parallel trait — we rationalize the existing `RenderBackend`.

---

## 1. Canonical layering (target)

```
UI / WM / web layout / browser_engine
        │  emit
        ▼
Draw-IR:  RenderScene / SceneCommand   (extended — §6)          common/render_scene/scene.spl
        │  the ONLY serializable source of truth for a frame
        ▼
Executor: execute_scene_to_engine2d    (single dispatch point; complete replay — §6)
        ▼
Facade:   Engine2D  (capability-aware backend selection — §4)
        ▼
Interface: trait RenderBackend  (ONE interface — §2)
        ▼
   ┌─────────────────────────────────────────────────────────────┐
   │ SharedRaster  (mixin/free-function reference — §3)           │  ← the parity oracle
   │   every Draw-IR op implemented over draw_rect_filled + fb    │
   └─────────────────────────────────────────────────────────────┘
        ▲ delegate unaccelerated ops          ▲ override accelerated ops
        │                                      │
   software / cpu / directx / …          metal / vulkan / cuda / cpu_simd / …
   (accelerate nothing → all shared)     (declare accelerated set; rest → shared)
```

---

## 2. ONE interface (resolve the three-trait drift)

**Decision D1 — collapse to a single trait `RenderBackend` + a capability descriptor; retire the
Core/Adv split as *dead code*.**

Rationale (from research §2): every backend already implements the flat `RenderBackend`; **nothing**
implements `RenderBackendCore`/`RenderBackendAdv`; the "implement Core, get Adv free" promise is
un-enforced. Rather than keep three traits and hope, we encode the same idea *correctly* with:

1. **`RenderBackend`** stays the sole trait every backend implements. Its method set = the union
   the executor needs to replay a complete scene (clear, fills, primitives, gradient, text, image,
   clip stack, mask, transform, present, sized readback). This is the **contract**.
2. A backend is **not required to accelerate** any op — the *shared reference* provides a correct
   body for all of them (§3). "Implement only what you accelerate" becomes true because the shared
   reference supplies the rest via delegation, not via a trait-inheritance trick the language
   forbids.
3. `RenderBackendCore` / `RenderBackendAdv` / their `.spl` files are **deleted** (or reduced to a
   doc note) once §3 lands — they encode a contract the shared reference now enforces at the
   call-forwarding layer. `Engine2DExtended` (`draw_text_bg`) folds into `RenderBackend` as an
   ordinary op with a shared body.

**Method surface of the unified `RenderBackend`** = current `RenderBackend` (backend.spl:21-44)
**plus** `capability() -> BackendCapability` (§4) **plus** the IR-completeness ops the executor must
be able to call (`draw_triangle_filled` already present; add `push_clip`/`pop_clip` stack form,
`set_transform`, `draw_glyph_run`, `draw_gradient_stops`, `draw_rect_blend_mode` — §6). Ops a
backend does not accelerate are satisfied by the shared reference (§3), so widening the trait costs
backends nothing.

---

## 3. Shared-logic layer — `SharedRaster` (the parity oracle)

**Decision D2 — `backend_emu.spl` becomes THE canonical software reference (`SharedRaster`); it is
the single bit-exact parity oracle. `backend_software.spl` is refactored to *be* that reference
plus SIMD span overrides — it stops being a second, independently-drifting implementation.**

### 3a. Shape (composition, not inheritance)

`SharedRaster` is a **mixin over `draw_rect_filled` + framebuffer access**. It is the set of
stateless functions already in `backend_emu.spl` (`emu_draw_*`), promoted to the canonical library
and re-parented from the flat trait onto the minimal core surface:

- **Core surface a backend must supply** (the irreducible kernel — matches today's
  `RenderBackendCore` intent, backend_core.spl:23): `clear`, `draw_rect_filled`, `draw_image`,
  `set_clip`/`clear_clip`, `set_mask`/`clear_mask`, `present`, `read_pixels`, `width`, `height`.
- **Everything else** (`draw_rect`, `draw_line`, `draw_circle[_filled]`, `draw_rounded_rect`,
  `draw_triangle_filled`, `draw_gradient_rect`, `draw_text`, blend variants, transforms, gradients,
  blur/shadow, polygons) has a `SharedRaster` reference body composed from that core surface —
  already written in `backend_emu.spl` + `backend_emu_adv.spl`.

A backend gets shared behavior by a **`shared_dispatch` mixin**: for each non-core op the backend
does not accelerate, its method body is a one-line delegation to the `SharedRaster` free function
(`me draw_circle_filled(...): shared_draw_circle_filled(self, ...)`). To kill the ~300 forwarding
stubs (research §3b), we provide a **`SharedRasterMixin` composition helper** that a backend
`include`s to auto-supply all non-accelerated methods; the backend then only overrides the handful
it accelerates. (If the language's mixin/`include` cannot yet auto-forward trait methods, the
fallback is a generated forwarding block — one macro/codegen source, not hand-written per backend —
recorded as **FR-RENDER-MIXIN** rather than silently tolerating the boilerplate, per repo rule.)

### 3b. Bit-exact contract (the oracle)

The shared reference defines the **canonical pixel math**; every backend's accelerated path must
match it bit-for-bit on readback. The blend primitive is `_emu_blend_over` (backend_emu.spl:642,
straight src-over on ARGB u32). The contract, restated as an acceptance invariant:

> For any scene S and any backend B, `B.read_pixels(S)` **==** `SharedRaster.read_pixels(S)`
> pixel-for-pixel, where equality is exact u32 ARGB match. Example anchor (src-over,
> 0xAARRGGBB): `blend_over(src=0x01020304, dst=0x10203040) == 0x101F2F3F`.

This makes the shared reference the **single oracle**: parity gates compare every backend against
`SharedRaster`, not against each other, so there is exactly one truth. Any op a backend does not
accelerate trivially passes (it *is* the oracle). Accelerated GPU ops must be validated against it.

### 3c. Consolidating the two references

`backend_software.spl` today re-derives fills and owns SIMD hooks. Under D2 it becomes:
`SoftwareBackend` supplies the **core surface** (owns the framebuffer, implements `draw_rect_filled`,
`draw_image`, clip, mask) with **SIMD span kernels** on the hot core ops; it inherits all
higher-level ops from `SharedRaster`. There is then **one** algorithm for circle/triangle/gradient
(in `SharedRaster`), fed by either scalar or SIMD `draw_rect_filled`/span fills underneath. No
second oracle.

---

## 4. Capability + honesty model

**Decision D3 — every backend advertises a `BackendCapability` descriptor; `Engine2D` selects and
labels backends from it; readback source and `gpu_frame_complete` are computed uniformly in the
shared base, not hand-set per backend.**

```
class BackendCapability:
    name: text                 # honest, e.g. "metal", "directx-software-emulation", "cpu-simd-neon"
    class_: text               # "real-gpu" | "software-emulation" | "software-reference"
    device_present: bool       # a real device was opened (probe result)
    accelerated_ops: [text]    # op kinds this backend runs natively; all others → SharedRaster
    readback_source: text      # what read_pixels actually returns: "gpu-readback" | "software-fb"
```

Rules enforced by the shared base:
- `name` **must** disclose emulation when `class_ == "software-emulation"` (directx already does —
  backend_directx.spl:22; generalize to cpu, and any GPU backend that failed to open a device and
  fell back).
- `readback_source` is set by the **actual** path taken (GPU present-then-readback vs shared-fb
  copy), not asserted. `Engine2DReadback.source` (backend.spl:5) is populated from it, closing the
  "claimed GPU while software fell back" hole (MEMORY 06-10).
- `gpu_frame_complete` (today metal-only, backend_metal.spl:215) becomes a **shared-base field**:
  set true only when *every* op in the frame was serviced by an accelerated path with a real
  device; any fall-through to `SharedRaster` on a real-GPU backend flips it false (metal already
  does this per-op — we lift the pattern into the base so vulkan/cuda get it identically).
- Selection: `Engine2D` picks the highest-priority backend whose `device_present` is true; if none,
  it selects `SoftwareBackend` (or `cpu-simd`) and the descriptor honestly says
  `class_ == "software-reference"`. `SIMPLE_2D_BACKEND` override (engine.spl) still wins but the
  descriptor still tells the truth about what got selected.

---

## 5. SIMD-CPU as a first-class backend (not a parallel one)

**Decision D4 — SIMD-CPU is the `SoftwareBackend` core surface with SIMD-accelerated span kernels;
it is selected as `cpu-simd` and declares `accelerated_ops = [fill spans, copy, alpha-blend]`. It
does not fork the higher-level raster logic.**

- The hot kernels are `draw_rect_filled` (span fill), `draw_image` (copy), and alpha blend — exactly
  where `backend_software` already records `record_simd_{fill,copy,alpha}_hit` (research §5).
- Arch dispatch (x86 SSE/AVX, arm NEON — genuine per MEMORY 06-03, riscv RVV) routes through the
  existing `simd_provider` probes; scalar fallback when no ISA span kernel is available.
- Because circle/triangle/gradient/text all funnel through `draw_rect_filled`/spans in
  `SharedRaster`, accelerating the spans accelerates **every** higher-level op with **zero** risk of
  parity drift — the algorithm is unchanged, only the innermost fill is vectorized. This is the
  cleanest possible "SIMD without a parallel backend."

---

## 6. Draw-IR completeness (make the scene the sole source of truth)

Extend `SceneCommand`/`RenderScene` and the **executor** so a serialized scene fully describes a
frame (research §6). Keep the single struct (no numbered splits); add kinds/fields:

| Add | Kind / field | Executor action |
|---|---|---|
| Clip **stack** | keep `clip_push`/`clip_pop`, define **intersection** stack semantics | maintain clip stack; backend `push_clip`/`pop_clip` |
| **Mask** | `mask_set` (pixels [u8], w, h) / `mask_clear` | `engine.set_mask` / `clear_mask` (trait already has these) |
| Gradient **stops** + direction | `gradient` gains `stops: [(offset,color)]`, `dir: text` (v/h/radial) | `draw_gradient_stops`; 2-color stays a fast path |
| **Transform / CTM** | `transform_set(a,b,c,d,tx,ty)` | `set_transform`; image/primitive ops apply it |
| **Glyph run** | `glyph_run(font, size, glyphs, x, y, color)` | `draw_glyph_run`; plain `text` stays a fallback |
| **Triangle / polygon** | `triangle`, `polygon(xs,ys)` | `draw_triangle_filled` / `draw_polygon_filled` |
| **Blend mode** | `blend_mode: i32` on paint ops | `draw_rect_blend_mode` |
| Fix replay holes | `blur_rect` (in IR, dropped by executor) | wire to `draw_blur_rect` |

The **executor stays the single dispatch point**; every new kind routes there. Default background
`clear` should be a scene command, not the hardcoded white (engine2d_executor.spl:31), so headless
replay is deterministic.

---

## 7. Adding a new backend — the seam

To add backend `Foo`, an implementer:
1. Implements the **core surface** (§3a): `clear`, `draw_rect_filled`, `draw_image`, clip, mask,
   present, `read_pixels`, `width`, `height`.
2. Includes the **`SharedRasterMixin`** — every non-core op now works via the oracle. Foo is
   already correct and passes the parity gate at this point.
3. Declares a **`BackendCapability`** (name, class, device_present probe, `accelerated_ops=[]`).
4. **Optionally** overrides individual ops with native kernels, adding each to `accelerated_ops`;
   each override must pass the bit-exact gate against `SharedRaster`.

"Implement 9 core methods + a capability descriptor, get a complete honest backend free; accelerate
incrementally." That is the whole onboarding cost.

- **DirectX/Vulkan/Metal/CUDA/etc.** each map their `accelerated_ops` to native kernels; everything
  else → `SharedRaster`. Metal/Vulkan (real GPU) keep their present+readback path and set
  `readback_source="gpu-readback"`; on any device-open failure they downgrade honestly to
  `software-emulation` and their name discloses it.

---

## 8. Web-lane fold-in (SIMPLE_WEB_GPU_PAINT)

The web GPU-paint path (research: emits `SceneCommand`s dispatched as per-primitive Metal calls,
parity kept via residual-vs-readback blit) is **already** a Draw-IR producer. Under this design it
stops being a special path:
- Its emitter produces the extended `RenderScene`; the **standard executor** replays it against the
  selected backend (Metal when present).
- Parity is no longer "residual-vs-readback blit" bookkeeping but the **standard shared-oracle
  gate**: web-lane Metal output is compared to `SharedRaster` on the same scene. The residual-blit
  becomes an optimization detail behind the capability descriptor, not a separate correctness story.
- `browser_engine/simple_web_layout_engine2d_fast.spl` and the HTML presenters become ordinary
  `Engine2D` clients.

---

## 9. MDSOC+ placement & module layout

- **Reuse the existing `src/lib/gc_async_mut/gpu/engine2d/` directory** — no new numbered split, no
  `engine2d_v2` (repo rule). Files evolve in place:
  - `backend_emu.spl` → promoted to `SharedRaster` canonical reference (add `SharedRasterMixin`).
  - `backend_core.spl` defines the **core surface** the mixin needs; `backend_adv.spl` deleted or
    reduced to a doc pointer once the mixin lands.
  - New `backend_capability.spl` — the `BackendCapability` type + honesty helpers.
  - `backend_software.spl` → core-surface + SIMD spans only (higher ops from `SharedRaster`).
  - `backend.spl` — unified `RenderBackend` (+`capability()`), `Engine2DExtended` folded in.
- **Draw-IR** stays in `common/render_scene/` (pure, dependency-light — correct MDSOC layer).
- **Executor** stays in `gc_async_mut/render_scene/` as the single dispatch point (mirror the
  `gc_sync_mut` variant).
- **MDSOC+**: rendering is a userland service surface → MDSOC outer facade (`Engine2D`) + the
  backend set as the business/driver layer; `baremetal`/`virtio_gpu` stay MDSOC-only (kernel/driver)
  and simply implement the same core surface — they get `SharedRaster` for free like everyone else.

---

## 10. Honesty — exists / designed / deferred

**Exists (reused as-is):** `RenderBackend` trait, `SceneCommand`/executor single dispatch,
`backend_emu` reference bodies, `backend_software` SIMD hooks, directx honest naming, metal
`gpu_frame_complete`, `Engine2DReadback.source`, `SIMPLE_2D_BACKEND`/`cpu_simd` selection.

**Designed here (new):** single-trait consolidation + retirement of Core/Adv (D1); `SharedRaster`
as the one parity oracle with the `SharedRasterMixin` to kill forwarding boilerplate (D2);
`BackendCapability` + uniform readback/`gpu_frame_complete` in the shared base (D3); SIMD-CPU as
span-override of the software core, not a fork (D4); IR-completeness additions (masks, stops,
transforms, glyph runs, triangle/polygon, blend modes, executor replay of blur); the add-a-backend
seam; web-lane fold-in.

**Deferred / risks:** if language mixin/`include` cannot auto-forward trait methods, the boilerplate
kill needs codegen (**FR-RENDER-MIXIN**) — not silent tolerance. Real GPU parity for
transform/glyph-run may lag the reference (accelerate later; correctness via `SharedRaster`
meanwhile). Known blockers to respect in the plan: **engine2d drift** (line/circle CPU↔GPU,
MEMORY 06-03), **metal readback** falling back to software silently (MEMORY 06-10), **JIT-render
crash** on some winit/graphics apps (needs `SIMPLE_EXECUTION_MODE=interpret`, MEMORY 06-06).
