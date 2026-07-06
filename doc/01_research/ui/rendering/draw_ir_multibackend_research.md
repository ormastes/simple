<!-- opus-research 2026-07-06 -->
# Draw-IR Multi-Backend Rendering — Research

**Goal (verbatim user intent):** "draw-ir rendering should support variety backend,
simd cpu, directx, metal, vulkan and so on. and share logic and same interfaces
between backends."

**Finding in one line:** the interface and the backend variety already exist; the
shared-logic layer *also* already exists (`backend_emu.spl`) — but it is applied
inconsistently, duplicated by a second reference (`backend_software.spl`), targets a
trait that has drifted, and there is **no capability/honesty model**. The problem is
**coherence**, not greenfield.

Cross-references (do not duplicate): `doc/05_design/ui/renderer_unification_2026-06-15.md`
(common/web/text on one 2D API), `doc/03_plan/ui/backend_taxonomy/backend_taxonomy_plan.md`
(shell peers: Electron/Tauri/pure-Simple — a *different* axis), `doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md`
(Draw.io SDN diagram IR — unrelated). This document is about the **GPU/CPU
rasterization backend** axis under `src/lib/gc_async_mut/gpu/engine2d/`.

---

## 1. Today's layering (verified file:line)

```
UI / WM / web layout
        │  builds display list
        ▼
Draw-IR:  common.render_scene  (SceneCommand / RenderScene)      src/lib/common/render_scene/scene.spl:7
        │  single dispatch point
        ▼
Executor: execute_scene_to_engine2d(scene, engine)              src/lib/gc_async_mut/render_scene/engine2d_executor.spl:19
        │  maps cmd.kind → engine method
        ▼
Facade:   Engine2D  (auto-selects a backend)                    src/lib/gc_async_mut/gpu/engine2d/engine.spl
        │  delegates every op to the active backend
        ▼
Interface: trait RenderBackend                                  src/lib/gc_async_mut/gpu/engine2d/backend.spl:21
        │
        ├─ Shared reference (stateless):  backend_emu.spl       (emu_draw_* over core.draw_rect_filled)
        │
        ▼
N backends: metal, vulkan, cuda, rocm, intel, opencl, opengl, qualcomm,
            webgpu, virtio_gpu, cpu, software, directx, baremetal, accel_{metal,vulkan,cuda}
```

### 1a. What each layer carries

| Layer | Ops it exposes | Notes |
|---|---|---|
| **Draw-IR** `SceneCommand` (scene.spl:7-22) | fill_rect, stroke_rect, text, line, circle, circle_filled, rounded_rect, gradient_rect (2-color), image, clip_push, clip_pop, blur_rect | Flat struct, `kind: text` string tag. Fields overloaded (line stores x2/y2 in width/height). No masks, transforms, gradient **stops**, glyph runs, triangle/polygon, blend modes. |
| **Executor** (engine2d_executor.spl:19-81) | fill_rect, stroke_rect, text, line, circle, circle_filled, rounded_rect, gradient_rect, image, clip_push, clip_pop | **Single dispatch point** (good). But does **not** replay `blur_rect` (in IR, dropped here), triangle, polygon, mask. Hardcodes `clear(0xFFFFFFFF)` white background (line 31). |
| **`RenderBackend`** (backend.spl:21-44) | clear, draw_rect[_filled], draw_line, draw_circle[_filled], draw_rounded_rect, draw_triangle_filled, draw_gradient_rect, draw_text, draw_image, set_clip, clear_clip, set_mask, clear_mask, present, read_pixels[_with_source], width, height | The **real** interface — every backend implements this flat trait. Richer than the IR (has masks, triangles) but poorer than `RenderBackendAdv`. |
| **`RenderBackendAdv`** (backend_adv.spl:23-90) | + ellipse, arc, bezier, polygon, polyline, thick outlines, h/radial gradients, blend variants, image scale/transform, blur, shadow, blend modes | **Aspirational** — see drift below. |

---

## 2. The three-trait drift (interface incoherence #1)

There are **three** backend traits plus an extension trait:

- `RenderBackend` — flat, everything-in-one (backend.spl:21).
- `RenderBackendCore` — minimal irreducible set (backend_core.spl:23), doc claims "implement only this and get Adv for free."
- `RenderBackendAdv` — optimized ops (backend_adv.spl:23).
- `Engine2DExtended` — `draw_text_bg` only (backend.spl:46).

**Verified reality:** every backend implements the *flat* trait —
`impl RenderBackend for {Cuda,Metal,Cpu,OpenCl,Baremetal,Rocm,Software,DirectX,Intel,OpenGL,Qualcomm,VirtioGpu,WebGpu,Vulkan}Backend`.
There is **zero** `impl RenderBackendCore for …` or `impl RenderBackendAdv for …` in the tree.
The Core/Adv split is **documentation-only / dead code**: the promised "implement Core, get
Adv free" contract is not wired through the type system. `backend_emu.spl` even imports
`RenderBackend` (the flat trait), not `RenderBackendCore` (backend_emu.spl:21) — so the emulation
layer is glued to the flat trait, contradicting its own header comment ("using ONLY
RenderBackend methods" — but the *design intent* was Core methods).

**Consequence:** the elegant capability idea ("a Core-only backend gets everything") exists on
paper but is unenforceable and unused. This is the single biggest coherence liability.

---

## 3. Shared logic vs duplication (the crux)

### 3a. Two shared reference implementations coexist (redundancy)

1. **`backend_emu.spl`** — stateless. 34 `emu_draw_*` functions, each composes the target op
   from `core.draw_rect_filled` (rect outline = 4 fills, backend_emu.spl:42; Bresenham line :54;
   midpoint circle :96; scanline triangle :199; gradient row-lerp :249; src-over blend :642 via
   `_emu_blend_over`). This is a clean, backend-agnostic **software reference**.
2. **`backend_software.spl`** — stateful (30 KB). Owns a pixel buffer, has its own fills, and
   wires **SIMD hooks** (`record_simd_fill_hit` at :137/:202/:685, `record_simd_copy_hit`,
   `record_simd_alpha_hit`) via `simd_provider`. This is a *second*, richer reference rasterizer.

So there are **two oracles**. `emu` is the composable fallback; `software` is the fast path with
SIMD. They can (and historically did — see MEMORY float→int lerp fixes) drift bit-for-bit. A
unified design must pick **one canonical parity oracle** and make the other a strict subset.

### 3b. Who delegates to shared logic vs who re-implements

**Delegate to `backend_emu`** (import it, ~30 `emu_draw_*` call sites each): vulkan, rocm, intel,
opencl, opengl, qualcomm, virtio_gpu, webgpu, software, baremetal. But delegation is **manual
per-method forwarding boilerplate** — each backend hand-writes ~30 wrapper methods
`me draw_circle_filled(...): emu_draw_circle_filled(self, ...)`. ~30 methods × ~10 backends ≈
**300 forwarding stubs** that exist only because the Core/Adv "free Adv" contract is not wired.

**Do NOT import `backend_emu`** (reimplement locally): cpu, cuda, directx, metal, accel_*.
Breaking that down:
- **cpu** (backend_cpu.spl:16) and **directx** (backend_directx.spl:127) — *honest composition*:
  they hold an internal `SoftwareBackend` and forward to it (cpu :79-86, directx wraps
  `sw: SoftwareBackend`). No algorithm duplication — this is the good pattern, just not generalized.
- **cuda** (backend_cuda.spl:549), **metal** (backend_metal.spl:237) — real GPU kernels **plus**
  local scalar fallbacks that re-derive fills/blends. This is **genuine algorithm duplication** of
  the reference math, and the historical source of parity drift (MEMORY 06-03 line/circle divergence).

**Duplication sites to eliminate:** every backend that has a local `draw_circle_filled`,
`draw_triangle_filled`, `draw_gradient_rect`, blend, and clip/mask/bounds body that is not a GPU
kernel is re-implementing the reference — 15 files carry a `draw_circle_filled` (grep-verified).

---

## 4. Honesty / consistency gaps

| Gap | Evidence | Impact |
|---|---|---|
| **No capability descriptor** | grep for `capabilit`/`is_real_gpu`/`accelerated_ops`/`BackendCapability` finds no unified type | Callers cannot ask "is this real GPU?" / "which ops are accelerated?" |
| **`gpu_frame_complete` is metal-only** | field + reset only in backend_metal.spl:215,232 (reset to false per unaccelerated op) | Other real-GPU backends (vulkan, cuda) have no equivalent — readback truth is per-backend ad hoc |
| **Readback source string is the only honesty channel** | `Engine2DReadback.source` (backend.spl:5), `read_pixels_with_source` | Free-text, not validated; easy to lie (past "GPU_RENDERED" while software fell back — MEMORY 06-10) |
| **Dishonest names historically** | directx **fixed** → `"directx-software-emulation"` with disclosure comment (backend_directx.spl:13-25); accel_metal → `"metal-accel"` (:200) | directx is the good precedent; other CPU-delegate backends should follow |
| **Core/Adv drift** | §2 | Interface promises a contract the code doesn't keep |

directx is the model of an honest CPU-emulation backend: name discloses emulation, `read_pixels`
copies the software framebuffer, the D3D11 device is used only for dispatch/probe. P2 should make
every CPU-delegate backend match this.

---

## 5. SIMD-CPU reality

- `simd_provider.spl` exists in **4 stdlib variants** + `src/compiler/85.mdsoc/feature/optimization/`.
- `backend_software` records SIMD fill/copy/alpha hits (backend_software.spl:137/202/685) — the
  hot span kernels are the SIMD seam. MEMORY (06-03) confirms **genuine NEON kernels verified in
  `fill_span`**; other lanes historically scalar with accounting hooks.
- Selection: `SIMPLE_2D_BACKEND=cpu_simd` is a recognized key in `engine2d_env_backend_override`
  (engine.spl). So **SIMD-CPU is a *lane over the software reference*, not a separate backend
  class** — exactly where a first-class SIMD backend should slot: same interface, override only
  the hot fill/blend/copy spans, scalar (or emu) fallback for everything else.
- Probes for arch dispatch (x86 SSE/AVX, arm NEON, riscv RVV) exist in the compiler/runtime SIMD
  layer; the design must route the software reference's span kernels through them.

---

## 6. Draw-IR completeness gaps (for full backend-agnostic replay)

`SceneCommand` (scene.spl) cannot yet express everything `RenderBackend` accepts, so a scene is
**not** a faithful serialization of what backends can draw:

| Backend/trait op | In Draw-IR? | Gap |
|---|---|---|
| clip rect push/pop | yes (`clip_push`/`clip_pop`) | **stack** semantics implicit; nested clips = intersection not modeled |
| **mask** (`set_mask`/`clear_mask`) | **no** | trait has it; IR + executor drop it |
| gradient | 2-color only | no **stops**, no direction (h/v/radial), no matrix |
| text | plain string + size | no font family/weight, no **glyph runs**, no color spans |
| transform | **no** | trait has `draw_image_transform`; IR has no transform/CTM |
| triangle / polygon | **no** | trait has `draw_triangle_filled`; IR drops it |
| blend mode | **no** | trait has `draw_rect_blend_mode`; IR drops it |
| blur | in IR, **not in executor** | replay hole |

The **executor** (engine2d_executor.spl:19) is correctly the single dispatch point, but it is
incomplete relative to the IR (blur dropped) and relative to the trait (no mask/triangle/transform).

---

## 7. How other engines solve this (transferable patterns)

- **Skia** — `SkCanvas` records ops; `SkDevice`/`SkBitmapDevice` is the CPU reference; GPU
  (`GrRecordingContext` → Ganesh/Graphite) implements a device that **accelerates what it can and
  the raster device is the correctness baseline**. Transferable: *one recorder, one reference
  device, GPU devices override only accelerated ops.*
- **WebRender** — a display list (our `RenderScene`) is the single serializable IR; a batching
  frame-builder replays it; the GPU is the only backend but the display list is fully
  self-describing (clips as a **stack/tree**, gradients with **stops**, glyph runs, transforms).
  Transferable: *make the IR complete enough to be the sole source of truth.*
- **wgpu / a backend-agnostic HAL** — one trait, N implementations (Vulkan/Metal/DX12/GL), each
  maps a uniform command set to native calls; unsupported features are advertised via a
  **capabilities/features struct**, not discovered by crashing. Transferable: *capability
  descriptor + one interface; fall back, don't fake.*

**Synthesis for Simple:** a shared **command recorder** (`RenderScene`) + **one software reference
rasterizer** (the parity oracle) + **GPU backends that declare an accelerated-op set and delegate
everything else to the shared reference**, with a **capability descriptor** advertising real-GPU vs
software-emulation and per-op acceleration. Simple already has every piece except the capability
model and a single-oracle consolidation — this is assembly, not invention.

---

## 8. Honesty — exists / partial / missing

**Exists today (verified):**
- Draw-IR (`SceneCommand`/`RenderScene`), single executor dispatch point, flat `RenderBackend`
  trait, ~17 backends, a stateless shared reference (`backend_emu`), a SIMD-hooked software
  reference (`backend_software`), `cpu_simd` selection key, directx honest naming precedent,
  `Engine2DReadback.source` honesty channel, per-op `gpu_frame_complete` on metal.

**Partial:**
- Shared logic (two competing references; ~10 backends delegate via boilerplate, 4 reimplement).
- SIMD (genuine NEON in `fill_span`; other lanes/arches scalar-with-hooks).
- Honesty (directx honest; metal has frame-complete; others ad hoc).

**Missing / not designed:**
- Capability descriptor type; enforced Core/Adv "free Adv" contract; single canonical oracle;
  IR completeness (masks, stops, transforms, glyph runs, triangles, blend modes); executor replay
  of blur/triangle/mask/transform; uniform readback bookkeeping across GPU backends; a
  formal seam for adding a backend.

These gaps are the agenda for the Design and Plan documents.
