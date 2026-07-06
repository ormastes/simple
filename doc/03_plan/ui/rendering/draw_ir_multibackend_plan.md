<!-- opus-plan 2026-07-06 -->
# Draw-IR Multi-Backend Rendering — Plan

**Design:** `doc/05_design/ui/rendering/draw_ir_multibackend_design.md`.
**Research:** `doc/01_research/ui/rendering/draw_ir_multibackend_research.md`.

Six phases. Each is **Sonnet-sized**, **independently landable**, ships an SSpec, and passes a
**parity-vs-shared-oracle gate**: every backend's `read_pixels(scene)` must equal
`SharedRaster.read_pixels(scene)` bit-for-bit (ARGB u32 exact). The oracle anchor test:
`blend_over(0x01020304, 0x10203040) == 0x101F2F3F`. Phases P1-P2 are behavior-preserving refactors
(all existing backends still green); P3+ add capability incrementally. No branches — land each on
`main`. Reuse `src/lib/gc_async_mut/gpu/engine2d/` (no numbered splits).

---

## P1 — Extract & formalize the shared reference + capability descriptor (refactor, behavior-preserving)

**Do:** promote `backend_emu.spl` to the canonical `SharedRaster` (rename functions
`emu_draw_*` → `shared_draw_*` with a compat re-export); re-parent its bodies onto the **core
surface** (`backend_core.spl`'s minimal set) rather than the flat trait; add
`backend_capability.spl` with `BackendCapability`. Provide `SharedRasterMixin` (or, if the language
cannot auto-forward, a single generated forwarding block — file **FR-RENDER-MIXIN**, do not
hand-duplicate).

**Files:** `backend_emu.spl`, `backend_emu_adv.spl`, `backend_emu_math.spl` (→ SharedRaster);
`backend_core.spl` (core surface = contract); **new** `backend_capability.spl`; `backend.spl`
(add `capability()` to `RenderBackend`); `engine.spl` (import shared names).

**Gate:** all ~14 backends compile and pass the existing parity comparison unchanged; new SSpec
`shared_raster_oracle_spec.spl` pins the blend/circle/triangle/gradient reference outputs
(bit-exact anchors incl. `0x101F2F3F`).

**Risks:** rename churn across ~12 delegating backends → keep compat re-exports for one phase.
Behavior must not change (this is the safety net for P4). Watch **engine2d drift** (MEMORY 06-03):
lock line/circle reference outputs in the spec now so later phases can't regress them.

---

## P2 — Convert CPU-delegate backends to explicit software-emulation + shared logic (honest, dedup)

**Do:** make `cpu`, and any GPU backend that fails device-open, follow the **directx precedent**
(backend_directx.spl:13-25): `class_="software-emulation"`, name discloses emulation,
`readback_source="software-fb"`, all non-core ops routed through `SharedRaster` (delete any local
re-derived raster math). directx is already honest — formalize it against the new descriptor.

**Files:** `backend_cpu.spl`, `backend_directx.spl`, `backend_software.spl` (declare
`class_="software-reference"`), `backend_accel_*` (honest `*-accel` names + descriptors).

**Gate:** parity-vs-oracle still exact; **honesty spec** `backend_honesty_spec.spl` asserts every
backend whose device is absent has an emulation-disclosing `name` and `readback_source != "gpu-*"`.

**Risks:** removing local raster bodies from cuda/metal is **deferred to P4** (they have real
kernels); P2 only touches pure CPU-delegate paths. No perf regression expected (same software path,
one algorithm).

---

## P3 — SIMD-CPU accelerated spans behind the shared interface

**Do:** make `SoftwareBackend` the SIMD core-surface: route `draw_rect_filled` span fill,
`draw_image` copy, and alpha blend through `simd_provider` arch kernels (x86 SSE/AVX, arm NEON —
genuine per MEMORY 06-03; riscv RVV), scalar fallback otherwise. Select as `cpu-simd`
(`SIMPLE_2D_BACKEND=cpu_simd` already recognized); declare `accelerated_ops=[fill,copy,alpha]`.
Higher-level ops stay in `SharedRaster` unchanged.

**Files:** `backend_software.spl`, `simd_provider.spl` (4 variants), `engine.spl` (selection),
`backend_capability.spl` (cpu-simd descriptor).

**Gate:** `cpu-simd` output **bit-exact** to `SharedRaster` scalar (SIMD must not change pixels,
only speed); micro-bench shows span-fill speedup on at least one ISA; `record_simd_*_hit` counters
prove the SIMD path was taken (not silent scalar fallback — the historical fake-evidence trap).

**Risks:** SIMD lanes historically scalar-with-accounting-hooks; the gate must prove the vector path
executed AND matches bit-for-bit. Do not accept an accounting counter as proof of vectorization.

---

## P4 — Metal/Vulkan declare accelerated-op sets, fall through to shared logic, uniform readback

**Do:** for `metal`, `vulkan`, `cuda`, `rocm`, `intel`, `opencl`, `opengl`, `qualcomm`,
`webgpu`, `virtio_gpu`: (a) delete local re-derived raster fallbacks; unaccelerated ops → `SharedRaster`;
(b) populate `accelerated_ops` with the ops that truly hit native kernels; (c) lift
`gpu_frame_complete` bookkeeping into the shared base — any fall-through to `SharedRaster` on a
real-GPU backend flips it false (metal already does this per-op, backend_metal.spl — generalize);
(d) `readback_source` set by the actual path.

**Files:** `backend_metal.spl`, `backend_vulkan.spl`, `backend_cuda.spl`, and the rest listed;
shared-base helper in `backend.spl`/`backend_capability.spl`.

**Gate:** for each backend, every op in `accelerated_ops` passes bit-exact vs `SharedRaster`; every
op NOT in the set is *served by* `SharedRaster` (proven by an op-coverage spec); `gpu_frame_complete`
is true **only** when the whole frame was accelerated with a present device.

**Risks:** **metal readback silently falling back to software** (MEMORY 06-10) — the gate must
distinguish gpu-readback from software-fb via `readback_source`, and a frame that fell back must NOT
report `gpu_frame_complete=true`. Real-GPU raster may not match the reference for AA'd primitives —
if a native kernel can't be bit-exact, it must **not** be listed in `accelerated_ops` (fall through
instead). File any genuine kernel≠reference divergence as a bug rather than loosening the gate.

---

## P5 — Draw-IR completeness + executor replay coverage

**Do:** extend `SceneCommand`/`RenderScene` and the executor (design §6): clip **stack** semantics,
`mask_set`/`mask_clear`, gradient **stops**+direction, `transform_set`/CTM, `glyph_run`,
`triangle`/`polygon`, `blend_mode`; wire the existing-but-dropped `blur_rect`; make background
`clear` a scene command (remove hardcoded white, engine2d_executor.spl:31).

**Files:** `common/render_scene/scene.spl`, `gc_async_mut/render_scene/engine2d_executor.spl`
(+ `gc_sync_mut` mirror), `backend.spl` (trait ops: `push_clip`/`pop_clip`, `set_transform`,
`draw_glyph_run`, `draw_gradient_stops`), `SharedRaster` (reference bodies for the new ops).

**Gate:** round-trip spec `scene_replay_completeness_spec.spl` — a scene using every new kind
replays through the executor and matches `SharedRaster` bit-exact; masks/clips/transforms verified
against hand-computed reference frames.

**Risks:** field-overloading in the flat `SceneCommand` (line stores x2/y2 in width/height) — new
fields must not collide; keep the single struct (no numbered split). Text→glyph-run is a superset;
plain `text` stays a fast path so existing scenes are untouched.

---

## P6 — Fold web-lane GPU-paint into the unified model; migrate parity gates

**Do:** retarget `SIMPLE_WEB_GPU_PAINT` emitters to produce the extended `RenderScene` and replay
through the **standard executor** against the selected backend; replace the residual-vs-readback
blit *correctness* story with the standard shared-oracle gate (residual-blit stays only as an
optimization behind the capability descriptor). Make the browser_engine presenters ordinary
`Engine2D` clients.

**Files:** `gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`,
`simple_web_html_engine2d_presenter.spl`, `simple_web_html_layout_renderer.spl`,
`app/wm_compare/production_gui_web_renderer_parity.spl` (migrate its gate).

**Gate:** web-lane Metal output == `SharedRaster` on the same scene (replaces bespoke parity);
existing web-parity SSpecs still green; the parity gate references the single oracle, not a
per-lane baseline.

**Risks:** **JIT-render crash** on winit/graphics apps (MEMORY 06-06) — run web-lane verification
under `SIMPLE_EXECUTION_MODE=interpret` where needed. Retina 2x capture stride artifacts
(MEMORY 06-02) — keep the box-downsample fix; parity compares logical pixels.

---

## Sequencing & landability

- **P1, P2** are behavior-preserving — safe to land first, in order (P2 depends on P1's descriptor).
- **P3** (SIMD) and **P4** (GPU accel-set) are independent of each other once P1 lands — can run in
  parallel by two Sonnet sessions on disjoint files (software/simd vs metal/vulkan).
- **P5** (IR) is independent but should precede **P6** (web fold-in needs the extended IR).
- Every phase leaves the tree green and the oracle gate passing; no phase requires a bootstrap
  rebuild (pure-Simple stdlib edits) — deploy via the self-hosted binary per repo default.

## Filed bugs / feature requests to reference in commits
- **FR-RENDER-MIXIN** — auto-forwarding of non-accelerated trait methods (kills ~300 stubs); if
  mixin/`include` can't do it, needs codegen. (P1)
- **engine2d drift** — CPU↔GPU line/circle bit divergence (MEMORY 06-03). Lock reference in P1 spec. (P4)
- **metal readback fallback** — silent software fallback reporting as GPU (MEMORY 06-10). Gate via
  `readback_source`. (P4)
- **JIT-render crash** — winit/graphics apps panic under JIT; use interpret mode. (P6)

## Honesty — exists / to-build / deferred
**Exists:** IR, executor, flat trait, `backend_emu` reference, `backend_software` SIMD hooks,
directx honest naming, metal `gpu_frame_complete`, readback source channel, cpu_simd key.
**To build (this plan):** SharedRaster consolidation + mixin (P1), honest capability descriptors +
dedup (P2), real SIMD spans with proof (P3), GPU accel-sets + uniform readback (P4), IR completeness
(P5), web fold-in (P6).
**Deferred:** codegen for forwarding if mixins insufficient (FR-RENDER-MIXIN); bit-exact GPU AA for
transform/glyph-run (fall through to reference until achievable).
