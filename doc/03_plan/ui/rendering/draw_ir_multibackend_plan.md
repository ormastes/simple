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

## P1 — Prerequisite harness gate, dead-code retirement, and the shared reference + capability descriptor (refactor, behavior-preserving)

**Do:**
(a) **Bit-exact validation harness — PREREQUISITE GATE, must land and pass before anything in this
plan switches a core op to delegate to `SharedRaster`.** `backend_software.spl`'s ~9 core ops
(rect, line, circle, circle_filled, rounded_rect, triangle_filled, gradient_rect, text, text_bg —
e.g. `draw_circle` at backend_software.spl:227) are **independently hand-written**, never proven
equal to `backend_emu`'s reference math. Promoting `backend_emu` to the oracle is therefore **not**
automatically behavior-preserving. Build/land the harness (already underway at
`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`) comparing emu vs. software
per op; where they diverge, pick the canonical algorithm **per op** and file a bug for the
divergence — do not let the design presume `backend_emu` wins by default.
(b) Promote `backend_emu.spl` (23 ops) + `backend_emu_adv.spl` (5 ops) — **28 total, corrected from
an earlier "~34"** — to the canonical `SharedRaster` (rename functions `emu_draw_*` →
`shared_draw_*` with a compat re-export); unify the byte-identical duplicate blend implementations
(`color.spl`'s `blend()` and `backend_emu_math.spl:33`'s `_emu_blend_over` — not backend_emu.spl:642,
which is only the `emu_draw_rect_blend` call site) into the one reference. Re-parent bodies onto the
**core surface** (`backend_core.spl`'s minimal set) rather than the flat trait; add
`backend_capability.spl` with `BackendCapability`.
(c) **Forwarding stubs stay hand-written in this phase — do NOT attempt stub elimination here.**
Two independent checks (an adversarial verification pass and a separate coherence audit) confirmed
the shipped compiler does not auto-forward trait/mixin methods: the offline `src/app/desugar`
five-pass rewrite is reachable only via the explicit `bin/simple desugar <file>` CLI subcommand
(`main_and_help.spl:312`, file-delegation to `app/desugar/mod.spl`); the real build pipeline's
`desugarer:` port is wired to `_noop_desugar` (`compiler_services.spl:157,244`,
`create_default_services()`), with no other `desugarer:` override anywhere in `src/`. File the
mixin idea separately as **FR-RENDER-MIXIN** (wire `src/app/desugar` into the compiler front-end,
not just the CLI subcommand; preserve return-type annotations the offline pass currently drops; add
an end-to-end test using `alias` with zero hand-written stubs) and mark it a **prerequisite for a
later, currently-unscheduled stub-cleanup phase** — it is not part of P1.
(d) Resolve the `RenderBackend` naming collision: `engine2d/backend.spl`'s pixel-level trait vs. the
unrelated widget-tree trait in `common/ui/backend.spl:22-40` (2 implementors: `fb_backend.spl`,
`browser_backend.spl`). Rename the widget-tree side (fewer implementors) so the 14 GPU backends are
untouched; do this early so later phases' greps/refactors are unambiguous.
(e) Retire the two other dead shared-interface attempts alongside Core/Adv: `ComputeSession`
(backend_session.spl:78-95, zero implementations) and the textual `RenderBackend` copy in
`nogc_async_mut/gpu/engine2d/backend.spl` (byte-for-byte duplicate of the canonical trait, separate
nominal type, no facade re-export — will drift the moment either side adds a method).
(f) Collapse the `Engine2D` facade's dead 3-way branch (~35 methods, e.g. `clear` engine.spl:534-541)
to a single `self.backend` call — every constructor already sets `backend`/`baremetal_backend`/
`virtio_gpu_backend` to the identical object, so this is behavior-preserving by inspection.
(g) Unify the two disagreeing backend-selection paths: `Engine2D.probe_backend()`
(engine.spl:323-412, real per-class probes) vs. `compute_dispatch.spl`'s `BackendProber`/
`_strict_probe_backend` (backend_probe.spl:107-148 — no branch for cuda/opencl, permanent
`Unavailable` for rocm, a `probe_cpu_simd_x86()` miswiring that hits the wrong branch). Make
`Engine2D.probe_backend()` the single source of truth and route `compute_dispatch.spl` through it.

**Files:** `backend_emu.spl`, `backend_emu_adv.spl`, `backend_emu_math.spl` (→ SharedRaster);
`color.spl` (delete duplicate `blend()`); `backend_core.spl` (core surface = contract);
`backend_session.spl` (retire `ComputeSession`); `nogc_async_mut/gpu/engine2d/backend.spl`
(reconcile/delete duplicate trait); `common/ui/backend.spl` (rename to resolve naming collision);
**new** `backend_capability.spl`; `backend.spl` (add `capability()` to `RenderBackend`); `engine.spl`
(collapse dead 3-way branch; import shared names); `compute_dispatch.spl`, `backend_probe.spl`
(unify selection path); **new** `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`
(the prerequisite harness, in progress).

**Gate:** the bit-exact harness (a) passes first, before any core-op delegation switch; all ~14
backends compile and pass the existing parity comparison unchanged; new SSpec
`shared_raster_oracle_spec.spl` pins the blend/circle/triangle/gradient reference outputs
(bit-exact anchors incl. `0x101F2F3F`); the naming-collision rename and dead-branch collapse leave
all existing specs green; `compute_dispatch.spl`'s answers now agree with `Engine2D.probe_backend()`
for every backend name (single source of truth).

**Risks:** rename churn across ~12 delegating backends → keep compat re-exports for one phase.
Behavior must not change (this is the safety net for P4). Watch **engine2d drift** (MEMORY 06-03):
lock line/circle reference outputs in the spec now so later phases can't regress them. The harness
(a) may surface real emu-vs-software divergences beyond line/circle — file each as a bug rather than
loosening the gate. FR-RENDER-MIXIN is **not** a dependency for landing P1 itself — only for the
later, unscheduled stub-cleanup phase.

---

## P2 — Convert CPU-delegate backends to explicit software-emulation + shared logic (honest, dedup)

**Do:** make `cpu`, and any GPU backend that fails device-open, follow the **directx precedent**
(backend_directx.spl:13-25): `class_="software-emulation"`, name discloses emulation,
`readback_source="software-fb"`, all non-core ops routed through `SharedRaster` (delete any local
re-derived raster math). directx is already honest — formalize it against the new descriptor.
**Fold in WebGPU (live dishonest backend, same class DirectX had before its fix):** `init()`
unconditionally returns `true` regardless of `webgpu_sffi_is_available()`/`create_surface`
(backend_webgpu.spl:227-252) — fix so it returns `false` on a failed probe; `name()` always reports
`"webgpu"` — add a DirectX-style honest fallback name when falling back to CPU; `probe_backend()`'s
webgpu branch (engine.spl:382-387) checks only `init()`, never `gpu_ready` — require `gpu_ready`
before reporting `Initialized`; `read_pixels_with_source()` always returns the CPU buffer tagged
`"cpu_mirror"` (backend_webgpu.spl:531-532) even after a real GPU dispatch — either add a real
GPU→CPU sync/download path, or keep `readback_source` honestly `"cpu_mirror"` and don't claim
`gpu-readback` (do not fabricate a download path just to pass the honesty gate). **Delist or
register vaporware:** Intel (`rt_oneapi_*`) and OpenGL (`rt_opengl_*`) have zero extern registration
in `compiler_rust` — any call hard-errors via `common::unknown_function` instead of degrading
gracefully. Either register real FFI (out of scope here) or remove them from
`backend_default_priority_order()`/`renderer_priority_order()` (helpers_availability.spl:104-136) so
auto-detect never reaches them; while touching this file, also fix OpenGL's unchecked
`opengl_read_pixels()` boolean return in `read_pixels_with_source()` (backend_opengl.spl:234-243).
**Quarantine orphaned fabricated-FFI files:** `backend_accel_{cuda,metal,vulkan}.spl`,
`backend_cuda_proof.spl`, `backend_webgpu_proof(.spl/_runtime_ops.spl)` do not implement
`RenderBackend`, declare `extern fn` symbols that mostly don't exist in the Rust runtime (and where
one does, has a mismatched signature), and have zero wiring into selection or the executor —
**delete or quarantine them**, the same precedent as the earlier `backend_metal_proof` deletions.
Do **not** rename them to honest `*-accel` names and keep them — they are not real accelerated
backends, just fabricated demonstrations with no working FFI behind them.

**Files:** `backend_cpu.spl`, `backend_directx.spl`, `backend_software.spl` (declare
`class_="software-reference"`), `backend_webgpu.spl` (honesty fix), `engine.spl` (webgpu probe
`gpu_ready` check), `helpers_availability.spl` (Intel/OpenGL priority-order delist, unless
registering real externs), `backend_opengl.spl` (unchecked-return fix), `backend_accel_cuda.spl`,
`backend_accel_metal.spl`, `backend_accel_vulkan.spl`, `backend_cuda_proof.spl`,
`backend_webgpu_proof.spl`, `backend_webgpu_proof_runtime_ops.spl` (delete/quarantine, not
rename-and-keep).

**Gate:** parity-vs-oracle still exact; **honesty spec** `backend_honesty_spec.spl` asserts every
backend whose device is absent has an emulation-disclosing `name` and `readback_source != "gpu-*"` —
including WebGPU, which must now honestly fail this assertion instead of always reporting
`"webgpu"`/`Initialized`; a vaporware spec asserts Intel/OpenGL are either functional or absent from
`backend_default_priority_order()`; a cleanup check asserts the orphaned accel/proof files are gone
(or moved to a clearly-marked quarantine location) and the self-duplicating specs that inline-copy
them are removed too.

**Risks:** removing local raster bodies from cuda/metal is **deferred to P4** (they have real
kernels); P2 only touches pure CPU-delegate paths plus the honesty/vaporware/orphan cleanup above.
No perf regression expected (same software path, one algorithm). WebGPU's honest failure may drop it
out of `detect_best_backend()` entirely on hosts without a real adapter — that is the intended,
correct behavior change (today's dishonest always-true `init()` is the bug being fixed).

---

## P3 — SIMD-CPU accelerated spans behind the shared interface

**Do:** today `"cpu_simd"` is a **bare alias** for `"cpu"` — `engine.spl:271-279` instantiates the
byte-identical `CpuBackend.create()` for both, differing only in the `selected_backend_name`
string. This phase is **"wire the existing real kernels", not "write new SIMD kernels."** Genuine
NEON/AVX2 kernels already exist (`nogc_sync_mut/gpu/engine2d/simd_kernels.spl:333-378`, real
`extern`-backed C intrinsics; `rt_engine2d_simd_*`) but are never called from
`backend_software.spl`/`backend_cpu.spl` — wire them into the hot path: route `draw_rect_filled`
span fill, `draw_image` copy, and alpha blend through these real kernels (not just
`simd_provider`'s detection layer), scalar fallback otherwise. **Fix the NEON-only gate:** the
current dispatch is effectively NEON-oriented in practice — ensure x86 AVX2 hosts engage a real
vector kernel instead of silently falling through to scalar. Select as `cpu-simd`
(`SIMPLE_2D_BACKEND=cpu_simd` already recognized); declare `accelerated_ops=[fill,copy,alpha]`.
Higher-level ops stay in `SharedRaster` unchanged.

**Files:** `backend_software.spl`, `backend_cpu.spl`, `simd_kernels.spl` (wire into the hot path,
not just the separate `cpu_simd_session.spl` API), `simd_provider.spl` (4 variants), `engine.spl`
(fix `"cpu_simd"` so it is no longer a bare `CpuBackend.create()` alias; selection),
`backend_capability.spl` (cpu-simd descriptor).

**Gate:** `cpu-simd` output **bit-exact** to `SharedRaster` scalar (SIMD must not change pixels,
only speed); micro-bench shows span-fill speedup on at least one ISA, **both arm NEON and x86
AVX2** (not NEON-only); proof of execution must observe the **real vector kernel actually
running** (e.g. an instrumented call-count or a distinguishing return value on the
`simd_kernels.spl`/`rt_engine2d_simd_*` entry points). **`record_simd_*_hit` counters are
explicitly discredited as proof** — they are the historical fake-evidence pattern (a counter
increments with no vectorized code behind it) and must **not** be accepted as sufficient evidence
that the SIMD path executed.

**Risks:** SIMD lanes historically scalar-with-accounting-hooks; the gate must prove the vector path
executed AND matches bit-for-bit. Do not accept an accounting counter as proof of vectorization —
this is the same trap the corrected Gate above closes.

---

## P4 — Metal/Vulkan declare accelerated-op sets, fall through to shared logic, uniform readback

**Note:** `intel`/`opengl` only need the treatment below if P2 registered their real externs; if P2
instead de-listed them from `backend_default_priority_order()` (the default), skip them here until
the FFI work lands — don't declare `accelerated_ops` for a backend that hard-errors on call. WebGPU
enters this phase already honesty-fixed by P2 (§P2); this phase adds its `accelerated_ops`
declaration and uniform readback bookkeeping on top of that fix.

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
`clear` a scene command (remove hardcoded white, engine2d_executor.spl:31). See
`doc/08_tracking/bug/engine2d_facade_dead_3way_branch_and_drawir_gaps_2026-07-06.md` for the
verified evidence on the `blur_rect` drop and the missing triangle/mask IR kinds.

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

- **P1's bit-exact harness gate (a) lands first**, before any core-op delegation switch — it is the
  safety net every later phase relies on.
- **P1, P2** are behavior-preserving — safe to land first, in order (P2 depends on P1's descriptor
  and on P1 having already resolved the `RenderBackend` naming collision).
- **P3** (SIMD) and **P4** (GPU accel-set) are independent of each other once P1 lands — can run in
  parallel by two Sonnet sessions on disjoint files (software/simd vs metal/vulkan). P4's
  intel/opengl treatment is conditional on P2's disposition of those two backends (registered vs.
  de-listed).
- **P5** (IR) is independent but should precede **P6** (web fold-in needs the extended IR).
- **Stub-cleanup phase (deferred, unscheduled, blocked on FR-RENDER-MIXIN):** once FR-RENDER-MIXIN
  wires `src/app/desugar` into the compiler front-end (preserving return-type annotations) and an
  end-to-end zero-hand-written-stub test passes, replace the ~191 hand-written forwarding stubs
  established in P1 with auto-forwarded mixin methods. This phase does not exist yet and is
  explicitly not part of P1-P6.
- Every phase leaves the tree green and the oracle gate passing; no phase requires a bootstrap
  rebuild (pure-Simple stdlib edits) — deploy via the self-hosted binary per repo default.

## Filed bugs / feature requests to reference in commits
- **FR-RENDER-MIXIN** — auto-forwarding of non-accelerated trait methods (kills ~191 stubs,
  corrected count, not ~300). **Confirmed infeasible with the shipped compiler today** (two
  independent checks: the offline `src/app/desugar` five-pass rewrite is reachable only via the
  `bin/simple desugar` CLI subcommand, not wired into the build pipeline's `desugarer:` port, which
  stays `_noop_desugar`). Needs compiler-front-end wiring + preserving return-type annotations the
  offline pass currently drops. Filed as a **prerequisite for the deferred, unscheduled
  stub-cleanup phase** — not part of P1.
- **engine2d drift** — CPU↔GPU line/circle bit divergence (MEMORY 06-03). Lock reference in P1 spec. (P4)
- **metal readback fallback** — silent software fallback reporting as GPU (MEMORY 06-10). Gate via
  `readback_source`. (P4)
- **JIT-render crash** — winit/graphics apps panic under JIT; use interpret mode. (P6)
- **`webgpu_backend_dishonest_always_initialized_cpu_mirror_2026-07-06`** — WebGPU `init()` always
  true, readback always `cpu_mirror`; same class as the fixed DirectX bug. (P2)
- **`engine2d_vaporware_backends_intel_opengl_unregistered_externs_2026-07-06`** — Intel/OpenGL
  hard-error on unregistered externs; OpenGL unchecked readback return. (P2, P4)
- **`cpu_simd_backend_is_bare_alias_no_real_simd_2026-07-06`** — `cpu_simd` is a bare `cpu` alias;
  real NEON/AVX2 kernels exist but are unwired. (P3)
- **`engine2d_orphaned_fake_accel_and_proof_files_2026-07-06`** — fabricated-FFI accel/proof files,
  zero wiring, mismatched extern signatures. (P2)
- **`engine2d_rendbackend_naming_collision_and_dead_traits_2026-07-06`** — two same-named
  `RenderBackend` traits; `ComputeSession`/`RenderBackendCore`/`RenderBackendAdv`/nogc_async_mut
  copy all dead. (P1)
- **`engine2d_facade_dead_3way_branch_and_drawir_gaps_2026-07-06`** — dead 3-way facade branch;
  `scene_blur_rect` dropped by executor; dual disagreeing backend-selection paths. (P1, P5)

## Honesty — exists / to-build / deferred
**Exists:** IR, executor, flat trait, `backend_emu` reference (28 ops: 23 in `backend_emu.spl` + 5
in `backend_emu_adv.spl`, corrected), `backend_software` SIMD hooks, directx honest naming, metal
`gpu_frame_complete`, readback source channel, cpu_simd key.
**To build (this plan):** bit-exact harness gate + SharedRaster consolidation (forwarding stays
hand-written; mixin deferred) + naming-collision fix + dead-interface/dead-branch/dual-selection-path
cleanup (P1); honest capability descriptors + dedup + WebGPU honesty fix + Intel/OpenGL vaporware
delist-or-register + orphaned accel/proof file cleanup (P2); real SIMD spans wiring the existing
unwired kernels with genuine execution proof (P3); GPU accel-sets + uniform readback (P4); IR
completeness (P5); web fold-in (P6).
**Deferred:** FR-RENDER-MIXIN — confirmed infeasible with today's compiler (not merely "if mixins
insufficient") — and its dependent, unscheduled stub-cleanup phase; bit-exact GPU AA for
transform/glyph-run (fall through to reference until achievable).
