# Simple WM/GUI/Web/2D Rendering Performance — Diagnosis (2026-08-06)

Status: research, claim-verified against this repo on 2026-08-06.
Companion plan: `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`.

Every measured number below came from the **Rust bootstrap seed** binary
(`bin/simple`, md5 `ed53cc5f255e269ca27c4cd83b17aef9`) unless the cited source
says otherwise. No number in this document is a self-hosted AOT measurement.

## Executive verdict

Multi-second render times are NOT primarily caused by insufficient SIMD width
or missing Vulkan. The dominant costs are earlier in the pipeline:

1. Pixel/style work runs through interpreted or seed-runtime paths with boxed
   values and repeated dynamic dispatch.
2. The "native SIMD" row path performs allocation, gather, FFI, and scatter
   around the vector kernel; it can be slower than scalar and has corrupted
   pixel values.
3. The packed-scene native writer does not write directly into the arena — it
   builds growable local arrays and copies rows in, because interpreter
   class-field reference semantics are value-copy.
4. Showcase paths clear + repaint the full framebuffer, read it back,
   downsample/encode, write PPM, and route through the WM.
5. Web style application probes hundreds of property names per node instead of
   iterating only the declarations that exist.
6. Forwarding is generated source wrappers, so zero-logic architectural layers
   remain real call boundaries.

Correct optimization order:

> Direct packed memory → retained incremental scene → zero-copy forwarding →
> common optimization → scalar reference → per-operation SIMD → GPU backends.

Starting with more AVX/RVV/Vulkan/Metal kernels would accelerate only the
smallest part of the current path.

## Claim verification ledger

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| 1 | 8K full-fixture: scalar software 909.530 ms, CPU-SIMD 1282.166 ms (SIMD *slower*) | **VERIFIED** | `doc/07_guide/platform/gui_perf_benchmark_comparison.md:53-54` — checksum + `nonzero_pixels:33177600` proof on both rows |
| 2 | 1080p fill: C scalar 4.5 ms vs Simple scalar 141 ms (~31x) | **VERIFIED** | same guide, line 78 (`fill_1080p | 4.5 ms | 141 ms`) |
| 3 | Retained Node/Cairo headless 8K baseline ≈17.3 ms | **VERIFIED** | same guide, line 14 (Node.js Canvas row) |
| 4 | Native scene writer copies rows because interpreter class-field assignment is a value copy | **VERIFIED** | `src/lib/nogc_sync_mut/ui/draw_ir_v3_native_writer.spl:14-19` ("ARCHITECTURE NOTE (verified interpreter limitation)… a private copy the caller's own `arena` variable never sees"), also :512-522 |
| 5 | Scalar fill 0–1 ms vs nominal native-row fill 8 ms; blend 27 vs 64 ms; SIMD colour corruption | **VERIFIED** | `doc/08_tracking/bug/engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md:21,61` |
| 6 | Persistent Engine2D vs create/shutdown = 176x–684x | **VERIFIED** | `doc/03_plan/ui/perf/gui_web_2d_perf_fix_plan.md:16` (landed `a7b57550`); `doc/01_research/ui/rendering/cpu_gpu_dual_algorithm_research.md:224` |
| 7 | Web style probing is wide (per-node probe of large property vocabulary) | **VERIFIED in kind** | `simple_web_html_layout_renderer_decl_apply.spl` carries ~502 quoted property-name literals; interpreted showcase HTML renders cost "minutes"/"tens of minutes" (`src/app/wm_showcase/session.spl:79,167`) |
| 7a | Exact figures "283 property probes", "176-field Style", "4 s per node" | **UNVERIFIED** | no repo source found stating these exact numbers; do not cite them — use claim 7's verified form |
| 7b | "4K showcase comments report interpreted execution exceeding 300 seconds" | **UNVERIFIED as stated** | repo says "minutes at 4K" / "tens of minutes interpreted" (`session.spl:79,167`) — same direction, different wording |
| 8 | Route contract distinguishes `cpu_selected` (policy chose CPU) from `gpu_fallback` (GPU denied) | **VERIFIED** | `src/lib/common/ui/draw_ir_v3_execution_route.spl:7-18` |
| 9 | Unified packed-scene lanes (DrawIR-v3 arena, L0–L9) already landed; one physical arena, no separate GUI/Web display-list formats | **VERIFIED** | commits `1e0a4c18b0b` (L6 GUI), `721bc3f579b` (L7 Web), `ed086bb06d4` (L8), `dcd08e77f22` (L9), `dfd465a7125`, `b11002b7eeb`; feature expert `doc/00_llm_process/feature_expert/unified_packed_ui_scene/skill.md` |
| 10 | SIMD level is one global cached enum; `Avx512` reports `avx2` as its feature text | **VERIFIED** | `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:66` (`case Avx512: "avx2"`); level selection at :130,:297 |

Claims 1–3 together are the diagnosis in one line: on the same host, a
retained Cairo baseline does the 8K fixture in ~17 ms while Simple's full-size
paths are near one second, and Simple's *scalar* is 31x slower than C scalar
at 1080p — a representation/compiler/runtime-bound problem, not a
vector-width problem. Claim 1 additionally shows the current SIMD path is a
net *pessimization* (gather/box/FFI/scatter around the kernel, claim 5).

## 8K @ 80 FPS reality check

- 7680×4320 = 33,177,600 px; at 80 FPS = 2.65 Gpx/s; one u32 write/px =
  10.6 GB/s; src-over blend (read src+dst, write dst) ≥ 31.9 GB/s.
  Frame budget 12.5 ms; one framebuffer = 132.7 MB.
- Full-screen 8K80 complex software rerasterization is not a realistic
  small-SBC target. 8K80 *presentation* is realistic when the scene is
  retained and only damaged regions (0.1–2% typical for cursor/caret/text)
  are rerasterized; full-screen blur/scale/video belongs on the GPU;
  unchanged frames must do zero style/layout/raster/upload/readback work.
- Target restated: **8K80 presentation with damage-proportional CPU work**,
  not unconditional 8K80 CPU rasterization.

## Ranked bottlenecks

| Pri | Bottleneck | Evidence | Correction |
|---|---|---|---|
| P0 | Execution-path identity — "native" measurements are seed/JIT/interpreter-backed | claims 2, 7b; standing memory: seed delegation, engine divergence | Every perf receipt names engine, triple, ISA, fallback status; perf gates fail closed on wrong engine |
| P0 | Boxed pixel ABI — gather boxed elements → native buffer → kernel → scatter | claims 1, 5 | Packed `Span`/`MutSpan`; resolve backing object to one raw pointer at the boundary |
| P0 | Scene-writer copies — growable temp columns copied into arena | claim 4 | Fix class-field reference semantics across engines, then direct indexed column writer |
| P1 | Full redraw + readback + PPM present path | showcase code, WS-B/WS-D plans | Retained scene, damage, persistent surfaces, no normal-frame readback |
| P1 | Per-frame/session construction | claim 6 (176x–684x) | One persistent RenderSession per surface (largely landed `a7b57550`; keep as gate) |
| P1 | Web style wide-probe application | claim 7 | Numeric PropertyId, typed values, hot/cold style split, O(k)-declarations apply |
| P2 | Text and filters — interpreted blur, per-character overhead | prior profiling reports | Separable filters, glyph atlas, shaped-run cache, packed glyph batches |
| P2 | Source-level forwarding wrappers | forwarding desugar in frontend | Typed forwarding metadata in HIR/MIR, erased after weaving (see plan §C) |
| P2 | One global SIMD level | claim 10 | Per-operation/format/alignment/size-bucket kernel table, promotion by measurement |
| P3 | Allocating event conversion per layer | input ring already fixed-slot | POD packet + zero-copy views + batched drain (largely built in WS-C; keep as gate) |

## What already exists (do not rebuild)

- One physical DrawIR-v3 packed arena with producer leases, generations,
  owner/event tables, hit shapes (claim 9). The plan is additive V2 repair —
  **not** another scene architecture, and explicitly not a GuiIR/WebIR
  (rejected decision on record).
- Execution-route receipts with `cpu_selected` vs `gpu_fallback` (claim 8).
- Persistent Engine2D sessions (claim 6).
- Fixed-capacity input ring over `HostInputEvent`
  (`src/os/drivers/input/input_event.spl`), compositor damage mechanism
  (`backend_software.spl` — currently with **zero consumers**, see
  `doc/03_plan/os/simpleos/screens/ws_d3_damage_present_investigation.md` §9).

## Known measurement traps for any follow-up benchmarking

- `SIMPLE_EXECUTION_MODE=native` is not a mode; everything but `interpret` is
  JIT under the seed.
- `bin/simple` is the Rust seed; `simple test` can silently delegate to a seed
  child. Identity must be probed positively (capability probe), not inferred
  from banner or size.
- 60 s monitor cap kills long runs with exit 255 and no verdict line;
  measurement requires a pinned worktree.
