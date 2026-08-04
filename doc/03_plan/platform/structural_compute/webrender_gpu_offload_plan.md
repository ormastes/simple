# WebRender GPU Offload Plan (remaining WebScene lanes)

**Date:** 2026-07-31 · **Status:** Proposed
**Parent:** `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` — this
plan indexes its remaining work groups; that document stays authoritative for
contracts, ownership and gates. Parser/style/layout/link/placement halves are
covered by the sibling lane plans in this directory.

## Scope

Everything in the GPU WebScene lane not owned by a sibling plan:

| Group | Content |
|---|---|
| W1 | `@gpu_event` GPU-safe Simple script compiler (HIR effect/bound analysis → GpuEventIR → ProcessingIR → CPU oracle + SPIR-V/CUDA/MSL/DXIL/SIMD) |
| W2 | GPU event core: input ring, coalescing, hit query, capture/target/bubble, deterministic mutation journal, host-effect ring |
| W6A/W6B | GPU image codecs (WebP/PNG staged decoders, libwebp oracle) and video surfaces (Vulkan Video VP9/AV1, zero-copy YUV) |
| W7/W8* | WebScene scheduler + platform adapters (Vulkan/Metal/DX/CUDA/WebGPU tiers 0–2) |
| W9 | Host services + SimpleOS bridge (effect services, IVSHMEM, fault restart) |
| W10/W11 | Web integration (feature flags, shadow → candidate → promotion) + evidence |
| I1–I12 | DrawIR v3 program: contract, capacity/no-realloc pools, typed tables, diff/patch, CPU oracle sinks, count/scan/emit + Prepared2D, hit index, cache, v2/v3 adapters, execution backends, Engine2D integration, evidence |

## Structural-compute bindings (normative)

- WebScene device pools = Object VM arenas (gpu_mmu lane contracts); no
  private placement layer.
- Mutation journal commit = MutationIR snapshot semantics; scene generation is
  a `SnapshotId`.
- DrawIR v3 `SourceProvenanceTable` = MappingGraph edges (`PaintOf`,
  `HitRegionOf`).
- Invalidation frontiers = DirtyMask + selector-feature model shared with the
  html_css_parser lane.
- DrawIR v3 is a packed encoding of the one shared display list
  (`DrawIrComposition` — DrawIR v2); it is not a second display-list format.
  The WebIR rejection stands: `doc/03_plan/ui/webir_drawir_optimization.md`
  §Decision. Table/pool implementations follow ADR-004 write-back semantics
  (`doc/04_architecture/adr/ADR-004-indexed-access-value-semantics.md`).

## Variable execution config

The web renderer supports the full offload spectrum as **configuration**, per
the shared rule (README "Variable execution configuration"):

```text
cpu only       flags off — current CPU path, byte-identical (W10 gate)
compatibility  L0–L3 accepted and reported; L4 = full CPU document render
balanced       shadow/candidate — CPU authoritative or GPU with CPU recovery
full offload   strict GPU profile — L0/L1 only; any L2–L5 fails the test
```

Mode selection is per session via feature flags + `ExecutionProfile`; no
rebuild, no silent downgrade (`cpu_selected` by cost policy ≠ `gpu_fallback`).

## Ownership and ordering

Owned paths, feature flags, waves (WAVE 0–5), dependency graph, and acceptance
gates are defined in the parent plan §10–§14 and are not duplicated here.
Ownership ledger: `doc/03_plan/agent_tasks/gpu_web_scene/ownership.sdn`.

Implementation ordering (parent §15): DrawIR v3 foundation (I1–I3) and the
`@gpu_event` compiler + event transaction model (W1/W2) first; full GPU
DOM/style/layout/media stages connect only after the first vertical slice
(panel/button/flex/custom-property fixture on Vulkan) passes its proofs:

```text
no allocator call after startup · no pixel readback · no per-widget submission
CPU oracle state/layout/IR/pixel parity · clean device-loss recovery
flag-off byte-identical to current behavior
```

## Compile-time offloadability check

Staged per `doc/01_research/ui/rendering/gpu_runnable_compile_time_verification.md` §D4:

- **Now (zero compiler changes):** transitive scanner
  `src/app/gpu_lint/gpu_runnable_scan.spl` (`bin/simple run` it) inventories
  engine2d + browser_engine roots against the ban list, with the
  any-def-blocked overload-taint rule. **Inventory mode first** — warnings and
  a ratchet on blocked/tainted counts, not build errors.
- **Later (W1 lane):** `@gpu_runnable` semantic pass in `35.semantics` wiring
  `gpu_checker` + the `alloc_inference` fixpoint; only that pass meets the W1
  acceptance bar that every rejection names the exact unsupported construct
  and call chain. The scanner stays as the out-of-band cross-check.
  Process notes: `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md`.

## Test evidence (2026-08-02)

All seven GPU-offload spec lanes are landed and green (re-verified 2026-08-02
on the interpreter-backed `bin/simple test` lane; Results lines verbatim):

| Lane | Spec | Results |
|---|---|---|
| HTML parser GPU (flat projection, CPU-oracle parity) | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl` | 24/24 |
| CSS parser GPU tables (style_block_parse + selector) | `.../css_parser_gpu_tables_spec.spl` | 47/47 |
| DOM build GPU offload | `.../dom_build_gpu_offload_spec.spl` | 38/38 |
| CSS apply + transform (decl_apply lane) | `.../css_decl_apply_transform_spec.spl` | 61/61 |
| GPU script load + animation ticks | `.../browser_script_animation_gpu_spec.spl` | 22/22 |
| 2D rendering GPU offload parity (device provenance) | `test/02_integration/rendering/web_engine2d_gpu_offload_parity_spec.spl` | 17/17 |
| Full-GPU-offload web showcase + capture verification | `test/03_system/gui/web_showcase_full_gpu_offload_spec.spl` | 13/13 |

Supporting gates: engine2d renderer unit spec 23/23, backend resolver spec
6/6 (viable-probe auto-resolution, commit `b0ef8e6aee5`), tile grid + paint
parity 21/21 (commit `f86f4c45354`). Capture evidence in the showcase lane:
deterministic checksum, mutation sensitivity, pixel probes for the pinned
palette, and honest offload provenance (device identity required for any
device-readback claim; `host_cache_after_device_present` carries identity per
the backend_vulkan provenance fix).

**Coverage.** Measured with the now-working `SIMPLE_COVERAGE=1` statement
path (test_runner epilogue injection; commit `1a6c1e362a5`). Conservative
floors on target modules: selector_matcher 97%, dom_limits 100%,
style_block_resolve 77%, style_block_parse 72%, html_tokenizer 64%,
dom_identity_index 50%, tree_builder 28%. These are FLOORS, not point
estimates: attribution requires line-hit AND enclosing-function match, and
`dom.spl` measures 1% despite the 38/38 DOM lane exercising it heavily —
direct evidence of under-attribution. The spec `@cover` targets declare 90%;
closing the measured-floor gap is tracked as a coverage-tooling defect
(`doc/08_tracking/bug/instrumented_statement_coverage_tooling_inert_2026-08-02.md`),
not by adding vacuous tests.

Defects found and filed by this campaign (all in `doc/08_tracking/bug/`):
seed runner 600s child kill (fixed `fd381db82bc`), render-session second-render
arm shadowing (fixed in `6eb19236c05`), heuristic size whitelist painting
24x16 (fixed in `6eb19236c05`), JIT nil-`.lower()` in backend auto-resolve
(open), seed `.?` bool-lowering crashing the CUDA resolve arm (worked around,
family open), coverage tooling inert (fixed) / under-attribution (open).

### Per-phase offload status (2026-08-04)

Presenter-lane audit of the browser_engine render pipeline
(tokenize → dom → style → layout → paint → tiles → present). "GPU-shaped"
means the phase computes a GPU-friendly flat/table projection verified against
the CPU oracle but has no device dispatch in the production path (zero
engine2d/`rt_gpu`/device references in the phase modules).

| Phase | Modules | Status | Probe-gated fallback |
|---|---|---|---|
| tokenize | `html_tokenizer.spl` | CPU-only; GPU-shaped flat projection (24/24 parity) | n/a — no device lane |
| dom build | `html_tree_builder.spl`, `dom.spl` | CPU-only; offload-shaped build parity (38/38) | n/a — no device lane |
| style | `style_block_parse.spl`, `style_block_resolve.spl`, `selector_matcher.spl` | CPU-only; GPU table projections (47/47) + decl apply (61/61) | n/a — no device lane |
| layout | `simple_web_html_layout_renderer*.spl` | CPU-only; emits `WebGpuPaintFrame` for the paint lane | n/a — no device lane |
| paint | `simple_web_html_engine2d_presenter.spl` (economics + gpu-first) | GPU rect-fill lane; glyph/gradient/image residual stays CPU ground truth (bit-exact by construction) | yes — backend verdict + engine2d create probe; per-frame decision string marks every decline |
| tiles | `simple_web_html_layout_renderer_paint_tiles_gpu.spl` | GPU tile lane via Engine2D Vulkan | yes — `Engine2DReadback` source + `vulkan_cpu_fallback_reason` provenance |
| present | `simple_web_html_engine2d_presenter.spl` (`_present_gpu_first`) | gpu-first default (`SIMPLE_WEB_GPU_PAINT` unset); `device_readback` + device identity for any offload claim | yes — fail-closed resolved-backend probe (vulkan/software); create-failure fallback marked `cpu-fallback` |

Remaining CPU-only phases (tokenize, dom, style, layout) have no production
device dispatch today; their GPU-shaped projections are the prepared
offload surface.

**Gate status: the present row is currently RED.** The 2D offload parity gate
regressed to `Results: 17 total, 12 passed, 5 failed` — the gpu-first default
publishes an EMPTY buffer (`expected 0 to equal 4800`) when its decline branch
mirrors an unusable GPU frame instead of re-running the CPU renderer. The
capability probe itself is sound (device creation attempt + device-derived
readback source; a real device produced
`source=device_readback:handle=1:device_identity=…` in the same session); the
defect is in the fallback's recovery. Filed as
`doc/08_tracking/bug/web_gpu_first_default_publishes_empty_frame_2026-08-04.md`.
The 17/17 row in the table above predates this regression.

## Acceptance

The parent plan's gates apply verbatim (§14): byte-matching mutation
journals, canonical serialization parity, semantic checksums, fail-closed
capacity overflow, no hidden SoftwareBackend calls, and promotion only on
measured p50/p95 event-to-present improvement including transfer +
synchronization cost.
