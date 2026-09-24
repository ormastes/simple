# Simple 2D/WebRenderer GPU objective audit

Date: 2026-09-09
Scope: canonical Chrome primitive prerequisite, Simple 2D/WebRenderer GPU
residency and offload, async/event correctness, fair Vulkan/web comparisons,
Astra/Sol planning, and SPipe UI-optimization knowledge. One bounded canonical
Chrome-oracle builder admission attempt was run; no benchmark or runtime test
was rerun.

## Verdict

**STATUS: INCOMPLETE — no release, device-execution, or performance-comparison
admission.**

The top-level GPU feature/NFR choice, production surface owner (O1), and
compatible async runtime pair (B+N2) are selected. Source contracts and focused
static/bootstrap-diagnostic evidence exist, but no current general admitted
pure-Simple CLI/runtime can supply the required runtime or SPipe evidence.

The canonical Chrome library is not built. Neither worktree contains a
`stage2-admitted` tree or passing Stage-2 parent sanity/provenance receipts. The
latest isolated candidate failed frontend sanity at the K1 composition policy.
The K1 content-order repair is present in the isolated source but has not been
retried canonically. The C Vulkan row is `measured-unadmitted`; the Simple row
is `skipped:bootstrap-seed-forbidden`; therefore no ratio is valid.

## Canonical Chrome builder attempt (2026-09-09)

The single permitted initial build/admission attempt was:

```text
sh scripts/check/build-chromium-primitive-oracle.shs
```

It failed closed before invoking a compiler (`exit_code=1`):

```text
chromium-oracle-builder: REJECTED — bootstrap-output-not-canonical
```

The clean PR worktree has no physical `build/bootstrap` directory and no
`stage2-admitted` compiler/parent receipts. No output dylib or receipt was
created. The existing builder remains the authoritative path and correctly
rejects substitution with `bin/simple`, a Rust seed, or a fabricated receipt
graph. This lane must not rerun the builder until an independently produced,
source-matched admitted Stage-2 compiler and all authority receipts physically
exist; creating that authority is a separate scoped compiler task, not this
lane.

Chrome comparison admission remains incomplete unless all of the following are
present: pinned Electron `42.5.0` and Chrome `148.0.7778.271` identities with
broker and npm-lock hashes; the same versioned fixture/workload, viewport,
timing scope, warmups, and sample counts on both sides; a proven hardware GPU
backend/renderer identity with SwiftShader, software, fallback, and unknown
states rejected; CPU `capturePage` pixels explicitly retained as
`device_origin_readback=false`; frame-bound artifact/readback/checksum hashes;
raw samples producing p50/p95 frame times and max RSS; and all four canonical
fixtures. Otherwise the result is WARN/INCOMPLETE, never PASS. A dylib build
alone cannot satisfy GPU or performance-comparison admission.

## Requirement evidence

| Requirement | Evidence | Classification |
|---|---|---|
| Chrome library first (REQ-GPUUI-001; REQ/NFR-CHROME) | Root `doc/02_requirements/feature/chromium_web_renderer_primitive_differential.md`, `doc/02_requirements/nfr/chromium_web_renderer_primitive_differential.md`, `tools/chromium-primitive-oracle/chromium_primitive_oracle.spl`, and `doc/01_research/local/chromium_web_renderer_primitive_differential.md`; isolated `scripts/check/build-chromium-primitive-oracle.shs`, `test/01_unit/scripts/chromium_primitive_oracle_builder_contract_test.shs`, and `doc/08_tracking/bug/chromium_oracle_canonical_admission_plan_2026-09-08.md` | **INCOMPLETE**. Root and isolated oracle sources both hash to `ec27253f996886e6f490503d6daf9a2166f2622791714a012b537b2f143c3a31`. The retained arm64 dylib has exactly five ABI symbols but was built by a Rust bootstrap seed and is diagnostic-only. The isolated fail-closed producer and its contract source are prepared, but canonical preflight cannot pass without a `stage2-admitted` compiler and parent receipts. No canonical library receipt, native load/run/release/broker receipt, Chrome init/normalization timing, RSS, or exact-once release evidence exists. |
| GPU offload, retained buffers, and device consumption (REQ-GPUUI-003/006) | `src/lib/gc_async_mut/gpu/engine2d/vulkan_resident_2d.spl`, `backend_vulkan.spl`, `backend_vulkan_spirv.spl`; `src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs`; `doc/08_tracking/todo/web_gpu_offload_buffer_residency_gap_matrix_2026-09-09.md` | **PARTIAL, UNADMITTED**. Retained buffer/descriptor and shader-consumption paths exist. Available shader/object checks are static or bootstrap-diagnostic; no admitted physical-device receipt proves production browser device consumption, per-surface ownership, or deterministic device-loss teardown. |
| Production surface and presenter owner (REQ-GPUUI-002–005) | `doc/02_requirements/feature/browser_renderer_gpu_surface_owner.md`; `doc/04_architecture/browser_renderer_gpu_surface_owner.md`; `src/os/compositor/{host_compositor_core,compositor_engine2d}.spl`; `src/lib/gc_async_mut/gpu/engine2d/{engine,backend_vulkan,backend_vulkan_helpers}.spl` | **SELECTED / UNINTEGRATED**. O1 assigns ownership to the long-lived compositor; BrowserSession remains a producer. `GpuRenderSurfaceState` has no production caller, while the current Vulkan present path flushes through synchronous `submit_and_wait_fence`; no presenter read-lease/release receipt exists. |
| Zero ordinary readback and fewer CPU↔GPU crossings (REQ-GPUUI-002; NFR-GPUUI-004) | `src/lib/gc_async_mut/gpu/session/render_surface_state.spl`; `doc/02_requirements/nfr/engine2d_vulkan_2d_perf.md`; `doc/08_tracking/todo/web_gpu_offload_buffer_residency_gap_matrix_2026-09-09.md` | **PARTIAL, MODEL-ONLY FOR NEW LIFECYCLE**. The portable state contract separates zero-readback presentation from explicit capture and generation-bound provider receipts. Production still has synchronous fence/present behavior and documented host-copy/full-pixel API paths. No current admitted runtime receipt proves zero timed readback/upload/allocation. |
| Async ring and fence/timeline correctness (REQ-GPUUI-004; NFR-GPUUI-005) | `doc/02_requirements/feature/vulkan_async_compute_submission_ring.md`; `doc/02_requirements/nfr/vulkan_async_compute_submission_ring.md`; `doc/03_plan/sys_test/vulkan_async_compute_submission_ring.md`; `doc/05_design/runtime/vulkan_async_compute_submission_ring.md`; `doc/08_tracking/bug/vulkan_no_wait_pending_submission_blocks_followup_compute_2026-09-09.md` | **SELECTED / UNIMPLEMENTED**. B+N2 is selected, but Simple submission still waits. No-wait work stays quarantined, and public fence destruction cannot retire its native owners or safely recycle a slot. No admitted positive ring exists. The C three-slot ring is diagnostic evidence only. |
| Event ordering, admission, and stale-work rejection (REQ-GPUUI-005/008) | `src/lib/gc_async_mut/gpu/session/{render_surface_event_damage,render_surface_state}.spl`; `test/01_unit/lib/gc_async_mut/gpu/session/render_surface_event_damage_spec.spl`; `test/03_system/app/ui.browser/feature/simple_2d_web_renderer_gpu_optimization_spec.spl`; GPU gap matrix | **SOURCE CONTRACT PRESENT; PRODUCTION/RUNTIME OPEN**. Generation binding, damage freeze/coalescing, stale rejection, capture generation, and teardown are represented in source/tests. The state owner and `gpu_event_normalize` have no production caller, no synchronized manifest-bound ingress owner exists, and no admitted compositor/device run proves the workflow. Historical seed runs are not release evidence. |
| Hot-path compaction, device-native primitives, pixel/public-API/fallback preservation (REQ-GPUUI-006/008) | `src/lib/gc_async_mut/gpu/browser_engine/{simple_web_html_layout_renderer,simple_web_html_layout_renderer_paint_layout,simple_web_layout_engine2d_fast}.spl`; focused clip-cache, image-index, and engine-reuse specs; GPU gap matrix | **PARTIAL, STATIC**. Reviewed changes remove duplicate clip-cache construction and linear image scans and add exact guarded reuse. The production HTML entry still rebuilds DrawIR and cannot hit the reuse cache. Device-native hot-primitive coverage, exact production pixel parity, and fallback/public-interface preservation lack admitted runtime/device evidence. |
| C Vulkan vs Simple Vulkan showcase (REQ-GPUUI-007; NFR-GPUUI-002) | `scripts/check/check-vulkan-2d-c-compare.shs`; `scripts/check/lib/perf-comparison-admission.shs`; `build/vulkan-2d-c-compare/{c.env,simple.env,evidence.env}`; `doc/09_report/perf_comparison_admission_2026-09-09.md` | **NOT ADMITTED**. Current evidence says C `measured-unadmitted`, Simple `skipped:bootstrap-seed-forbidden`, comparison `skipped`, ratio `0`. The gate correctly refuses unequal/stale/seed evidence, but gate correctness is not renderer performance evidence. |
| Simple Web vs Chrome rendering (REQ-GPUUI-001/007; NFR-GPUUI-003) | `doc/01_research/local/chromium_web_renderer_primitive_differential.md`; `doc/05_design/chromium_web_renderer_primitive_differential.md`; `test/02_integration/rendering/chromium_reference_oracle_native_integration.spl`; `scripts/check/check-chrome-simple-web-comparison.shs`; `doc/09_report/{perf_comparison_admission_2026-09-09,production_gui_web_renderer_parity_evidence_2026-06-23}.md` | **INCOMPLETE**. Pinned browser DOM/style/layout/paint/input evidence is semantic/CPU-capture evidence and explicitly not GPU promotion. The canonical native oracle, matching device-origin receipts, and comparable measurements are absent; historical production parity failed. |
| Quantitative latency, memory, and evidence targets (NFR-GPUUI-001/006/007) | `doc/02_requirements/nfr/simple_2d_web_renderer_gpu_optimization.md`; `doc/02_requirements/nfr/engine2d_vulkan_2d_perf.md`; GPU gap matrix | **INCOMPLETE**. No admitted warm 4K p95 ≤12.5 ms row, stable retained-allocation/RSS bound, teardown return, or complete device receipt exists. Diagnostic C counters cannot satisfy the Simple or cross-renderer NFRs. |
| Astra analysis/solution/plan | Surface-owner architecture/options; GPU gap matrix; isolated Stage-2 diagnosis and Chrome admission plan | **ANALYSIS COMPLETE; IMPLEMENTATION OPEN**. Astra located the real owner and the linker, MIR, VHDL, selector, and K1 blockers and reviewed fail-closed plans. This does not establish compiler admission, production ownership, async retirement, or device performance. |
| Existing documentation checked | Selected feature/NFR requirements, pending option documents, architecture/design, plans/spec sources, tracking, and reports referenced here | **PARTIAL**. The selected and pending choices are now distinguished, but generated documentation is stale. `doc/06_spec/03_system/app/ui.browser/feature/simple_2d_web_renderer_gpu_optimization_spec.md` predates changed surface/event wording, and `doc/06_spec/02_integration/app/llm_process/knowledge_routing_process_spec.md` lacks the new routing steps. Neither manual is admissible freshness evidence. |
| SPipe UI-optimization knowledge | `doc/00_llm_process/knowledge_registry.sdn`; `doc/00_llm_process/feature_group/rendering_ui/skill.md`; `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md`; `.spipe/simple_2d_web_renderer_gpu_optimization/knowledge_selection.sdn`; `test/02_integration/app/llm_process/knowledge_routing_process_spec.spl`; docgen blocker | **SOURCE UPDATED; GENERATED/RUNTIME EVIDENCE OPEN**. Exact-feature and longest-prefix renderer routes plus GPU residency, crossing, async, event, and comparison rules are present. No admitted CLI run proves the changed routing spec. `doc/08_tracking/bug/spipe_docgen_deployed_macos_cli_stale_2026-09-09.md` proves the April CLI cannot regenerate the knowledge manual; direct comparison also shows the GPU system manual is stale relative to its executable source. |

## Stage-2 and Chrome critical path

The latest retained canonical Stage-2 attempt is isolated
`build/stage2-resume.MbhTTc`. It linked all Stage-2 inputs but its
`stage2-sanity.env` is an explicit **failure** record: bootstrap-0 frontend
status 1 at `PLUG-E-K1-POLICY`, bootstrap-1 not run, rejected candidate SHA-256
`0573f188f532ad04cc1fa09c606beadac492f518e386d23d31076855561bc720`.
It is not a passing parent sanity receipt. No admission/provenance receipt or
`stage2-admitted` directory was published.

The isolated `static_backend_registry.spl` now compares backend names by
character content in both validation and selection. Its 49-pair projection and
object disassembly are Rust-bootstrap diagnostic evidence only. The permanent
22-check whole-registry fixture did not build or execute, and no canonical
Stage-2 retry has used the K1 repair. Earlier SIGSEGV, selector, MIR-owner,
linker, and VHDL repairs likewise remain source/focused-diagnostic evidence
until the ordinary sanity and admission chain passes.

Required order:

1. Run one bounded, source-matched canonical Stage-2 retry in the isolated
   worktree. Require both frontend modes, positional hello-world link/run, exact
   admission, parent sanity/provenance, and Stage-3 authority-map evidence.
2. Only then run the isolated Chrome builder. Require the exact five-symbol
   artifact/manifest hashes and the separate native ABI load/run/release plus
   pinned broker evidence. Stage-2 authority is accepted only for this scoped
   compiler operation, not as general renderer, SPipe, release, or Stage-4
   evidence.
3. Supply a current general admitted pure-Simple CLI/runtime for the root
   renderer and docgen lanes. The stale April CLI, rejected candidates, and an
   admitted Stage-2 receipt cannot substitute for that authority.
4. Implement the selected O1 surface/presenter owner and B+N2 runtime
   retirement ring, plus the manifest-bound production event ingress; do not
   reinterpret selection as implementation evidence.
5. Implement the real surface/presenter owner, runtime retirement ring, and
   manifest-bound production event ingress; then run admitted device,
   RenderDoc/readback, lifecycle, and pixel-parity gates.
6. Run only matched C/Simple and Chrome/Simple rows through the fail-closed
   common admission gate.
7. Regenerate both affected SPipe manuals with the current admitted CLI and
   require complete, zero-stub output and source-current scenario text.

## Safe bounded next action

The next engineering action is one source-matched canonical Stage-2 admission
attempt after the isolated worktree owner confirms the reviewed dirty source
set. Do not replace it with a seed build, diagnostic dylib, comparator rerun,
general-runtime claim, or assumed owner/async selection.
