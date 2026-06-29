# Feature: host-gpu-runtime-queue

## Raw Request
with spipe skill, impl all the planed, check event flow and fix any problems. and check them with vulkan, metal, cuda/hip as possible as or make win, mac plan. fix them you think missing for complete and production level gui web 2d engine layers api. make small task apply to spark and verify works with normal llm. make pherallel agent plan and do works in pherallel go

## Task Type
feature

## Refined Goal
Make host/GPU lane markers and Engine2D Draw IR paths emit verifiable runtime queue packets with typed drain/readback evidence, while documenting and testing the remaining production browser-frame/backend gaps.

## Acceptance Criteria
- AC-1: Interpreted and forced-native `target.later(...) gpu` fixtures record begin/end lane counters and exactly one runtime queue packet.
- AC-2: Engine2D exposes public submit and drain result helpers that wrap `rt_host_gpu_queue_*` without direct raw-counter assertions in new SPipe specs.
- AC-3: A GPU-selected `DrawIrBatch` can flow through `DrawIrBatch -> runtime queue submit -> Engine2D render -> runtime drain` with an executable spec and generated manual.
- AC-4: Vulkan and CUDA readback evidence are rerun when available on the local host; Metal and ROCm/HIP produce typed unavailable evidence or a concrete Mac/AMD follow-up plan.
- AC-5: Documentation separates evidence adapters, runtime queue emission, backend readback fixtures, and the remaining production GUI/web browser-frame queue-drain integration.
- AC-6: Spark and normal-model reviews identify unresolved correctness/performance gaps, and those gaps are reflected in the plan/docs.
- AC-7: The feature is not considered production-complete until completed BrowserBackend Vulkan frame queue/readback evidence is separated from the remaining hard gates: queue capacity semantics must match across Rust/C runtimes, lane end accounting must be exception-safe for arbitrary runtime traps, and all-platform device readback proof must cover the requested native backends.

## Scope Exclusions
Full browser-frame HTML/widget Draw IR command parity, all-platform same-frame
device readback, and cross-host Metal/ROCm hardware validation remain open
unless implemented and verified by later SPipe phases. Focused BrowserBackend
evidence now proves Vulkan-backed real backend-handle/readback propagation and
a widget-semantic Draw IR dispatch receipt on this Linux lane, including
command-level image URI evidence and event-target context resolution; CUDA/OpenCL
remain child backend fixtures in the production wrapper.

## Phase
dev-in-progress

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
- impl: Added focused BrowserBackend runtime queue diagnostics coverage for
  GPU-selected frames and cache-hit reset. Remaining production blockers are
  real backend-handle propagation and backend submit/readback receipts.
- impl: Added runtime submit/complete phase APIs so `SUBMITTED` is observable
  before terminal completion, with Rust runtime and SPipe event-path coverage.
- impl: Split Engine2D runtime queue identity from backend-handle identity,
  changed Simple drain evidence to read `rt_host_gpu_queue_last_backend_handle()`,
  and made the production GUI/web wrapper run the BrowserBackend frame probe
  while keeping same-frame backend readback fail-closed.
- impl: Added OpenCL WebRenderArtifact queue stamping to fail closed with a
  typed unavailable/missing-backend-handle reason when local OpenCL does not
  expose a concrete device readback handle, and made the production wrapper
  report partial platform-matrix status explicitly.
- impl: Added BrowserBackend/WebRender dispatch status plumbing and tests. A
  direct hot-path HTML -> Draw IR bridge was probed and left out because it is
  too slow/sticky for the render path without a prepared/cached Draw IR plan.
- impl: Strengthened the direct WebRender pixel-backend queue spec to assert
  bounded runtime payload size/hash/text for Vulkan submits and zero/empty
  payload evidence for OpenCL missing-handle and software-neutral paths.
- impl: Wired BrowserBackend first-frame prepared-layout Draw IR dispatch
  through `engine2d_draw_ir_adv_batch_runtime_queue`, while cache hits continue
  to reset dispatch status to `not_requested`.
- impl: Extended BrowserBackend/WebRender dispatch receipts with payload
  size/hash/text evidence so the production wrapper can prove the dispatched
  packet is `simple-draw-ir-v2` instead of relying only on dispatch status.
- impl: Replaced the single synthetic prepared Draw IR frame rect and
  layout-only proxy with a bounded widget-semantic Draw IR batch. BrowserBackend
  now dispatches the frame background, widget-id rect commands, and
  `draw_ir_text` commands for the focused panel/text/button fixture.
- impl: Extended BrowserBackend queued Draw IR evidence to include an image
  command with preserved `image_uri` plus `draw_ir_event_target_context`
  resolution for `browser_queue_action:text` back to the queued GUI AST batch.
- impl: Made Engine2D Draw IR unsupported-command handling fail closed in the
  result reason. Image commands are now explicitly reported as skipped
  unsupported Draw IR commands until decoded-image rendering is implemented.
- impl: Added Pure Simple Draw IR host/GPU event-flow phase evidence.
  `host_gpu_draw_ir_event_flow.spl` now reports host-to-GPU `forward` and
  GPU-to-host `backward` completion records derived from the existing decision,
  submit, and receipt path, and `host_gpu_event_path_spec.spl` proves both the
  GPU-forwarded and host-only cases.
- impl: Added `Engine2dHostGpuPureQueueState` as an additive Pure Simple-owned
  queue lifecycle model. It mirrors emit -> submit -> complete -> drain with
  payload size/hash/text and backend-handle receipt evidence without changing
  the Rust runtime queue externs, and `host_gpu_event_queue_spec.spl` now proves
  the in-language lifecycle.
- impl: Connected BrowserBackend local input-event dispatch telemetry to the
  Engine2D host/GPU event-flow model as scheduling evidence. `record_event_dispatch`
  now records target lane, forward status, backward completion status, and summary
  text; the focused BrowserBackend queue probe proves enqueued/polled/dispatched
  event counters and rendered roundtrip status.
- system-test: Added `browser_backend_host_gpu_event_evidence_spec.spl` and wired
  it into `ui_sspec_evidence_audit_spec.spl`. The system lane now checks
  implementation fields, focused executable assertions, generated manual markers,
  and the UI manual-pair audit for BrowserBackend host/GPU event scheduling evidence.
- impl: Added resolved ARGB image-buffer support to the Engine2D advanced Draw IR
  adapter through `engine2d_draw_ir_adv_batch_with_images` and
  `engine2d_draw_ir_adv_composition_with_images`. Existing URI-only image
  commands still fail closed when unresolved or invalid; this does not claim
  PNG/JPEG/WebP decode support.
- impl: Started the no-GC default migration after the GC-side Engine2D slice by
  removing the GC-backed `std.gpu` alias, mapping `std.gpu` to the
  `nogc_async_mut` runtime family in the boundary checker, and adding
  no-GC async CPU-deterministic kernel intrinsics for `cpu_kernel_run_1d` and
  block/grid/global id helpers. Full Engine2D default migration remains open:
  `nogc_async_mut/gpu/engine2d` still lacks the 2D facade and backend rendering
  files now owned by `gc_async_mut/gpu/engine2d`.
- impl: Migrated the Engine2D Host/GPU lane scheduler, runtime event queue, and
  Draw IR event-flow adapter to no-GC canonical source files under
  `src/lib/nogc_async_mut/gpu/engine2d`. The old `gc_async_mut` paths are now
  export-only compatibility shims, and dynSMF `render2d` now compiles the
  no-GC backend-lane source rather than the shim.
- impl: Migrated pure backend identity, priority-order, feature-gate, and
  numeric packing helpers from `gc_async_mut/gpu/engine2d/helpers_availability.spl`
  to `nogc_async_mut/gpu/engine2d/helpers_availability.spl`. The GC path is now
  an export-only compatibility shim; no SFFI or runtime externs moved.
- impl: Migrated pure Engine2D backend contracts from
  `gc_async_mut/gpu/engine2d/{backend,backend_core,backend_adv}.spl` to
  `nogc_async_mut/gpu/engine2d/{backend,backend_core,backend_adv}.spl`. The old
  GC and GC-sync paths are export-only compatibility shims; concrete rendering
  backends still live under `gc_async_mut` until their no-GC migration slices.
- impl: C backend call lowering now treats MIR string-constant callees with the
  `rt_host_gpu_` prefix as direct runtime symbols instead of C string literals,
  and `src/runtime/runtime.h` declares the host/GPU lane and queue ABI used by
  generated C. `test/01_unit/compiler/backend/c_backend_host_gpu_runtime_call_spec.spl`
  pins lane-event and queue-submit codegen.
- impl: LLVM text and lib-backed runtime declaration tables now declare the
  same `rt_host_gpu_*` lane and queue ABI used by MIR host/GPU lowering.
  `test/01_unit/compiler/backend/llvm_host_gpu_runtime_declarations_spec.spl`
  pins lane marker, queue phase, receipt counter, and payload accessor
  declarations without requiring live LLVM hardware/tooling.
- impl: Migrated pure Engine2D clip/bounds/mask helpers from
  `gc_async_mut/gpu/engine2d/helpers_clip.spl` to
  `nogc_async_mut/gpu/engine2d/helpers_clip.spl`. The GC path is now an
  export-only compatibility shim, and `helpers_parity_spec.spl` covers the
  no-GC canonical helper path.
- verify: Ran `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
  with captured output. Overall GUI/web Host-GPU queue/readback status passed
  for Vulkan joined frame evidence plus CUDA/OpenCL child readback fixtures;
  Metal/ROCm remained host-unavailable on Linux and DirectX/WebGPU remained
  provenance-only guarded, so the platform matrix is still partial.
- impl: Migrated Engine2D bitmap glyph and text blit helpers from `gc_async_mut/gpu/engine2d/{glyph,helpers_text}.spl` to canonical `nogc_async_mut/gpu/engine2d`. GC and GC-sync glyph/text paths are export-only compatibility facades, text helpers now depend on no-GC color/glyph modules directly, and glyph/text specs cover the no-GC canonical paths.
- impl: Completed the matching no-GC color helper slice by moving
  `engine2d/color.spl` to canonical `nogc_async_mut` and keeping
  `gc_async_mut` as an export-only facade. Added same-family and deep
  `std.nogc_async_mut.gpu.engine2d.*` alias guards to the Rust lint checker,
  Rust module loader, and Pure Simple GC-boundary mirror. Verified with rebuilt
  `src/compiler_rust/target/debug/simple check` on no-GC color/pixel/text
  helpers plus the focused Engine2D and GC-boundary specs; release `bin/simple`
  remains stale until rebuilt.
- impl: Added canonical no-GC Engine2D package facades at
  `src/lib/nogc_async_mut/gpu/engine2d/{mod,__init__}.spl` and exposed a focused
  migrated Engine2D contract/helper/event-flow set from the top-level
  `std.gpu` facade without importing GC concrete backends. Added
  `test/01_unit/lib/nogc_async_mut/gpu/engine2d/facade_spec.spl` plus generated
  manual coverage proving package-level `std.gpu.engine2d` and top-level
  `std.gpu` access to no-GC Engine2D contracts/helpers.
- audit: DirectX and WebGPU still do not have production device-readback
  evidence. Current DirectX `swapchain_present` and WebGPU `surface_upload`
  readbacks are provenance-only; production completion still needs real staging
  texture / copy-buffer readback paths before evidence gates can claim
  `device_readback` for those backends.
- impl: Migrated the pure nested Engine2D helper contracts
  `helpers/{pixel_pack,clip_mask,text_fallback,upload_download}.spl` to
  canonical `nogc_async_mut`; the old `gc_async_mut` helper paths are now
  explicit export-only facades. Added no-GC helper package facades
  `helpers/{mod,__init__}.spl`, exported the helper contracts through
  `std.gpu.engine2d` and top-level `std.gpu`, and added
  `helpers_facade_spec.spl` plus generated manual coverage for no-GC and legacy
  GC import paths. `spipe-docgen` still reports the generated helper manual as a
  stub by heuristic even though it includes scenario steps and assertions.
- impl: Added fail-closed WebGPU staging readback checksum evidence plumbing:
  `src/runtime/hosted/webgpu.rs` now exports `rt_webgpu_readback_checksum`,
  the no-GC SFFI wrapper exposes `webgpu_sffi_readback_checksum`, and
  `backend_webgpu.spl` only reports `device_readback` when that checksum is
  nonnegative. Default/stub builds stay `surface_upload` provenance-only. The
  compiler/runtime symbol table and interpreter extern dispatch were updated so
  Pure Simple interpreter tests see the same negative checksum sentinel.
- verify: Focused WebGPU/default and no-GC event evidence checks pass with the
  rebuilt `src/compiler_rust/target/debug/simple`: `backend_webgpu_spec`,
  `backend_readback_handle_contract_spec`, no-GC `engine2d_readback_metadata`,
  no-GC `host_gpu_event_queue`, GC `draw_ir_runtime_queue`, and hosted runtime
  `webgpu::tests`. The aggregate
  `check-production-gui-web-host-gpu-queue-readback-evidence.shs` was updated
  to use the moved no-GC specs and now passes WebGPU provenance guards, but the
  overall gate still fails because same-frame Vulkan browser-backend
  device-readback receipt remains unproven.
- audit: Remaining no-GC migration work is not complete. Read-only sidecar
  found duplicated mask block helpers in concrete GC backends, duplicated
  Vulkan/Metal push-constant byte packers, and lower-priority direct text
  render helpers. Next no-GC slices should move common mask/packing helpers to
  canonical no-GC modules before touching more concrete backend code.
- impl: BrowserBackend input dispatch now records host/GPU event-flow evidence
  with the canonical `frame_batch` operation, so the scheduler marks the event
  GPU-batchable. Focused probe evidence shows one enqueue, one poll, one
  dispatch, `event_host_gpu_target_lane=gpu`, `forwarded=true`, and
  `backward_completed=true`. Same-frame Vulkan BrowserBackend readback also now
  reports `first_readback_status=readback`, `first_readback_backend=vulkan`,
  `first_gpu_readback_source=device_readback`, and the expected
  `same-frame Engine2D read_pixels` reason.
- impl: Moved the WebGPU SFFI extern owner to
  `src/lib/common/gpu/webgpu_sffi.spl`; the no-GC path is now a compatibility
  facade and the GC WebGPU backend imports the shared common wrapper. This
  removes the new GC-to-no-GC family-boundary warning without duplicating the
  runtime extern block.
- verify: Re-ran focused WebGPU and BrowserBackend queue specs with the rebuilt
  Rust Simple driver. `backend_webgpu_spec` and
  `browser_backend_runtime_queue_spec` pass, and `simple check` passes for the
  shared WebGPU SFFI/no-GC facade/GC backend files. The aggregate
  `check-production-gui-web-host-gpu-queue-readback-evidence.shs` still exits
  nonzero, but now for the accurate blocker:
  `production_runtime_queue_integration_reason=browser-frame-first-render-budget-not-met`.
  Event forward/backward and same-frame Vulkan device-readback evidence pass;
  first render remains about 7.5s while second render is under budget.
- impl: Removed duplicate Draw IR evidence rendering from the BrowserBackend
  host/GPU frame path. `draw_ir_adv.spl` now exposes
  `engine2d_draw_ir_adv_batch_runtime_queue_dispatch_only`, which performs the
  same runtime queue submit/drain/dispatch and payload receipt without parsing
  the payload back into a second Engine2D render. BrowserBackend uses this
  helper for dispatch evidence while the real frame pixels/readback continue to
  come from the SimpleWeb Engine2D artifact.
- impl: Added BrowserBackend render-stage timing evidence fields and probe
  output so first-frame regressions can distinguish DOM/layout, HTML assembly,
  pixel/readback artifact, Draw IR dispatch, framebuffer copy, and state-store
  cost. The production evidence script now captures these fields in
  `build/production_gui_web_host_gpu_queue_readback/evidence.env`.
- impl: Moved the host/GPU event-path system spec off direct `rt_host_gpu_*`
  declarations by adding owner-module wrappers
  `engine2d_host_gpu_runtime_reset` and
  `engine2d_host_gpu_runtime_emit_packet`.
  `runtime_need`: test and adapter code need to reset and seed the real
  host/GPU runtime queue before exercising submit/complete/drain phases.
  `facade_checked`: existing Engine2D host/GPU event queue facade already wraps
  submit, complete, drain, status, and payload paths but did not expose reset or
  plain packet seeding.
  `chosen_path`: add-smallest-owner-facade in the Engine2D host/GPU queue owner
  module, mirrored across no-GC canonical and legacy GC surfaces.
  `rejected_shortcuts`: direct runtime externs in SPipe specs, fixture-only
  queue counters, backend field pokes, and generated-code workarounds.
- impl: Extracted the SimpleWeb Engine2D layout-routing predicate and used it
  from the readback path so layout-routed HTML can call
  `simple_web_layout_render_html_readback` directly instead of rendering pixels
  and then re-presenting the same pixels through Engine2D. This preserves the
  pinned heuristic/fixture routes and keeps backend readback provenance intact.
- verify: Focused checks/specs pass with the rebuilt Rust Simple driver:
  `simple check` for BrowserBackend, Draw IR adv, renderer readback routing,
  WebGPU common/no-GC/GC wrapper files; `browser_backend_runtime_queue_spec`;
  `backend_webgpu_spec`; `draw_ir_runtime_queue_spec`; and
  `draw_ir_adv_spec`. The aggregate
  `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
  now exits 0. Latest evidence: `browser_first_render_us=3418191`,
  `browser_first_render_under_budget=true`,
  `browser_first_render_pixel_artifact_us=3003556`,
  `browser_first_render_draw_ir_dispatch_us=18266`,
  `browser_frame_queue_status=pass`,
  `same_frame_gpu_backend_readback_status=pass`, and
  `production_runtime_queue_integration_status=pass`.
- plan: Added `doc/03_plan/sys_test/production_gui_web_host_gpu_platform_execution.md`
  as the concrete Mac/Windows/ROCm/WebGPU execution checklist for Spark and
  normal-LLM agents. It records host requirements, commands, promotion keys,
  and fail-closed rules for Metal, DirectX, ROCm/HIP, and WebGPU so the partial
  platform matrix is actionable without relaxing the Linux Vulkan gate.
- impl: Added a standalone WebGPU real-mode readback wrapper at
  `scripts/check/check-webgpu-real-readback.shs` plus the hosted runtime
  example `src/runtime/hosted/examples/webgpu_readback_probe.rs`. The wrapper
  is separate from the default Linux aggregate and only exits 0 when
  `webgpu-real` returns `device_readback`, a positive backend handle, and
  matching expected/actual staging checksums.
- verify: Integrated the WebGPU real-mode wrapper into the production aggregate
  as optional device proof. On this host the wrapper passed with
  `webgpu_real_readback_source=device_readback`,
  `webgpu_real_readback_backend_handle=1`, and matching checksum
  `1023148974`. The aggregate still exits 0, now with
  `webgpu_spark_task_status=pass`,
  `webgpu_normal_llm_verification_status=pass`,
  `platform_matrix_status=partial`, and
  `missing_device_readback_platforms=metal,rocm,directx`.
- impl: Reduced host-GPU queue duplication by factoring the Draw IR runtime
  queue submit/drain/dispatch sequence into one private helper in
  `draw_ir_adv.spl`; both render-and-dispatch and dispatch-only paths now use
  the same lane scheduling, payload submit, drain, and dispatch logic.
- impl: Migrated pure WebGPU probe policy out of the GC backend into
  `src/lib/common/gpu/webgpu_probe.spl`. The GC Engine2D backend and spec now
  import `webgpu_available` / `webgpu_strict_init_check` from the common owner.
- impl: Moved WebGPU surface lifecycle/readback/compute wrappers into
  `src/lib/nogc_sync_mut/gpu/engine2d/webgpu_surface.spl` with a
  `gc_async_mut` compatibility facade. `backend_webgpu.spl` now keeps only the
  RenderBackend glue and CPU mirror buffer behavior for that surface path.
- verify: Focused WebGPU/no-GC checks pass:
  `simple check` for `common/gpu/webgpu_probe.spl`,
  `nogc_sync_mut/gpu/engine2d/webgpu_surface.spl`,
  `gc_async_mut/gpu/engine2d/webgpu_surface.spl`,
  `gc_async_mut/gpu/engine2d/backend_webgpu.spl`,
  `gc_async_mut/gpu/engine2d/engine.spl`, and the focused GPU directories.
  `backend_webgpu_spec`, `draw_ir_runtime_queue_spec`,
  `browser_backend_runtime_queue_spec`, MCP app check, Simple LSP MCP app check,
  and MCP stdio integration pass. Full `src/lib` and `src/compiler` checks were
  attempted with bounded timeouts and timed out before completion; partial logs
  showed existing unrelated warnings, not a host-GPU regression.
- impl: Closed the Pure Simple MIR-interpreter host-GPU runtime gap. Unknown
  named MIR calls and call terminators now route through `_call_runtime_fn`
  before falling back to `0`, and `_call_runtime_fn` handles the
  `rt_host_gpu_*` lane/queue extern family used by lowered `HostGpuLane`.
- verify: Added
  `test/01_unit/compiler/interpreter/mir_host_gpu_runtime_spec.spl` plus the
  generated manual
  `doc/06_spec/test/01_unit/compiler/interpreter/mir_host_gpu_runtime_spec.md`.
  The spec builds a tiny MIR function containing the lowered runtime call shape
  and proves `packet_count=1`, `submitted=1`, `completed=1`, `in_flight=0`,
  `event_count=2`, and `last_backend_handle=77` through `MirInterpreter`.
  `simple check` passes for `src/compiler/95.interp/mir_interpreter.spl`, the
  new spec source, and `test/03_system/feature/language/host_gpu_lane_spec.spl`;
  the new MIR spec and the existing host-GPU lane system spec both pass in
  interpreter mode. Generated-spec layout guard remains `0`.
- todo: Core flat interpreter still needs structural `host(...)` / `gpu(...)`
  handling in `src/compiler/10.frontend/core/interpreter/eval_ops_part1.spl`.
  Parser desugaring already turns `target.later(...) gpu \:` into
  `gpu(marker, lambda)`, but `eval_call` currently treats `gpu`/`host` as
  ordinary undefined functions unless the HIR/MIR lowering path is used.
- impl: Closed the core flat-interpreter `host(...)` / `gpu(...)` lane gap.
  `eval_call` now recognizes structural `host(marker, lambda)` and
  `gpu(marker, lambda)` calls before normal builtin/function lookup, evaluates
  the marker first, emits lane begin/end events, queues/submits/completes GPU
  packets with the active backend handle, and runs the lambda body through the
  existing `eval_block` scope/defer machinery.
- verify: Strengthened
  `test/03_system/feature/language/host_gpu_lane_spec.spl` so the interpreted
  host/GPU/host callback scenario also proves GPU queue evidence:
  `queue=1`, `submitted=1`, `completed=1`, `in_flight=0`, and backend handle
  round-trip. `simple check` passes for
  `src/compiler/10.frontend/core/interpreter/eval_ops_part1.spl` and the
  host-GPU lane system spec. The host-GPU lane system spec passes in
  interpreter mode, the MIR host-GPU runtime spec still passes, and the
  generated-spec layout guard remains `0`.
- verify: Re-ran the aggregate production evidence after the core interpreter
  host/GPU queue fix:
  `SIMPLE_BIN=src/compiler_rust/target/debug/simple sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
  completed with status `0`.
  `production_gui_web_host_gpu_queue_readback_status=pass`,
  `production_runtime_queue_integration_status=pass`,
  `webgpu_real_readback_status=pass`, `webgpu_real_readback_source=device_readback`,
  and `webgpu_real_readback_backend_handle=1`. The platform matrix remains
  partial because `missing_device_readback_platforms=metal,rocm,directx`;
  Metal and ROCm are host-unavailable on this Linux host, while DirectX remains
  the next local code/evidence gap.
- impl: Moved the host-GPU runtime lane/phase/kind/status contract into named
  Pure Simple constants in
  `src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl` and exported
  them through the existing GC shim. The no-GC runtime queue path now emits
  `ENGINE2D_HOST_GPU_RUNTIME_LANE_GPU` /
  `ENGINE2D_HOST_GPU_RUNTIME_KIND_DRAW_IR` instead of bare numeric literals,
  and status-name mapping uses the exported status constants.
- impl: Replaced the core flat-interpreter host/GPU structural handler's
  runtime event/queue magic numbers with named Pure Simple constants local to
  `src/compiler/10.frontend/core/interpreter/eval_ops_part1.spl`, aligned with
  the no-GC queue and Rust runtime contract. Runtime queue state remains owned
  by the hosted runtime; only the shared numeric contract was centralized.
- verify: `simple check` passes for the no-GC host-GPU queue module, the GC
  shim, the GC Engine2D public module, and the core interpreter file. The
  host-GPU lane system spec still passes in interpreter mode with 11 scenarios,
  and the generated-spec layout guard remains `0`.
- verify: Re-ran the aggregate production evidence after the no-GC runtime
  constants migration. The wrapper completed with status `0`;
  `production_gui_web_host_gpu_queue_readback_status=pass`,
  `production_runtime_queue_integration_status=pass`,
  `queue_backend_handle_roundtrip_status=pass`,
  `webgpu_real_readback_status=pass`,
  `webgpu_real_readback_source=device_readback`, and
  `webgpu_real_readback_backend_handle=1`. The remaining platform matrix is
  unchanged: `missing_device_readback_platforms=metal,rocm,directx`.
- impl: Added a no-GC structured D3D11/DXVK readback target facade in
  `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl`. The facade now creates a
  readback target, uploads framebuffer pixels, returns copied pixels with
  pixel count/checksum, and rejects destroyed or invalid targets.
- impl: Wired `DirectXBackend` to create the no-GC readback target, upload the
  software framebuffer on `present()`, cache the returned pixels/checksum, and
  report `device_readback` only when `last_readback_ok`, positive
  `readback_handle`, non-empty pixels, and positive checksum evidence are all
  present. Otherwise it keeps the previous `swapchain_present`/`cpu_mirror`
  provenance paths.
- verify: Added focused DXVK and DirectX backend assertions for readback
  handle/checksum propagation and tightened
  `backend_readback_handle_contract_spec.spl` so DirectX `device_readback`
  requires positive readback handle and pixel/checksum gates.
  `dxvk_spec`, `dxvk_vkd3d_dispatch_spec`, `backend_directx_spec`, and
  `backend_readback_handle_contract_spec` all pass in interpreter mode.
- verify: Updated the aggregate evidence wrapper to report DirectX as
  `structured-readback-contract` instead of plain `provenance-only` while
  keeping production/native DirectX device readback pending. The aggregate
  wrapper completed with status `0`, `presentation_provenance_guard_status=pass`,
  `directx_spark_task_status=structured-readback-contract`,
  `directx_normal_llm_verification_status=structured-readback-contract-pass-native-pending`,
  and `missing_device_readback_platforms=metal,rocm,directx`.
- impl: Added `scripts/check/check-directx-native-readback.shs`, a fail-closed
  Windows native D3D11 evidence wrapper. It records the required production
  path (`ID3D11Texture2D` render target -> staging texture -> `CopyResource` ->
  `Map` -> checksum -> `Unmap`) and emits host-unavailable evidence on Linux
  instead of promoting the structured DXVK contract to production proof.
- verify: Wired the DirectX native wrapper into the production aggregate as
  `readback_directx_native_*`. On this Linux host it reports
  `readback_directx_native_status=unavailable`,
  `readback_directx_native_reason=directx-native-readback-requires-windows`,
  and `readback_directx_native_verdict=unavailable`. The aggregate still exits
  with status `0` for the Linux-supported production lane, keeps
  `directx_spark_task_status=structured-readback-contract`, keeps
  `directx_normal_llm_verification_status=structured-readback-contract-pass-native-pending`,
  and keeps `missing_device_readback_platforms=metal,rocm,directx`.
- docs: Updated platform plan and Spark handoff docs so WebGPU real
  `device_readback` is no longer listed as missing, WebGPU `surface_upload`
  remains provenance-only, and DirectX is described as structured-contract with
  native Windows D3D11 evidence pending.
- impl: Added hosted runtime example
  `src/runtime/hosted/examples/directx_native_readback_probe.rs` and wired
  `scripts/check/check-directx-native-readback.shs` to run it through Cargo
  when no external `DIRECTX_NATIVE_READBACK_HARNESS` executable is provided.
  The example emits fail-closed evidence on non-Windows/default builds and
  reserves the Windows `win32-real` path for the native D3D11 staging texture
  implementation.
- verify: `cargo run --manifest-path src/runtime/hosted/Cargo.toml --example
  directx_native_readback_probe` succeeds on Linux and emits
  `directx_native_readback_status=unavailable`,
  `directx_native_readback_reason=directx-native-readback-requires-windows-win32-real`,
  and `directx_native_readback_source=not_device_readback`. The DirectX native
  wrapper consumes that example and the aggregate production wrapper still
  completes with status `0`, preserving
  `missing_device_readback_platforms=metal,rocm,directx`.
- impl: Completed the Windows-gated hosted runtime D3D11 native readback probe
  in `src/runtime/hosted/examples/directx_native_readback_probe.rs`. The
  `win32-real` path now creates a D3D11 hardware device, initializes a
  render-target `ID3D11Texture2D`, creates a staging texture, performs
  `CopyResource`, maps the staging resource, copies row-pitched pixels, and
  reports `pass/device_readback` only when the checksum matches and the probe
  handle is positive. Linux/default builds remain fail-closed typed unavailable.
- impl: Added the target-gated `windows` crate dependency to
  `src/runtime/hosted/Cargo.toml` for the D3D11 probe while leaving default
  Linux builds dependency-light. `Cargo.lock` was updated by Cargo.
- impl: Reduced GC DirectX readback duplication. Durable readback pixels now
  remain canonical in the no-GC `dxvk_d3d11` readback target; the GC Engine2D
  adapter tracks only handle/status/pixel-count/checksum evidence and reads the
  no-GC snapshot on demand. DirectX readback validity now requires exact pixel
  count rather than positive checksum so all-zero frames remain valid.
- impl: Hardened DirectX partial-init cleanup for created no-GC device/readback
  handles on swapchain/readback/software init failures. The no-GC DXVK facade
  still has no swapchain destroy surface, so swapchain release remains limited
  by the current facade.
- impl: Extended `scripts/check/check-directx-native-readback.shs` to publish
  `directx_native_readback_exit_code` and `directx_native_readback_timed_out`,
  and to use `timeout-after-${TIMEOUT_SECS}s` on timeout. Extended the aggregate
  wrapper with explicit `directx_native_gate_status`, currently `unavailable`
  on this Linux host.
- docs: Updated the DirectX platform matrix wording so DirectX is included as a
  native child probe in the production wrapper but is not a production pass
  unless `readback_directx_native_verdict=pass` and
  `directx_native_gate_status=pass`.
- verify: `cargo check --manifest-path src/runtime/hosted/Cargo.toml --target
  x86_64-pc-windows-gnu --features win32-real --example
  directx_native_readback_probe` passes, proving the Windows-gated D3D11 code
  type-checks locally without hardware. `rustfmt --check` passes for the
  DirectX probe file.
- verify: Focused Simple checks/specs pass for `backend_directx.spl`,
  `backend_directx_spec.spl`, `backend_readback_handle_contract_spec.spl`,
  `dxvk_spec.spl`, and `dxvk_vkd3d_dispatch_spec.spl`. Docgen refreshed the
  DirectX backend and readback-handle contract manuals; docgen emitted only
  existing toolchain warnings. `find doc/06_spec -name '*_spec.spl' | wc -l`
  remains `0`.
- verify: `scripts/check/check-directx-native-readback.shs` remains fail-closed
  on Linux with `status=unavailable`, `reason=directx-native-readback-requires-windows-win32-real`,
  `source=not_device_readback`, `exit_code=0` for the inner cargo probe, and
  wrapper exit `1`. The aggregate wrapper exits `0` with Linux lane pass,
  `directx_native_gate_status=unavailable`, WebGPU real device readback pass,
  and remaining missing native device-readback platforms
  `metal,rocm,directx`.
- impl: Added stable first-class DirectX wrapper SSpec coverage in
  `test/03_system/check/directx_native_readback_spec.spl`. The spec runs
  `scripts/check/check-directx-native-readback.shs` through `/bin/sh` with a
  build-local `BUILD_DIR`/`REPORT_PATH`, treats `evidence.env` as the oracle,
  and accepts either fail-closed non-Windows evidence or a Windows pass only
  when `source=device_readback`, the backend handle is positive, and expected
  and actual checksums match.
- impl: Added `linux_gui_web_queue_integration_status`,
  `linux_gui_web_queue_integration_reason`, and
  `full_host_gpu_platform_matrix_status` to the production aggregate wrapper.
  The compatibility `production_gui_web_host_gpu_queue_readback_status` remains
  for existing consumers, but reports and handoff docs now distinguish Linux
  queue integration pass from full platform matrix completion.
- verify: Added DirectX all-zero frame coverage to
  `backend_directx_spec.spl`; DirectX device readback now accepts exact
  pixel-count readback with checksum `0`, proving checksum is evidence rather
  than a validity gate. `backend_directx_spec.spl` now passes with 22 tests.
- verify: `test/03_system/check/directx_native_readback_spec.spl` passes in
  interpreter mode and its generated manual was refreshed under `doc/06_spec`.
  The aggregate production wrapper exits `0` on Linux with
  `linux_gui_web_queue_integration_status=pass`,
  `full_host_gpu_platform_matrix_status=partial`,
  `directx_native_gate_status=unavailable`, and
  `missing_device_readback_platforms=metal,rocm,directx`. The generated-spec
  layout guard remains `0`.
- impl: Added shared Metal/ROCm generated-2D native readback wrapper SSpec
  coverage in `test/03_system/check/generated_2d_native_readback_wrappers_spec.spl`.
  The spec runs each wrapper with an isolated build-local evidence directory,
  treats `evidence.env` as the oracle, requires typed evidence keys, and only
  accepts a native pass when submit/readback evidence is true and checksums
  match. Generated manual refreshed under `doc/06_spec/test/03_system/check/`.
- impl: Added source-safe `*_required_path` evidence keys to Metal and ROCm/HIP
  generated-2D readback wrappers. The values are shell-quoted so the wrappers
  can still source `evidence.env` before report generation. Required paths now
  document Metal source -> metallib -> MTLDevice/pipeline/command-buffer ->
  submit/wait/readback/per-op checksum and HIP source -> HSACO -> ROCm
  loader/device/module/kernel -> launch/synchronize/readback/per-op checksum.
- fix: The first required-path attempt used unquoted values with spaces, which
  made `.` sourcing of `evidence.env` fail (`source: not found` for Metal and
  redirection-like parsing for ROCm). Quoting fixed the wrappers; direct wrapper
  runs now exit predictably with code `1` for typed unavailable instead of shell
  parse errors.
- docs: Removed stale WebGPU provenance-only wording from platform execution and
  matrix docs. Current docs state WebGPU real `device_readback` passes while
  WebGPU `surface_upload` remains provenance-only. The full platform matrix is
  still partial because Metal, ROCm/HIP, and native DirectX are missing.
- verify: `generated_2d_native_readback_wrappers_spec.spl` passes in interpreter
  mode with 2 scenarios. Direct Metal and ROCm wrapper runs emit typed
  unavailable evidence on this Linux host with required-path keys and exit `1`.
  The aggregate production wrapper exits `0` with
  `linux_gui_web_queue_integration_status=pass`,
  `full_host_gpu_platform_matrix_status=partial`, Metal/ROCm child exit codes
  `1`, `webgpu_spark_task_status=pass`, and missing platforms
  `metal,rocm,directx`. Generated-spec layout guard remains `0`.
- impl: Extended `scripts/check/check-rocm-generated-2d-readback.shs` with a
  future ROCm submit/readback harness path mirroring the Metal wrapper. When a
  verified HSACO, ROCm loader, probe tool, Simple binary, and
  `scripts/check/rocm_generated_2d_readback_harness.spl` are present, the
  wrapper now runs the harness and emits per-op `fill/copy/alpha/scroll`
  checksum/expected pairs. Current hosts without the required toolchain or
  harness still fail closed as typed unavailable.
- verify: Updated `generated_2d_native_readback_wrappers_spec.spl` so ROCm pass
  evidence must prove `submit_attempted=true`, `readback_available=true`, and
  per-op checksum equality, not only aggregate checksum equality. The spec
  passes in interpreter mode with 2 scenarios, and the regenerated manual is
  present under `doc/06_spec/test/03_system/check/`.
- verify: Direct ROCm wrapper run on this host remains typed unavailable with
  `reason=missing-primary-tool`, `submit_attempted=false`,
  `readback_available=false`, required-path evidence present, and exit `1`.
  The aggregate production wrapper still exits `0` for the Linux GUI/web lane,
  with `readback_rocm_exit_code=1`, `readback_rocm_verdict=host-unavailable`,
  `full_host_gpu_platform_matrix_status=partial`, and missing platforms
  `metal,rocm,directx`. Generated-spec layout guard remains `0`.
- impl: Moved DXVK D3D11 probe cleanup and present/upload/readback validation
  into no-GC `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl`. The GC DirectX
  Engine2D adapter now delegates probe and readback validity/checksum policy to
  no-GC helpers instead of duplicating it locally.
- verify: Added no-GC DXVK SSpec coverage for probe cleanup,
  `present_readback`, and all-zero frame validity. `dxvk_spec.spl` passes with
  20 scenarios, `backend_directx_spec.spl` still passes with 22 scenarios, and
  the production aggregate emits
  `native_readback_wrapper_sspec_coverage_status=pass` while the full platform
  matrix remains partial (`metal,rocm,directx` missing native readback hosts).
- impl: Completed the remaining small DirectX probe migration by routing
  `probe_directx()` through no-GC `dxvk_d3d11_probe_device()`, matching
  `dx_platform_probe()` and avoiding GC-side probe device ownership.
- impl: Added standalone verifier/report symmetry keys:
  `webgpu_real_readback_report` for WebGPU real readback and
  `directx_native_readback_wrapper_gate_status` /
  `directx_native_readback_wrapper_exit_code` for DirectX native readback.
  The DirectX SSpec now asserts those keys so typed unavailable is not confused
  with an inner harness/Cargo exit code.
- docs: Refreshed the queue/readback system-test plan so DirectX references the
  existing native wrapper and WebGPU states current `device_readback` pass while
  keeping `surface_upload` provenance-only. Generated wrapper manuals now carry
  the 2026-06-15 evidence date.
- impl: Propagated DirectX native child wrapper gate details into the production
  aggregate evidence. The aggregate now publishes
  `readback_directx_native_wrapper_gate_status`,
  `readback_directx_native_wrapper_exit_code`, and
  `readback_directx_native_child_report`, and the presentation table shows the
  child gate separately from the aggregate native gate.
- verify: The production aggregate wrapper exits `0` on this Linux host with
  Linux queue integration `pass`, `webgpu_real_readback_status=pass`,
  `native_readback_wrapper_sspec_coverage_status=pass`,
  `readback_directx_native_wrapper_gate_status=unavailable`,
  `readback_directx_native_wrapper_exit_code=1`, and
  `full_host_gpu_platform_matrix_status=partial` because native Metal, ROCm,
  and DirectX host evidence remains unavailable.
- verify: Tightened native wrapper SSpecs so unknown non-pass statuses no
  longer fall through as unavailable. DirectX, Metal, and ROCm wrapper specs now
  accept only `pass` or typed `unavailable`; unavailable evidence must carry a
  nonempty reason. The focused DirectX wrapper spec passes with 1 scenario and
  the generated-2D Metal/ROCm wrapper spec passes with 2 scenarios.
- impl: Added hardware-free BrowserBackend event-to-frame correlation receipts.
  `BrowserBackend.record_event_dispatch()` now assigns a stable
  `browser-input-N` correlation id, and the next rendered frame records whether
  that event produced a queued frame with same-frame `device_readback` evidence.
  Cache-hit frames reset the correlation receipt to `not_requested`.
- verify: `browser_backend_runtime_queue_spec.spl` passes with the new
  `first_event_correlation_status=event_frame_readback_correlated` and
  `second_event_correlation_status=not_requested` assertions. The UI event
  evidence system spec passes with 3 scenarios after regenerating manuals.
  The production aggregate now gates Linux queue integration on
  `event_frame_correlation_status=pass` and still exits `0`; full platform
  matrix remains partial pending Metal, ROCm, and DirectX native host evidence.
- verify: Added `production_gui_web_host_gpu_aggregate_status_contract_spec.spl`
  so the legacy `production_gui_web_host_gpu_queue_readback_status=pass` key
  cannot be mistaken for full host-GPU platform readiness. The spec requires
  the report and wrapper to publish distinct Linux queue integration, legacy
  compatibility, and full platform-matrix status keys. The focused check and
  interpreter run pass, generated manual coverage is refreshed, and the
  generated-spec layout guard remains `0`.
- impl: Migrated Draw IR runtime queue payload/dispatch ownership to no-GC
  `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl`. The GC
  `draw_ir_adv` renderer now delegates payload checksum/SDN generation and
  submit/drain/dispatch-only queue receipts through an export-only GC shim,
  while preserving the existing render-capable API.
- verify: Added no-GC unit coverage for Draw IR runtime queue dispatch without
  importing the GC Engine2D renderer. The rebuilt Rust Simple checker passes
  for the no-GC helper/spec and the GC compatibility wrapper/spec; interpreter
  tests pass for both no-GC dispatch-only and legacy GC render-queue specs.
- verify: Re-ran BrowserBackend runtime queue coverage and the production
  GUI/web host-GPU aggregate wrapper after the no-GC Draw IR queue migration.
  BrowserBackend queue evidence still passes, and the aggregate exits `0` with
  `event_frame_correlation_status=pass`, `linux_gui_web_queue_integration_status=pass`,
  legacy `production_gui_web_host_gpu_queue_readback_status=pass`, and
  `full_host_gpu_platform_matrix_status=partial` because native Metal, ROCm,
  and DirectX device-readback hosts remain unavailable.
- impl: Removed the production aggregate wrapper's shell-generated
  `queue_probe.spl` source. The runtime queue probe is now committed as
  `test/01_unit/lib/nogc_async_mut/gpu/engine2d/runtime_queue_probe.spl`, and
  the wrapper records `queue_probe_source` while preserving the existing
  zero-backend, nonzero-backend, payload, and overflow evidence keys.
- verify: The committed no-GC runtime queue probe checks and runs with the same
  queue evidence values as the former inline probe. The aggregate contract spec
  now has 3 passing scenarios, including the committed-probe contract, and the
  production aggregate wrapper exits `0` with Linux integration `pass` and full
  platform matrix `partial`.
- impl: Split Draw IR runtime queue SSpec evidence in the production aggregate
  wrapper into canonical no-GC and legacy GC bridge gates. The wrapper now runs
  `test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`
  first, keeps the historical `draw_ir_runtime_queue_*` keys as no-GC aliases,
  and records separate `nogc_draw_ir_runtime_queue_*` and
  `gc_draw_ir_runtime_queue_*` status/timeout/exit keys.
- verify: The no-GC Draw IR runtime queue spec, legacy GC bridge spec, and
  aggregate status contract all pass. The production aggregate exits `0`, now
  reports both `nogc_draw_ir_runtime_queue` and `gc_draw_ir_runtime_queue` rows,
  and still reports Linux GUI/web integration `pass` with full platform matrix
  `partial`.
- verify: Added `production_gui_web_host_gpu_platform_matrix_followup_spec.spl`
  to lock the remaining host-specific proof contract. The spec checks that the
  aggregate report remains `full_host_gpu_platform_matrix_status=partial` with
  `missing_device_readback_platforms=metal,rocm,directx`, that macOS Metal,
  ROCm/HIP, and Windows DirectX promotion requirements are documented with
  real `device_readback` expectations, and that Spark/normal-LLM platform
  review keys remain exposed by the wrapper. The focused check and interpreter
  run pass with 4 scenarios, and generated manual coverage is refreshed.
- verify: Extended the platform matrix follow-up spec to lock the child wrapper
  report contract for the current Linux host: Metal and ROCm generated 2D
  reports must remain typed `unavailable` with no submit/readback evidence, and
  DirectX must remain `unavailable` with `source=not_device_readback` until a
  real Windows D3D readback host promotes it. The focused check and interpreter
  run now pass with 5 scenarios.
- verify: Extended the platform matrix follow-up spec again to lock the local
  Linux production gates that are already required by the aggregate wrapper:
  Vulkan, CUDA, and OpenCL child readback verdicts must remain `pass`, and the
  plan now names those keys alongside the BrowserBackend same-frame
  `device_readback` proof. The focused check passes, the interpreter run now
  passes with 6 scenarios, and the generated manual was refreshed.
- impl: Tightened generated-2D CUDA evidence symmetry. The CUDA wrapper now
  emits `cuda_generated_2d_readback_submit_attempted` and
  `cuda_generated_2d_readback_readback_available` on unavailable, fail, and
  pass paths. The production aggregate lifts CUDA/OpenCL/Metal/ROCm
  submit/readback booleans into top-level `readback_*` keys and requires CUDA
  and OpenCL submit/readback availability before Linux queue integration can
  pass.
- verify: Re-ran the production aggregate wrapper after the stricter
  CUDA/OpenCL gate. It exits `0` and reports
  `readback_cuda_submit_attempted=true`,
  `readback_cuda_readback_available=true`,
  `readback_opencl_submit_attempted=true`,
  `readback_opencl_readback_available=true`, and
  `production_runtime_queue_integration_status=pass`; the full platform matrix
  remains partial for native Metal, ROCm, and DirectX host evidence.
- impl: Made the production aggregate report table-friendly for Spark and
  normal-LLM review. The Readback Matrix now has explicit `Submit attempted`
  and `Readback available` columns, and the Platform Spark/Normal-LLM table
  has a compact `linux_gui_web` row with event id, queue packet, readback
  source, and checksum plus a DirectX row that surfaces native verdict, gate,
  child gate, and reason.
- verify: Re-ran the production aggregate wrapper after the report-table
  change; it exits `0` and the platform follow-up SSpec passes with 6
  scenarios against the regenerated report.
- docs: Aligned the UI stack architecture, TLDR, and production queue-readback
  plan with the current no-GC Draw IR runtime queue owner and the table-friendly
  report contract. The docs now name
  `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl`, require the
  no-GC queue dispatch spec as an ownership gate, and keep submit/readback,
  compact `linux_gui_web`, and DirectX native gate fields visible for Spark and
  normal-LLM review.
- verify: Extended `production_gui_web_host_gpu_platform_matrix_followup_spec.spl`
  with architecture/TLDR alignment checks. The focused checker and interpreter
  run pass with 7 scenarios, and the generated manual metadata is refreshed to
  `2026-06-15`.
- impl: Moved BrowserBackend production Draw IR runtime queue dispatch and
  host/GPU event-flow imports to the canonical no-GC Engine2D modules:
  `std.nogc_async_mut.gpu.engine2d.draw_ir_runtime_queue`,
  `host_gpu_event_queue`, and `host_gpu_draw_ir_event_flow`. GC-family modules
  continue to route through their export-only compatibility shims to avoid
  runtime-family boundary warnings.
- impl: Demoted the legacy GC Draw IR runtime queue bridge from aggregate
  pass/fail gating to compatibility evidence. The production wrapper now
  requires `nogc_draw_ir_runtime_queue_status=pass` for runtime queue
  integration, while still reporting `gc_draw_ir_runtime_queue` as
  `legacy_gc_queue_bridge`.
- verify: Re-ran focused checks and interpreter specs after the no-GC-first
  migration. BrowserBackend and adjacent GC compatibility files check cleanly;
  `production_gui_web_host_gpu_aggregate_status_contract_spec.spl` passes with
  5 scenarios; `production_gui_web_host_gpu_platform_matrix_followup_spec.spl`
  passes with 7 scenarios; and the aggregate wrapper exits `0` with
  `production_runtime_queue_integration_status=pass`,
  `linux_gui_web_queue_integration_status=pass`, and
  `full_host_gpu_platform_matrix_status=partial` for Metal, ROCm, and DirectX.
