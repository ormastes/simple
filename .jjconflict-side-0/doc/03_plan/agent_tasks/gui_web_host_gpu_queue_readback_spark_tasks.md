# GUI/Web Host-GPU Queue + Readback — Spark Handoff

Owner: normal-LLM/Spark lane
Date: 2026-06-14
Status: superseded/merged into
`doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`
for broad GUI/Web/2D rendering delegation. Keep this file as the queue/readback
technical task packet only; do not use it as the current top-level platform
plan or completion evidence.

Current routing update, 2026-06-27:

- Use `doc/03_plan/agent_tasks/gui_rendering_parallel_agent_plan_2026-06-27.md`
  WO-9 for stale-doc cleanup and the active Spark/normal-review split.
- Use `doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md`
  for Linux Vulkan, macOS Metal, and Windows D3D12 RenderDoc/render-log
  platform execution.
- This file remains useful for BrowserBackend queue/readback metadata and
  fail-closed device-readback semantics.
- Spark output from this packet is advisory until a normal/high-capability
  reviewer accepts no raw `rt_*` additions, no direct backend-poke pass states,
  and no promotion of provenance-only rows to production proof.
- Retained 4K/8K showcase performance is now tracked as a dedicated lane in the
  2026-06-27 parallel plan, not in this queue/readback packet.

Historical status: current local focused specs passed when this packet was
written, and the production wrapper reported the platform matrix explicitly as
partial unless Metal/ROCm/DirectX/WebGPU same-frame device-readback proof was
present. Treat the rows below as last-known historical routing notes, not as a
prediction that a fresh run will pass. WebGPU `surface_upload` is
provenance-only and WebGPU real device readback was unavailable in that slice.
The Linux joined GUI/web frame proof was Vulkan-backed; CUDA/OpenCL were child
backend readback fixtures. Synthetic handles remain isolated probe evidence.

## Context

- This lane owns the final chain from 2D draw scheduling -> host/GPU queue emit/drain ->
  BrowserBackend frame evidence -> same-frame GPU readback receipt.
- Canonical source of truth: `sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`.
- Latest report at the time of this packet
  (`doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md`)
  was the last-known evidence source. Regenerate the wrapper before reuse; do
  not treat these historical rows as an expected current pass:
  `browser_frame_queue_status=pass`, `same_frame_gpu_backend_readback_status=pass`,
  `readback_vulkan_verdict=pass`, `readback_cuda_verdict=pass`,
  `readback_opencl_verdict=pass`,
  positive `browser_first_backend_handle`, and
  `linux_gui_web_queue_integration_status=pass`. The full platform matrix is
  still expected to report `full_host_gpu_platform_matrix_status=partial` and
  `missing_device_readback_platforms=metal,rocm,directx,webgpu` until those
  native host lanes pass.
- After the Engine2D runtime queue bridge changed from evidence-only validation
  to `DrawIrBatch -> runtime queue -> drain -> dispatch/render`, regenerate the
  production report on a Vulkan/CUDA/OpenCL-capable host before treating stored
  Linux evidence as current production proof.
- BrowserBackend/WebRender currently carries explicit dispatch diagnostics. The
  first GPU frame uses a bounded widget-semantic Draw IR dispatch receipt with
  payload size/hash/text evidence, GUI AST source evidence, widget-id rect
  commands, text command-count evidence, command-level image URI evidence, and
  event-target context resolution evidence;
  cache hits still reset to `not_requested` with zero/empty dispatch payload
  fields. Do not wire full HTML -> Draw IR generation into the hot render path
  until it uses a prepared or cached Draw IR plan; the direct path can hang or
  exceed focused-test budgets.

## Files to inspect first

1. `doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md` (gate requirements)
2. `doc/04_architecture/ui/simple_gui_stack.md` (what is currently considered proven)
3. `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs` (exact fail conditions)
4. `src/lib/common/ui/web_render_api.spl` (`WebRenderArtifact` and queue/readback fields)
5. `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl` (runtime queue bridge builder)
6. `src/lib/gc_async_mut/gpu/engine2d/host_gpu_event_queue.spl` (queue submit/drain wrapper semantics)
7. `src/app/ui.browser/backend.spl` (`last_artifact_*` mapping and cache reset)
8. `test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl`
9. `test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl`
10. `test/01_unit/app/ui/browser_backend_runtime_queue_probe.spl`
11. `src/runtime/runtime_native.c` and `src/compiler_rust/runtime/src/host_gpu_lane.rs` (status/handle semantics)

## Tasks for Spark (small, ordered)

1. **Keep queue probe coverage stable and fail closed on missing backend proof.**
   - AC: `queue_emit_status`, queue overflow checks, and `same_frame_backend_readback_status` remain pass in gate script.

2. **Keep BrowserBackend frame-level artifact provenance concrete.**
   - AC: `browser_first_gpu_readback_source=device_readback` when a concrete backend submit/readback path is used.
   - AC: cache-hit case still sets queue/readback fields to `not_requested` and does not leak old data.

3. **Preserve the BrowserBackend readback metadata contract.**
   - AC: `last_artifact_queue_backend_handle` is positive on the first GPU frame when Engine2D reports a concrete backend readback handle.
   - AC: first-frame readback pixel count, checksum, and reason come from the typed `Engine2DReadback` receipt.
   - AC: focused unit specs and production gate conditions require positive BrowserBackend proof on the first frame; synthetic values such as Vulkan `7` remain isolated runtime queue roundtrip evidence.

4. **Preserve production gate assertions without synthetic handle proof.**
   - AC: script exits nonzero unless same-frame frame + queue + backend readback evidence are all present.
   - AC: current expected state is `production_runtime_queue_integration_status=pass` with
     `same-frame BrowserBackend queue and backend device readback receipt proven`.

5. **Prevent false-positive typed states.**
   - AC: backend_code=0 packets still drain to typed unavailable in both queue and browser bridge evidence.

6. **Keep HostGpuLane lifecycle evidence aligned with runtime queue state.**
   - AC: interpreted and native HostGpuLane specs still report begin/end,
     submitted/completed, `in_flight=0`, and typed unavailable when no active
     backend handle is registered.
   - AC: Rust HIR statement lowering continues to consume
     `rt_host_gpu_active_backend_handle()` for GPU queue packets.

7. **Keep platform gaps explicit instead of upgrading provenance to proof.**
   - AC: DirectX structured readback remains
     `structured-readback-contract-pass-native-pending` until a native Windows
     D3D11 staging readback command returns a same-frame `device_readback`
     receipt and positive backend handle/checksum.
   - AC: WebGPU real readback remains pass only when `webgpu_real` reports
     `source=device_readback`, a positive backend handle, and matching checksum;
     WebGPU `surface_upload` remains provenance-only.
   - AC: Metal and ROCm/HIP are recorded as typed unavailable unless the agent
     runs on the required host/runtime stack and captures the child wrapper
     report.

8. **Keep browser dispatch diagnostics honest.**
   - AC: first GPU frame reports `queue_dispatch_status=dispatched` from the
     widget-semantic Draw IR queue bridge.
   - AC: first GPU frame reports nonzero dispatch payload size/hash and payload
     text containing `simple-draw-ir-v2`.
   - AC: first GPU frame reports GUI AST source evidence plus widget-id rect
     and `draw_ir_text` command evidence for the panel/text/button fixture.
   - AC: first GPU frame reports one `draw_ir_image_command` with preserved
     `image_uri` for the image fixture, without claiming decoded image pixels.
   - AC: first GPU frame resolves `browser_queue_action:text` through
     `draw_ir_event_target_context` back to the queued GUI AST batch.
   - AC: cache-hit frames still report `queue_dispatch_status=not_requested`.
   - AC: no hot-path HTML -> Draw IR generation is added without bounded
     performance evidence.
   - AC: image URI Draw IR commands remain command-level evidence only until an
     asset resolver plus PNG/JPEG/WebP decode pipeline feeds Engine2D pixels.
   - AC: unsupported Draw IR render commands, including image URI commands
     before decode support, surface `unsupported Draw IR commands skipped` in
     `Engine2dDrawIrAdvResult.fallback_reason` and increment skipped count.

## Commands to run

- `sed -n '1,220p' doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md`
- `SIMPLE_BIN=bin/simple SIMPLE_LIB=src timeout 420 sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
- `SIMPLE_LIB=src timeout 180 ./bin/simple test test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src timeout 180 ./bin/simple test test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src timeout 180 ./bin/simple test test/01_unit/app/ui/browser_host_event_roundtrip_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src timeout 180 ./bin/simple run test/01_unit/app/ui/browser_backend_runtime_queue_probe.spl --mode=interpreter`
- `SIMPLE_LIB=src timeout 180 ./bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src timeout 180 ./bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src timeout 180 ./bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_readback_handle_contract_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src timeout 300 ./bin/simple test test/03_system/feature/language/host_gpu_lane_spec.spl --mode=interpreter --clean`

## Crash Isolation Rules

- Focused interpreter specs listed above may run locally with `timeout` when no
  previous `simple`/`cargo`/wrapper process is still alive.
- Full production wrappers, native rebuild/deploy, Vulkan strict probes, QEMU,
  ROCm/HIP, Metal, DirectX, and WebGPU hardware probes are dangerous tasks:
  run them in a disposable Docker/container workspace or a separate supervised
  process with `timeout`, captured logs, and a pre/post process check.
- If Docker lacks GPU/Metal/DirectX device access, record the backend as
  `host-unavailable` or `provenance-only`; do not promote container compile
  success to runtime queue/readback proof.
- After any crash or user-aborted run, kill only the specific stale wrapper/test
  children from that run, then recheck process state before starting another
  backend probe.

## Platform Spark + Normal-LLM Tasks

### macOS Metal

- Spark task: on Darwin, run
  `timeout 240 sh scripts/check/check-metal-generated-2d-readback.shs`, then run
  the production wrapper with a Metal-capable `bin/simple`.
- Evidence keys: `readback_metal_verdict=pass`,
  `metal_spark_task_status=pass`,
  `metal_normal_llm_verification_status=pass`.
- Fail closed: Linux `host-unavailable`, missing `xcrun metal`, missing
  `xcrun metallib`, or CPU mirror output is not a Metal production pass.
- Safe non-HW guidance: non-macOS agents may update planning docs only and must
  leave Metal typed unavailable.
- Normal-LLM verification: confirm the report is from Darwin/native Metal tools
  and the production report no longer records Metal as `host-unavailable`.

### ROCm/HIP

- Spark task: on an AMD ROCm host, run
  `HIP_ARCH=${HIP_ARCH:-gfx1100} timeout 240 sh scripts/check/check-rocm-generated-2d-readback.shs`,
  then run the production wrapper.
- Evidence keys: `readback_rocm_verdict=pass`,
  `rocm_spark_task_status=pass`,
  `rocm_normal_llm_verification_status=pass`.
- Fail closed: missing `hipcc`, ROCm loader libraries, device visibility, or
  verified HSACO keeps ROCm/HIP typed unavailable.
- Safe non-HW guidance: agents without ROCm hardware may document the lane only;
  compile-only and probe-only output must not become pass evidence.
- Normal-LLM verification: confirm the report proves real ROCm/HIP
  submit/readback on AMD ROCm hardware.

### DirectX/Windows

- Spark task: add or run DirectX native evidence only after a real D3D11
  staging readback command exists on Windows.
- Evidence keys before native real readback:
  `directx_spark_task_status=structured-readback-contract`,
  `directx_normal_llm_verification_status=structured-readback-contract-pass-native-pending`,
  `presentation_provenance_device_readback_status=not_device_readback`.
- Fail closed: the structured readback contract proves handle/checksum gating
  but must not satisfy production/native DirectX `device_readback`.
- Safe non-HW guidance: Linux-only agents may keep this as planning/provenance
  work and must not add production pass keys.
- Normal-LLM verification: reject promotion unless the report includes a
  positive DirectX backend handle and same-frame `device_readback` receipt.

### WebGPU/Browser

- Spark task: preserve WebGPU real device readback and keep upload/fallback
  provenance separate.
- Evidence keys for current real readback:
  `webgpu_spark_task_status=pass`,
  `webgpu_normal_llm_verification_status=pass`,
  `webgpu_real_readback_source=device_readback`,
  positive `webgpu_real_readback_backend_handle`, and matching checksum.
- Fail closed: `surface_upload`, adapter probe success, and CPU mirror pixels are
  not production `device_readback` proof.
- Safe non-HW guidance: browserless or adapterless agents may preserve guard
  state only and must not promote upload-handle evidence to queue/readback proof.
- Normal-LLM verification: reject regression if WebGPU real readback stops
  proving same-frame `device_readback` and falls back to CPU mirror or
  upload-only evidence.

## Remaining Parallel Tasks

- Backend-native queue Spark: extend this positive handle proof beyond Vulkan
  readback receipt into backend-specific session/command-buffer receipts where
  the backend exposes them.

## What **not** to touch

- Do not edit unrelated lanes: browser layout/reftest suites, compiler MIR lowering, generic MCP/LSP tooling,
  or unrelated 3D/compute evidence paths.
- Do not edit system tests outside queue/readback-lane artifacts listed above.
- Do not edit third-party/runtime external bindings under `src/runtime/vendor/**`.
- Do not rewrite `doc/06_spec`; this is an executable handoff/implementation task packet only.
