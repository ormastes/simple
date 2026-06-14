# GUI/Web Host-GPU Queue + Readback — Spark Handoff

Owner: normal-LLM/Spark lane
Date: 2026-06-14
Status: Production gate still fail-closed.

## Context

- This lane owns the final chain from 2D draw scheduling -> host/GPU queue emit/drain ->
  BrowserBackend frame evidence -> same-frame GPU readback receipt.
- Canonical source of truth: `sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`.
- Latest report (`doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-14.md`) is failing with
  `same-frame-gpu-command-buffer-readback-receipt-not-proven` because the queue bridge currently
  validates (`browser_frame_queue_status=fail`) before proving backend command-buffer provenance.

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

1. **Keep queue probe coverage stable, then split queue evidence from backend command-buffer proof.**
   - AC: `queue_emit_status`, queue overflow checks, and `same_frame_backend_readback_status` remain pass in gate script.

2. **Make BrowserBackend frame-level artifact carry concrete same-frame backend-provenance details.**
   - AC: `browser_first_readback_source` transitions to `device_readback` when a concrete backend submit/readback path is used.
   - AC: cache-hit case still sets queue/readback fields to `not_requested` and does not leak old data.

3. **Resolve the `browser_first_backend_handle` contract.**
   - AC: If `last_artifact_queue_backend_handle` is intended to represent real command-buffer handles, update
     focused unit specs and gate conditions consistently; if not, document that and keep it queue-local (`0`),
     but do not mix the meanings.
   - AC: WebRender BrowserBackend evidence must not synthesize backend handles from backend names. Hardcoded
     mappings such as Vulkan `7` are allowed only in isolated runtime queue roundtrip tests.

4. **Adjust production gate assertions only after proof is real.**
   - AC: script pass still fails closed unless same-frame frame + queue + backend readback evidence are all present.
   - AC: when proof is achieved, `production_runtime_queue_integration_status=pass` and reason no longer
     mentions `same-frame-gpu-command-buffer-readback-receipt-not-proven`.

5. **Prevent false-positive typed states.**
   - AC: backend_code=0 packets still drain to typed unavailable in both queue and browser bridge evidence.

## Commands to run

- `sed -n '1,220p' doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-14.md`
- `sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
- `./bin/simple test test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl --mode=interpreter`
- `./bin/simple test test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl --mode=interpreter`
- `./bin/simple run test/01_unit/app/ui/browser_backend_runtime_queue_probe.spl --mode=interpreter`
- `./bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl --mode=interpreter`

## What **not** to touch

- Do not edit unrelated lanes: browser layout/reftest suites, compiler MIR lowering, generic MCP/LSP tooling,
  or unrelated 3D/compute evidence paths.
- Do not edit system tests outside queue/readback-lane artifacts listed above.
- Do not edit third-party/runtime external bindings under `src/runtime/vendor/**`.
- Do not rewrite `doc/06_spec`; this is an executable handoff/implementation task packet only.
