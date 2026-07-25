# Real Host/GPU Runtime Queue Emission Plan

Date: 2026-06-14
Status: Partial implementation; runtime queue externs, interpreter/native
GPU-lane queue evidence, Engine2D runtime-submit/drain evidence, a Draw IR
runtime queue bridge, WebRender queue metadata, and focused BrowserBackend
render-frame queue diagnostics are in place. Real backend submit/readback
receipts remain pending. The production GUI/web path is fail-closed until it
proves one ordered adapter -> runtime queue -> backend submit ->
drain/readback run.

## Scope

Implement the missing real runtime path from `target.later(...) gpu|host` and
Engine2D Draw IR batches into host/GPU queue packets, drain records, and backend
submit evidence. This plan does not cover synthetic evidence adapters except as
compatibility fixtures that must be replaced or cross-checked by runtime data.

## Already Proven

- `src/compiler_rust/runtime/src/host_gpu_lane.rs` has lane marker counters and
  a runtime queue facade: `host_gpu_queue_reset`,
  `host_gpu_queue_emit`, `host_gpu_queue_drain`,
  `host_gpu_queue_packet_count`, `host_gpu_queue_submitted_count`,
  `host_gpu_queue_completed_count`, and
  `host_gpu_queue_last_status`.
- `runtime_symbols.rs`, `runtime_sffi.rs`, `elf_utils.rs`, and
  `interpreter_extern/host_gpu_lane.rs` expose the counter and queue symbols to
  native and interpreter paths. `src/runtime/runtime_native.c` mirrors the queue
  externs for native C-runtime linked specs.
- `src/compiler_rust/compiler/src/interpreter_call/builtins.rs` emits a runtime
  queue packet for canonical interpreted `target.later(...) gpu` lane syntax.
  `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` lowers
  statement-position `target.later(...) gpu|host \:` markers to runtime
  begin/body/end calls, with GPU queue emit only. `test/03_system/feature/language/host_gpu_lane_spec.spl`
  covers begin/end counters, queued-packet status, and typed unavailable drain
  status for interpreted and forced-native `target.later(...) gpu` fixtures.
- `test/03_system/feature/language/host_gpu_event_path_spec.spl` and Pure
  Simple Engine2D helpers prove adapter-level queue submit/receipt summaries
  plus runtime queue emission through `engine2d_host_gpu_event_submit_to_runtime`:
  `engine2d_host_gpu_event`, `engine2d_host_gpu_event_handler_decision`,
  `engine2d_host_gpu_event_submit`, `engine2d_host_gpu_event_receipt`,
  `engine2d_host_gpu_runtime_queue`, `engine2d_host_gpu_event_submit_to_runtime`,
  `engine2d_host_gpu_runtime_drain`, `engine2d_host_gpu_draw_ir_event_flow`, and
  their summary helpers.
- `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` exposes
  `engine2d_draw_ir_adv_batch_runtime_queue`, which converts a GPU-selected
  `DrawIrBatch` into one host/GPU runtime queue packet, renders through the
  existing Engine2D path, and drains a runtime receipt. Coverage:
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`.
- `src/lib/common/ui/web_render_api.spl` now carries queue metadata on
  `WebRenderArtifact`: submit status, drain status, packet id, drained count,
  and diagnostic reason. `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
  attaches runtime queue evidence for GPU-selected web-render artifacts, and
  `src/app/ui.browser/backend.spl` mirrors those values as
  `last_artifact_queue_*` frame diagnostics. Focused coverage:
  `test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl`
  and `test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl`.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`
  routes Simple-generated widget HTML through the deterministic widget raster
  path before expensive CSS scans. This unblocks `BrowserBackend.render_frame`
  for generated widget frames while keeping generic non-widget HTML on the full
  layout renderer.
- Rust and C runtime queue capacity now match at 1024 pending packets. Rust
  runtime coverage rejects the overflow packet and accepts a new packet after a
  full drain.
- Interpreter lane `END` accounting is exception-safe for body errors. Coverage:
  `src/compiler_rust/compiler/tests/host_gpu_lane_error_test.rs`.
- Backend readback evidence exists for generated 2D paths where available, for
  example `doc/03_plan/sys_test/gpu_backend_readback_evidence_2026-06-14.md`.
  The concrete generated/native reports are
  `doc/09_report/vulkan_engine2d_readback_2026-06-14.md` (pass),
  `doc/09_report/cuda_generated_2d_readback_2026-06-14.md` (pass),
  `doc/09_report/metal_generated_2d_readback_2026-06-14.md` (typed
  unavailable on Linux), and
  `doc/09_report/rocm_generated_2d_readback_2026-06-14.md` (typed unavailable
  on Linux).

## Not Proven Yet

- No backend submit call is driven from the host/GPU lane queue.
- Browser-frame queue diagnostics are proven for a GPU-selected
  `BrowserBackend.render_frame` run, including cache-hit reset to
  `not_requested`. The frame now carries the runtime backend-handle value from
  the packet drain, but it is still not same-frame backend readback proof.
- Interpreter and statement-lowered native GPU queue packets currently emit
  `backend_code=0` and drain as `UNAVAILABLE`; they do not yet carry a real
  backend handle.
- The runtime now exposes `host_gpu_queue_last_backend_handle()` through the
  Rust/C/interpreter/SFFI symbol path and can round-trip a synthetic submitted
  packet handle. Production still requires GUI/web backend code to supply a real
  Vulkan/CUDA/WebGPU/Metal/ROCm submit/readback handle.
- The runtime now exposes a two-phase submit/complete path, so `SUBMITTED` is
  observable before terminal `COMPLETED` or `UNAVAILABLE` status. Coverage:
  `test/03_system/feature/language/host_gpu_event_path_spec.spl`.
- Runtime packets currently carry numeric metadata only; full Draw IR payload
  serialization still needs to flow through `draw_ir_to_sdn` or an equivalent
  runtime payload buffer.
- Runtime packets can carry a backend-handle value and BrowserBackend mirrors
  it, but a queue drain still cannot prove Vulkan/CUDA/WebGPU/Metal/ROCm
  submission for a GUI/web frame until backend readback is tied to that same
  frame receipt.
- Dedicated HostGpuLaneBegin/End MIR instructions do not exist in the current
  compiler. The current syntax parses as ordinary calls/trailing lambdas;
  statement lowering handles the marker form, but expression-position forms
  remain ordinary calls and a Rust MIR unit test should still lock the exact
  lowering shape.

## Implementation Tasks

1. Done: Add queue data structures and APIs in
   `src/compiler_rust/runtime/src/host_gpu_lane.rs`:
   `HostGpuQueuePacket`, `HostGpuQueueReceipt`, `HostGpuQueueDrain`,
   `host_gpu_queue_reset`, `host_gpu_queue_emit`,
   `host_gpu_queue_drain`, `host_gpu_queue_packet_count`,
   `host_gpu_queue_submitted_count`, `host_gpu_queue_completed_count`,
   and `host_gpu_queue_last_status`.
2. Keep existing counter APIs stable. `host_gpu_lane_event` should still
   record begin/end counters, then optionally associate the active lane scope
   with queue emission metadata.
3. Done: Wire every new extern through
   `src/compiler_rust/common/src/runtime_symbols.rs`,
   `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`,
   `src/compiler_rust/compiler/src/elf_utils.rs`, and
   `src/compiler_rust/compiler/src/interpreter_extern/host_gpu_lane.rs`.
4. Add a Rust MIR regression test for statement-position
   `target.later(...) gpu|host` queue emission. System evidence exists, but the
   compiler-owned unit test should assert begin, optional queue emit, body, and
   end ordering.
5. For `gpu`, emit a coarse queue packet around render/effect work. For `host`,
   preserve host execution and record a host-lane packet only when evidence mode
   requests it.
6. Partly done: Connect Engine2D Draw IR by extending
   `src/lib/gc_async_mut/gpu/engine2d/host_gpu_event_queue.spl` and
   `src/lib/gc_async_mut/gpu/engine2d/host_gpu_draw_ir_event_flow.spl` so the
   existing helper summaries can report runtime packet id, backend kind, submit
   result, drain status, and fallback reason. `draw_ir_adv.spl` now provides a
   `DrawIrBatch -> runtime queue -> render -> drain` bridge; full Draw IR
   payload serialization is still pending.
7. Backend submit should first target the existing runtime backend surfaces that
   already have typed availability/readback evidence. Unavailable GPU hardware
   must produce a typed unavailable drain result, not a silent host pass.
8. Done: Define matching queue capacity semantics across Rust and C at 1024
   pending packets. Rust runtime coverage now rejects overflow and accepts a new
   packet after drain. Follow-up: add a typed overflow/backpressure status if
   callers need to distinguish capacity rejection from invalid arguments.
9. Done: Make lane scope accounting exception-safe so a body error still records
   lane end/failure evidence and does not leave counters stale.
10. Done: Preserve observable `SUBMITTED` state when backend work is in flight,
   then transition through explicit completion to `COMPLETED` or
   `UNAVAILABLE`. Follow-up: add backend-specific `submit_failed` and
   `readback_mismatch` terminal statuses when real backend handles are plumbed.
11. Add real-backend-handle plumbing so packets no longer drain as
   `UNAVAILABLE` solely because `backend_code=0`.
12. Partly done: Add the browser-frame bridge. `WebRenderArtifact` and
   `BrowserBackend` now expose queue status fields, the pixel artifact backend
   can attach host/GPU runtime queue evidence for GPU-selected render artifacts,
   queue identity is separated from backend-handle identity, and generated
   widget frames complete reliably through the shared pixel artifact path with
   focused queue diagnostic coverage. Remaining work: fuse the BrowserBackend
   frame receipt with same-frame backend submit/sync/readback metadata and fall
   back to the existing Engine2D pixel artifact path with a typed reason when
   unavailable.
13. Keep reports and docs layer-specific. Adapter summaries, runtime queue
   counters, and backend readback fixtures are useful evidence, but only a
   single ordered GUI/web run through adapter -> runtime queue -> backend drain
   -> readback should be labeled production GUI/web GPU rendering.

## Test And Evidence Plan

- Done: Extend `test/03_system/feature/language/host_gpu_event_path_spec.spl`
  with runtime-backed cases.
- Done: Add focused native/interpreter checks that call
  `host_gpu_queue_reset`, emit one GPU Draw IR packet, drain it, and assert
  packet count, submitted count, completed or unavailable status, and stable
  ordering.
- Add a regression case proving stale target-cache or unresolved Draw IR stays
  on the host and does not increment GPU submitted count.
- Add typed overflow/backpressure status only if callers need to distinguish
  capacity rejection from invalid arguments.
- Add real-backend-handle tests proving a packet can leave `backend_code=0` and
  drain to a backend-specific terminal status.
- Add a GUI/web queue-drain regression once the bridge exists: one frame should
  produce a runtime packet, one drain receipt, backend status, readback checksum
  or typed unavailable reason, and an explicit CPU fallback receipt when needed.
- Add backend evidence scripts only after the runtime path exists; reports
  should distinguish `pass`, `typed_unavailable`, `submit_failed`, and
  `readback_mismatch`.
- Keep `doc/06_spec` free of executable specs; generated manuals mirror the
  executable tests only as Markdown.

## Exit Criteria

- Native and interpreter paths expose the same queue symbols.
- `target.later(...) gpu` can produce at least one real queue packet and drain
  receipt from Engine2D Draw IR.
- Backend submit is attempted only when capability checks pass; otherwise the
  drain result is typed unavailable.
- GUI/web documentation and evidence distinguish adapter-only, runtime-only,
  backend-only, and full queue-drain integration claims.
- Existing counter-only specs continue to pass.
- New evidence proves real runtime queue/drain data, not only Pure Simple
  adapter summaries.
