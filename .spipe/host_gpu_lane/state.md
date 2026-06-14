# Feature: host_gpu_lane

## Raw Request
$sp_dev imple comlletely with pherallel agents and sync git hub every hours. make sspec system tests and event flow and others work properly andcperf is faster than before and less ms.

## Task Type
feature

## Refined Goal
Implement and verify the Simple host/GPU `later(...) gpu \:` lane contract so host semantic events stay host-owned, GPU work is batched through bounded packets, SSpec manuals document the flow, and performance evidence proves lower milliseconds when a strict GPU lane is available.

## Acceptance Criteria
- AC-1: Canonical `target.later(...) gpu \:` and `target.later(...) host \:` syntax is accepted by `bin/simple check`.
- AC-2: Host semantic mutation is accepted on the host lane and rejected on the GPU lane with a stable diagnostic.
- AC-3: GPU work is accepted only as coarse render/effect/resource batches with explicit packet bounds; loop-local per-widget GPU dispatch is diagnosed.
- AC-4: Event-flow evidence records event count, Draw IR delta count, packet bytes, fallback state, event-to-DrawIR time, submit/present time, frame p50/p95, pixel hash, and speedup versus baseline.
- AC-5: Unit and system SSpec tests cover syntax, semantic ownership, queue-packet event flow, fallback honesty, and faster strict-GPU estimated timing.
- AC-6: Generated `doc/06_spec` manuals are current and no executable `*_spec.spl` files exist under `doc/06_spec`.
- AC-7: Relevant design, guide, SPipe state, and perf evidence docs identify the canonical commands and remaining host-specific full-GPU evidence gaps.
- AC-8: Host/GPU lane commits are synced to GitHub without folding unrelated concurrent work into the lane.

## Scope Exclusions
- Full compiler lowering from lane marker AST into runtime queue transport remains a follow-up unless implemented and verified in this lane.
- Real Vulkan/Metal/WebGPU/CUDA device submission requires suitable host hardware/display support and must not be claimed from fallback-only evidence.

## Phase
implementing

## Log
- dev: Restored SPipe state file from current host/GPU lane artifacts and active goal.
- impl: Existing lane contract and Rust `simple check` diagnostics cover syntax, semantic ownership, and per-widget dispatch diagnostics.
- impl: Added `Engine2dHostGpuEventFlowEvidence` with event-count, Draw IR delta, packet, p50/p95, event-to-present, pixel-hash, fallback, and event-order evidence fields.
- spec: Extended unit and system SSpec coverage for strict-GPU event-flow speedup, fallback honesty, and event-order rejection.
- doc: Updated system-test plan, detail design, and performance evidence report with HGL-006 traceability.
- spec: Added Draw IR executor bridge coverage that feeds `engine2d_draw_ir_adv_composition` rendered-command counts and pixel readback into host/GPU event-flow evidence.
- perf: Recorded bounded GTK fallback, `wm_compare` software, and `simple_runner` smoke evidence in `doc/09_report/perf/host_gpu_lane_event_flow_perf_evidence_2026-06-14.md`; these prove harness/fallback honesty, not real GPU less-ms completion.
- doc: Refreshed SPipe and UI/WebGPU guide references for the canonical host GPU event-flow wrapper and remaining full-GPU evidence gap.
- impl: Added `Engine2dHostGpuQueuePacket` as the deterministic queue-packet descriptor future `later(...)` lowering/runtime transport must emit.
- spec: Extended backend lane SSpec coverage to 18 tests for cross-lane packet sequence, payload checksum, fallback state, and invalid sequence rejection; regenerated `doc/06_spec/test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_lane_spec.md`.
- impl: Added `Engine2dHostGpuQueueTransportEvidence` to validate deterministic runtime queue drain accounting over lowered packet descriptors.
- spec: Extended backend lane SSpec coverage to 20 tests for ordered transport payload/fallback/checksum accounting and out-of-sequence rejection; regenerated `doc/06_spec/test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_lane_spec.md`.
- impl: Added native Rust `simple check` diagnostic `HGL-MAX-PACKET` so GPU `later()` source must declare `max_packet` before compiler lowering can emit bounded host/GPU queue packets.
- spec: Added Rust driver unit coverage `test_check_requires_max_packet_for_gpu_later_lane`; kept system SSpec positive canonical grammar on explicit `max_packet` because deployed `bin/simple` may lag the edited Rust driver source.
