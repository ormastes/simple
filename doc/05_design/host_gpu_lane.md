# Host/GPU Lane Detail Design

Feature: `host_gpu_lane`

## Scope

This implementation slice adds the host/GPU lane contract used by GUI and
Engine2D offload work. It proves parser acceptance for the compact grammar and
implements lane validation helpers that future compiler lowering and runtime
queue transport must preserve.

## Public Contract

Canonical syntax:

```simple
target.later(options...) gpu \:
    ...

target.later(options...) host \:
    ...
```

`gpu` and `host` are lane markers. Existing `\:` and `\e:` lambdas stay intact.

## Engine2D Contract Surface

Implementation path:
`src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`

The contract exposes:

- `Engine2dHostGpuLaneResult`
- `Engine2dHostGpuEventFlowEvidence`
- `engine2d_host_gpu_lane_schedule`
- `engine2d_host_gpu_lane_summary`
- `engine2d_host_gpu_event_flow_evidence`
- `engine2d_host_gpu_event_flow_summary`
- host/gpu lane constants
- direct versus queue-packet execution constants

Inputs describe source lane, target lane, operation kind, packet estimate,
packet limit, semantic mutation flag, per-widget dispatch flag, strict backend
availability, and CPU baseline milliseconds.

## Validation Rules

- Invalid lanes fail.
- Packet estimate above `max_packet` fails.
- GPU semantic mutation fails.
- Per-widget GPU dispatch fails.
- GPU operations must be coarse batches.
- Host semantic commits are valid only on the host lane.
- Same-lane callbacks are direct; cross-lane callbacks are queue packets.

## Check Diagnostics

Implementation path:
`src/compiler_rust/driver/src/cli/check.rs`

The native Rust `simple check` path includes source-level diagnostics that
mirror the Engine2D lane contract:

- `HGL-SEMANTIC` is a hard error when a `target.later(...) gpu \:` block writes
  a host-owned semantic field such as `.checked`.
- `HGL-BATCH` is a warning when `target.later(...) gpu \:` appears as a
  per-widget loop dispatch instead of a frame-level render/effect batch.
- `HGL-MAX-PACKET` is a hard error when a `target.later(...) gpu \:` block omits
  explicit `max_packet`, because compiler lowering must produce bounded queue
  packets before runtime transport or device submission.

These diagnostics are covered by Rust driver unit tests. A local deployed
`bin/simple` may still require a binary refresh before it reflects the edited
driver source.

## Event-Flow Evidence

`Engine2dHostGpuEventFlowEvidence` records the deterministic boundary contract
that full GPU submissions must later satisfy:

- event count and Draw IR delta count are positive;
- packet bytes stay within `max_packet`;
- event order is preserved across the queue-packet boundary;
- fallback is explicit and does not claim speedup;
- strict GPU batches record lower event-to-present, frame p50, and frame p95
  estimates than the host baseline;
- pixel hash is carried as the correctness oracle field for measured runs.

The Draw IR executor spec also feeds real `engine2d_draw_ir_adv_composition`
results into this evidence record: rendered command count becomes
`draw_ir_delta_count`, bounded packet bytes are derived from rendered command
count, and the Engine2D pixel readback value is carried as the pixel-hash field.
This proves the event-flow evidence is connected to the runtime Draw IR executor
surface even when the current host uses CPU fallback.

`Engine2dHostGpuQueuePacket` is the deterministic descriptor future
`later(...)` lowering/runtime transport must emit. It records sequence,
source/target lanes, operation, execution kind, payload bytes, max packet bytes,
payload checksum, fallback state, and host-commit ownership. The descriptor does
not submit to a device; it makes the queue packet ABI testable before the
hardware backend lands.

`Engine2dHostGpuQueueTransportEvidence` validates deterministic queue drain
accounting over those descriptors. It records packet count, total payload bytes,
maximum packet bound, first/last sequence, order preservation, fallback count,
host-commit count, and aggregate checksum. This is the runtime-transport
contract above packet construction and below real hardware submission.

`Engine2dHostGpuQueueSubmissionEvidence` validates the final submission/readback
gate above queue drain. It rejects invalid transport, fallback packets, missing
strict GPU backends, and invalid timing before device submission; if submission
does happen, it requires the GPU readback pixel hash to match the expected
oracle before reporting success. This keeps fallback evidence from claiming
less-ms device execution.

The frontend parser now preserves `target.later(max_packet: N) gpu|host \:` as a
dedicated flat statement and bridges it into rich AST as
`StmtKind.TargetLater(TargetLaterConfig, Block)`. This is the first structural
compiler carrier for lane, packet bound, and body metadata; HIR and MIR
propagation still need to consume that rich AST node before codegen can emit
runtime queue packets directly.

HIR lowering now carries that node as `HirStmtKind.TargetLater`, and MIR lowering
emits explicit `MirInstKind.HostGpuLaneBegin` / `HostGpuLaneEnd` markers around
the lowered body with lane text, optional max-packet operand, and statement span.
These markers give later codegen/runtime transport a concrete boundary to turn
into queue packet emission.

`src/compiler/50.mir/host_gpu_lane_queue.spl` consumes those markers for the
Pure Simple evidence path. It scans `MirFunction` instruction streams, turns each
closed lane-marker region into an `Engine2dHostGpuQueuePacket`, validates ordered
transport, and runs the queue submission/readback evidence gate. The adapter uses
the explicit MIR `max_packet` operand when it is a constant integer and derives a
deterministic payload estimate from the lowered body instruction count. This
proves MIR markers can drive the same queue evidence ABI used by Engine2D tests.
The remaining gap is native hardware/backend codegen emitting and draining those
packets against a real device queue.

## Performance Model

For this slice, GPU batch performance is a deterministic evidence estimate:
when strict GPU backend evidence is available and the operation is batched,
estimated milliseconds are half the CPU baseline with a minimum of 1 ms.

Measured backend evidence is tracked separately in
`doc/09_report/perf/host_gpu_lane_event_flow_perf_evidence_2026-06-14.md`.

## System Test

Executable SSpec:
`test/03_system/feature/language/host_gpu_lane_spec.spl`

Generated manual:
`doc/06_spec/test/03_system/feature/language/host_gpu_lane_spec.md`
