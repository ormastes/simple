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
- `engine2d_host_gpu_lane_schedule`
- `engine2d_host_gpu_lane_summary`
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
`doc/06_spec/03_system/feature/language/host_gpu_lane_spec.md`
