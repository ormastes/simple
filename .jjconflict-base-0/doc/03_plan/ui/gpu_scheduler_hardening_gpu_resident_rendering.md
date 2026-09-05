# GPU Scheduler Hardening and GPU-Resident Rendering Plan

## Merge sequence

1. Freeze receipt/provenance and defer normal DrawIR completion.
2. Add packed registered payload ownership; retain SDN adapter only as legacy.
3. Add fixed-arena Vulkan resident-2D vertical slice and device evidence.
4. Add capability-labelled Web/GUI event/style/layout islands.
5. Add Metal/D3D12 conformance providers and optional autonomous submission.

## Current increment acceptance map

| Requirement | Test evidence |
|---|---|
| REQ-GPU-SCHED-ASYNC-001 | submit leaves packet pending; compatibility dispatch still drains |
| REQ-GPU-SCHED-LIFE-001 | terminal-once, queue-full, stale/invalid completion outcomes |
| REQ-GPU-SCHED-PAYLOAD-001 | production API labels packed seam; text adapter is explicit compatibility |
| REQ-GPU-SCHED-PROFILE-001/PROOF-001 | strict profile/evidence contracts reject false device claims |

## Non-admission rule

Queue routing, a source scan, or an interpreter test does not prove GPU
execution. Production qualification needs exact binary/device identity,
timestamps, transfer/host-submit telemetry, retirement evidence, and negative
controls.

## Astra architecture review accepted

The existing host-GPU completion function is process-global compatibility
routing, not a queue-token/fence proof. `Engine2dGpuEpochRequest/Receipt`
belongs in common GPU Engine2D contracts and composes SimpleRing facts; it must
keep operation, queue, scene, surface and arena generations distinct. Reuse the
DrawIR v3 packed generation store only after its text-growing hash is removed
from the claimed hot path.

## Current execution evidence

On 2026-09-05, `SIMPLE_LIB=src bin/release/macos-arm64/simple test` passed the
focused no-GC queue suite (4 scenarios, 47 ms) and this system contract (3
scenarios, 40 ms). These are bounded routing/queue results only: they do not
admit native GPU execution, a fence/token, packed-payload residency, or
presentation.
