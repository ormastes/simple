# GPU Scheduler Hardening and GPU-Resident Rendering Plan

## Merge sequence and state (2026-09-05)

| # | Step | State | Owning code | Evidence |
|---|---|---|---|---|
| 1 | Freeze receipt/provenance; defer normal DrawIR completion | done | `nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` | unit 9/9, system 4/4 |
| 0 | Common epoch contract (added; every later step composes it) | done | `common/gpu/engine2d/gpu_epoch.spl` | unit 9/9 |
| 2 | Packed registered payload ownership; SDN adapter is named compat only | done | `draw_ir_runtime_queue.spl` (`*_submit_packed/_complete_packed/_retire_packed`, `*_sdn_compat`), v3 store FNV-1a hash | unit 9/9 + 7/7, integration 2/2 |
| 3 | Fixed-arena Vulkan resident-2D slice + device evidence | done (pure); device-gated | `gc_async_mut/gpu/engine2d/vulkan_resident_2d.spl` | unit spec; system spec skips without `SIMPLE_GPU_TEST=1` |
| 4 | Capability-labelled Web/GUI event/style/layout/render islands | done | `common/ui/gpu_scene_islands.spl` | unit 6/6 |
| 5 | Provider conformance (Vulkan/Metal/DirectX) + optional autonomous submission | done; no provider grades `full` yet | `common/gpu/engine2d/gpu_provider_conformance.spl`, `gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | unit 7/7; device spec 1 ungated + 3 gated |

"done" means the contract, code and tests exist and the tests execute green.
It never means GPU execution is proven — see the non-admission rule below.
Every seam that cannot be verified on this host carries a `# TODO: [gpu][P2]`
comment and a row in `doc/08_tracking/todo/todo_db.sdn`.

## Acceptance map

| Requirement | Test evidence |
|---|---|
| REQ-GPU-SCHED-ASYNC-001 | submit leaves packet pending; compatibility dispatch still drains |
| REQ-GPU-SCHED-LIFE-001 | terminal-once, queue-full, stale/invalid completion outcomes; epoch phases forward-only |
| REQ-GPU-SCHED-PAYLOAD-001 | packed submit never serialises SDN; `*_sdn_compat` is the only SDN producer |
| REQ-GPU-SCHED-PAYLOAD-002 | v3 store hash is incremental FNV-1a, 16 hex digits, one-row change flips it |
| REQ-GPU-SCHED-PROFILE-001 | required profiles refuse with exact missing bits (epoch, islands, deferred queue) |
| REQ-GPU-SCHED-PROOF-001 | `device_execution_proven` flips only at `gpu_finished` with qualifying evidence |
| REQ-GPU-SCHED-EPOCH-001 | five separate generations, ring token/lease, four truth labels |
| REQ-GPU-SCHED-RESIDENT-001/002 | N identical frames: 0 semantic rebuilds, 0 readbacks; evidence qualification bar |
| REQ-GPU-SCHED-ISLAND-001 | declared subset admitted/refused/fallback per profile |
| REQ-GPU-SCHED-PROVIDER-001 | three probes graded unavailable/routing_only/full; `d3d11-dxvk`, never d3d12 |
| REQ-GPU-SCHED-AUTONOMY-001 | autonomy only for `device_initiated_experimental` on a `full` provider with DGC/ICB/work-graph bits |
| REQ-GPU-SCHED-VERIFY-001 | device specs skip green without `SIMPLE_GPU_TEST=1`; Vulkan lane ran on Apple M4 via MoltenVK |

## Verification when a device is present

```bash
SIMPLE_GPU_TEST=1 SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple run \
  test/03_system/app/ui.browser/feature/gpu_provider_conformance_device_spec.spl
SIMPLE_GPU_TEST=1 SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple run \
  test/03_system/app/ui.browser/feature/gpu_resident_vulkan_slice_spec.spl
```

Run ONE spec per invocation. On this Mac (2026-09-05) `bin/release/macos-arm64/simple test`
is an Apr-11 build that parses `it` blocks and counts them without executing
assertions; only the Sep-5 seed's `run` executes bodies. Every count above was
taken with the seed.

## Non-admission rule

Queue routing, a source scan, or an interpreter test does not prove GPU
execution. Production qualification needs exact binary/device identity,
timestamps, transfer/host-submit telemetry, retirement evidence, and negative
controls. Evidence qualifies only with DEVICE-side timestamps and real transfer
bytes; host-bracketed empty submits never do. No provider reports a fence token
or device timestamps yet, so every receipt in the tree is `routing_evidence_only`.
That is the honest state.

## Astra architecture review accepted

The existing host-GPU completion function is process-global compatibility
routing, not a queue-token/fence proof. `Engine2dGpuEpochRequest/Receipt` lives
in `common/gpu/engine2d/gpu_epoch.spl`, composes SimpleRing facts, and keeps
operation, queue, scene, surface and arena generations distinct. The DrawIR v3
packed generation store's text-growing hash was replaced (step 2) before reuse.
