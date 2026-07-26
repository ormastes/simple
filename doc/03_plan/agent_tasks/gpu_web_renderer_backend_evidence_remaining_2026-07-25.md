# GPU web renderer backend evidence remaining

## Goal

Deploy one source-matched full CLI, then collect honest CUDA, Vulkan, and Metal
execution evidence for the web/Engine2D path. Static or synthetic checks do not
count as hardware passes.

## Lanes

| Lane | Owner | Work | Done evidence |
|---|---|---|---|
| Bootstrap | Linux build agent | A full Stage4 rebuild is deferred by user instruction. Reuse the validated cached Stage3 only for bounded incremental native builds. | Full CLI artifact, CLI smoke, MCP smoke, max RSS, no stub fallback. |
| CUDA | NVIDIA Linux agent | Done on 2026-07-26 with the cached native portable emitter and `scripts/check/check-cuda-generated-2d-readback.shs`. | PASS on both NVIDIA devices: submit attempted, nonzero identities, readback available, stable PTX hash, and zero fill/copy/alpha/scroll mismatches. |
| Vulkan | NVIDIA Linux agent | Provide a no-stub runtime/closure containing Vulkan without retaining unrelated optional backend SFFI, then run `scripts/check/check-vulkan-engine2d-readback.shs`. | `backend_name=vulkan`, present/readback exercised, both readbacks report `device_readback` with positive handle/identity, zero mismatch, strict/parity JSON pass. |
| Metal | macOS agent | Rebase the source-matched changes, rebuild/redeploy the macOS full CLI, then run `GPU_2D_LIVE_BACKEND=metal sh scripts/check/check-macos-gpu-2d-live-evidence.shs`. | Native Metal device/queue/submit/readback evidence and matching pixels; Linux skip is not a pass. |

## Coordination

- Sidecar lanes: CUDA, Vulkan, and Metal may run in parallel only after the
  bootstrap artifact is deployed on their host.
- Merge owner: bootstrap lane owner.
- Final reviewer: highest-capability model, read-only, after all receipts exist.
- Stop after three failed build/test cycles per lane and update TODO 580 with
  the exact blocker instead of retrying.

## 2026-07-25 Linux Vulkan checkpoint

- The gate now defaults to native mode, honors `SIMPLE_EXECUTION_MODE`, and
  rejects CPU fallback, zero backend handles, and zero device identities.
- Native lowering defects in the retained-session helper and backend import
  were fixed.
- The third bounded native cycle reached linking and stopped at
  `unresolved external symbol 'rt_vulkan_discard_command'`; no hardware pass is
  claimed until that provider exists and a source-matched pure-Simple CLI runs
  the gate.

## 2026-07-26 incremental checkpoint

- CUDA live hardware evidence passes on the RTX A6000 and TITAN RTX with PTX
  hash `da1995dc1111d30674380dc166639ae7e34699635bfa000acbc3b2059b6f9575`.
- The cached Stage3 now compiles the 184-module Vulkan evidence closure after
  DirectX reused the existing `gc_async_mut.env.platform.is_windows` probe.
- A stub-enabled link succeeds, but is not accepted as evidence. The no-stub
  link has zero unresolved Vulkan symbols and fails on 70 unrelated optional
  OpenCL, OpenGL, oneAPI, Intel, and WebGPU runtime symbols retained by the
  monolithic Engine2D closure.
- The retained TODO 580 `v7` native-all archive exports every one of those
  families plus Vulkan. Relative, absolute, and direct-environment runtime-path
  attempts all remain forced onto `core-c-bootstrap` by the cached Stage3, so
  the archive is not admitted and no hardware run is claimed.
- An isolated Vulkan/CUDA `simple-runtime` provider plus the emitted
  184-module Simple archive links without stubs. Hardware initialization reaches
  `Initialized` with compute and graphics enabled on the NVIDIA ICD. The
  owner-module probe helper fixes the cached enum comparison and strict Vulkan
  creation passes. The next cached LLVM defect corrupts the cross-module
  `Engine2DReadback` aggregate (`pixels.len() == -1`) and segfaults the evidence
  serializer. Source now conditionally removes `TAG_HEAP` before LLVM aggregate
  field GEP, with x86_64/RV32 read/write IR regressions passing 2/2. A bounded
  source-matched compiler build and hardware rerun remain. See
  `doc/08_tracking/bug/native_engine2d_readback_aggregate_abi_2026-07-26.md`.
- Cached-native Metal source emission succeeds with four hash markers. Live
  Metal submit/readback remains blocked on a prepared macOS host; resume with
  `GPU_2D_LIVE_BACKEND=metal sh scripts/check/check-macos-gpu-2d-live-evidence.shs`.
